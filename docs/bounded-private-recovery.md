# Bounded Private Recovery

## Resource Policy

`PrivacyAnalysisOptions` configures the hard total query limit and solver budget:

```rust
let options = PrivacyAnalysisOptions {
    max_semantic_queries: 256,
    solver_timeout_ms: Some(2_000),
    ..Default::default()
};
let report = analyze_private_recoverability::<Fr, _, _>(
    &circuit, k, &analyzer_input, private_cells, options,
)?;
println!("{report}");
```

The time setting applies to each CVC5 check and its containing solver process,
including the initial SAT check and the checks inside each semantic cell query.
The privacy API now also has a nested `search` policy for reserved target attempts,
progress-sensitive optional work, and bounded retries. See
[adaptive recovery](adaptive-private-recovery.md) for defaults and retry deadlines.
Zero is rejected. `None`
inherits `HALO2_ANALYZER_SMT_TIMEOUT_MS`; when neither is supplied, solver time
remains unlimited for backward compatibility. Explicit options take precedence
and are instance-local: no environment variable is modified.

CVC5's [documented `tlimit-per` policy](https://cvc5.github.io/docs/latest/options.html)
is solver-managed. In addition, the analyzer supervises each CVC5 process with
the same monotonic wall-clock budget, kills and reaps it on expiry, and discards
all partial output. Scheduling and shutdown overhead can exceed the budget
slightly. This is not a bound on synthesis, UCP, or the whole analysis. One
semantic query can perform two solver invocations, each with its own budget.
The initial SAT stage does not consume the semantic-query quota and always runs,
even when `max_semantic_queries` is zero. It can first try scoped, public-only UCP
exact-value hints: only SAT is accepted; rejected or unknown hints trigger an
original, unstrengthened check. Thus this stage uses one or two solver processes,
each with its own budget. The report counts actual initial SAT attempts. See
[positive-only SAT acceleration](sat-hint-acceleration.md). The report stores the effective options
and elapsed time; these make resource-relative observations reproducible, not
hardware-independent complexity claims.

Before process supervision was added, a manual 16-bit probe with a 1 ms policy
had to be interrupted after substantially overrunning that policy. That historical
run is not a successful analysis or a confirmed solver timeout. The new supervisor
addresses solver-process overruns; a hard end-to-end deadline would still require
separate UCP/synthesis cancellation. Supervision covers the direct CVC5 child,
not arbitrary trees of subprocesses.

## Cell Results

The existing `uniqueness` and `domain` fields are retained. The derived
`cell.recovery_status()` avoids a second stored label becoming stale:

| Status | Meaning |
| --- | --- |
| `Recovered` | An exact supported value was inferred or proved. Optional fresh SMT validation is a separate step. |
| `UniqueWithoutValue` | Uniqueness is established, but there is no reported concrete value. |
| `NonUnique` | SMT found alternative satisfying values under the same public observations. A finite candidate superset may still be known. |
| `Unresolved` | No uniqueness conclusion was obtained. |
| `UnsupportedValueRepresentation` | Uniqueness is established, but the concrete value exceeds the supported BigInt representation limit. |

`recovery_limitation` records the reason separately: `QueryLimit`, `SolverTimeout`,
`SolverUnknown { reason }`, `ValueRepresentationLimit`, `NoConcreteValue`, or
`InconsistentContext`. A structurally unique cell whose value query was skipped
is `UniqueWithoutValue` with `QueryLimit`, not automatically a representation
failure. A large value does not imply inversion hardness.

Unsuccessful domain inference alone cannot identify which internal precision cap
was responsible. No unsupported-value classification is guessed merely because
UCP returned no domain. Stored integer magnitudes are bounded by 4096 bits;
finite domains remain capped at 256 values, and linear-system limits remain in
place. Supported Halo2 field values fit the bit limit. Public observations also
use BigInt with a 4096-bit raw-input bound, checked before normalization. See
[full-width recovery](full-field-recovery.md) for the input API and migration.

## Unknown, Errors, And Unsupported Frontends

CVC5 incomplete diagnostics are preserved by the parser. An explicit
`TIMEOUT` diagnostic or supervisor-generated `WALLCLOCK_TIMEOUT` produces
`SolverTimeout`; merely configuring a time limit
does not turn every `unknown` into a timeout. Other diagnostics, including
`RESOURCEOUT`, remain structured `SolverUnknown` reasons. No model from an
`unknown` response is used as a recovered value.

An unknown original initial SAT check after any hint fallback returns `PrivacyAnalysisStatus::SolverUnknown` with
no UCP result or recovered domains, preventing claims without a known satisfiable
context. After initial SAT succeeds, unknown cell queries consume their query
quota, preserve previous sound facts, and allow other queries to proceed. Target
queries may be retried after new information or a larger solver budget, subject
to per-target and total limits. Remaining target unknowns keep the run incomplete;
a successful retry clears the earlier unknown. Unknown bridge queries do not
invalidate fully resolved targets.

Unsupported lookup modes/table forms return a typed `UnsupportedPrivacyFeature`
error, not a privacy report. Invalid cell selections, missing public observations,
malformed solver output, encoding failures, and execution errors remain errors;
they are not reclassified as protected secrets or ordinary solver unknowns.

## Independent Validation And Measurements

Optional [finite-domain refinement](finite-domain-refinement.md) has its own hard
solver-check cap, disabled by default. These checks are reported separately from
ordinary semantic cell queries and feed smaller covering domains back into UCP.
Partial candidate checking does not certify a complete feasible projection.

Optional [SMT domain discovery](smt-domain-discovery.md) separately bounds checks
and retained values for cells without an inferred domain. Only original-model
exhaustion exports a complete set; partial feasible samples are not covering sets.
Its hard total allowance never resets when UCP makes progress.
Fair discovery rounds preserve per-cell samples. Optional larger-timeout retries
use the same hard total; they do not inherit the ordinary uniqueness retry floor.

Fresh domain validation uses the recovery report's effective per-check time
policy. It assumes no inferred K/Delta facts for exclusion. Existential SAT hints
are popped first; a literal original-constraint subset can prove exclusion by
UNSAT. Subset SAT/unknown falls back to a full original exclusion query. Final
unknown/errors remain errors, never `VerifiedDomains`; validation does not certify recovery
status labels, entropy, or cryptographic privacy.

The measurement harness excludes structured incomplete recovery reports just as
it excludes SMT-only unknown errors. Correctness mismatches remain fatal. Raw
incomplete-case reasons retain timeout diagnostics; incomplete cases never receive
fabricated recovery times or speedup ratios.

## Regression Checks

```sh
cargo test --offline -p korrekt --lib privacy::tests -- --test-threads=1
cargo test --offline -p korrekt --lib smt_parser::tests -- --test-threads=1
cargo test --offline -p korrekt --lib smt_solver::process::tests -- --test-threads=1
cargo test --offline -p korrekt --lib privacy_measurement_smoke_reports_explicit_api_budget -- --nocapture --test-threads=1
```

Tests cover every result category, explicit budget isolation and validation use,
zero-budget rejection, missing-value reasons, initial uncertainty, partial results,
timeout-vs-other-unknown diagnostics, and malformed output. Unknown driver tests
inject deterministic responses through the same private state machine used by
production, rather than depending on machine-specific timeout timing.

## Historical Verification Snapshot

Before process supervision and full-width recovery, the default-feature serial
library suite passed 178 tests with no failures; the
one opt-in measurement test was run separately. Three release repetitions
completed twelve measurement cases. The existing 16- and 32-bit cases returned
explicit `TIMEOUT` diagnostics during the SMT-only initial SAT check and were
excluded, with their reasons preserved in
`/tmp/bounded-private-recovery-measurements.incomplete.tsv`.
Raw and summary data are in `/tmp/bounded-private-recovery-measurements.tsv` and
`/tmp/bounded-private-recovery-measurements.summary.tsv` on this workspace.

These results describe recovery by this implementation in a supplied public
context and resource policy. Non-uniqueness, unknown, timeouts, and unsupported
features do not establish cryptographic privacy or universal resistance to recovery.
