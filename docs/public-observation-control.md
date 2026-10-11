# Original-SMT Control Of Public Observation Effects

## Purpose

Recovery's `baseline_domain` is structural UCP reasoning without concrete public
values. The final recovery may also use stronger SMT reasoning. Thus
`domain_refined_from_baseline = true` does not by itself show that a publication
caused the domain refinement: SMT may simply discover an intrinsic constant that
UCP missed.

The optional `analyze_public_observation_effect` API independently tests whether
a reported Exact or finite covering domain needs the concrete public
observations. It compares the same original SMT encoding with and without those
equalities. No UCP baseline is used as the semantic reference.

## Checked Property

Let C be the original encoded circuit, P the supplied concrete instance
equalities, s the selected private cell, and D its reported covering domain.

First establish:

```text
SAT(C AND P)
```

Then check each domain:

```text
UNSAT(C AND P AND s NOT IN D)   -- independently verify observed coverage
SAT/UNSAT(C AND s NOT IN D)    -- release concrete instance equalities only
```

| Cell Effect | Meaning |
| --- | --- |
| `ObservationDependent` | Coverage holds under P, but a full original witness without P places s outside D. The concrete observations strictly narrow the feasible marginal projection. |
| `AlreadyImplied` | C alone already implies this particular covering claim. A UCP-to-SMT improvement must not automatically be attributed to P. |
| `Refuted` | A full original witness under P violates the reported domain. No observation-effect classification is accepted for it. |
| `Unresolved` | Budget or solver uncertainty prevented the required checks. |
| `NoDomainClaim` | Recovery reported no covering domain. Partial discovery samples are not tested as a domain. |
| `Inconsistent` | Original C AND P is unsatisfiable; no vacuous exclusion claim is accepted. |

Original observed SAT also proves C is satisfiable, so a separate unobserved base
SAT check is unnecessary. The unobserved SAT counterexample has a valid original
witness, but may require different public values. It is **not a second recovered
secret under the actual observations**.

`AlreadyImplied` is deliberately not a no-leakage verdict. If D is `{0,...,15}`,
C can already imply D even when P reduces the actual projection to `{15}`.
The control tests the supplied covering claim, not every narrower one. For
Exact `{v}`, original satisfiability and unobserved exclusion show that C already
fixes s=v; this can itself be an unwanted exposure in the public circuit.

No projection cardinalities, entropy, joint witness counts, or cryptographic
security scores are computed. The complete observation set is released together;
the API does not yet identify a minimal subset of publications responsible for
the effect, or quantify how much each publication contributes.

## Original Context Isolation

The existing privacy preparation validates the selected cells, complete concrete
public interface, and supported inline fixed lookup tables. A fresh analyzer
encodes gates, copy constraints, and correlated lookup tuples. Before any public
equalities or learned assertions are written, the control snapshots C. It then
adds the concrete observations and snapshots C AND P from that same encoding.

Nothing is removed by parsing/filtering SMT strings. Public variables remain
symbolic in C; gates, selectors, fixed constants, layout, copy bindings, and lookup
tables remain unchanged. A private cell copied to an instance can vary with that
instance in C. A private cell copied to a fixed constant cannot vary and is
intrinsic. Already written observations or legacy search restrictions cannot be
released merely by clearing the input map; a monotonic guard rejects that capture.

Every exclusion uses an immutable full original snapshot plus only that cell's
blocked domain values. Targeted subsets, other recovered values, K/Delta facts,
and actual assigned advice values are not premises. Query files are recreated
per check, so assumptions do not accumulate. Captured contexts remain independent
of subsequent strengthening of the ordinary analyzer.

Both comparisons concern the **same synthesized layout and fixed data**. They do
not resynthesize the program for every hypothetical public input or discard
information already baked into the public circuit itself. Results depend on
faithful frontend encoding and trusted solver results, not a machine-checked
proof of the implementation or protocol zero knowledge. As with fresh validation,
the caller supplies the circuit being checked; recovery reports have no circuit
fingerprint that can authenticate their original source.

## Usage And Costs

```rust
use korrekt::circuit_analyzer::ucp::privacy_observation::{
    analyze_public_observation_effect, PublicObservationEffectOptions,
};

let effect = analyze_public_observation_effect::<Fr, _>(
    &circuit,
    k,
    &analyzer_input,
    &recovery_report,
    PublicObservationEffectOptions {
        max_solver_checks: 64,
        ..Default::default()
    },
)?;
println!("{effect}");
```

This is a separate opt-in pass. It does not mutate the recovery report, K, Delta,
or the existing coarse-baseline metric, and adds no cost to ordinary recovery.
Default allowance is 256 actual solver invocations. The same hard total includes
one mandatory full-original SAT check and up to two full-model exclusions per
reported domain. No hidden SAT-hint retry or subset fallback is used. A refuted
observed claim skips its unobserved check; cells without domains skip both.

`solver_timeout_ms: None` inherits the recovery report's effective solver budget,
then the legacy environment fallback. An explicit nonzero value overrides it
locally; zero is rejected. The supervised timeout applies per process, not to
synthesis, UCP, or total analysis time. `max_solver_checks = 0` yields a query-limited
report with no solver calls; frontend validation/encoding can still take place.

The report separates `satisfiability_checks`, `observed_domain_checks`, and
`unobserved_domain_checks`; their sum equals `solver_checks`. Each cell records
`observed_domain_verified`, counterexamples, and structured limitations. An
observed claim may be verified while its unobserved control remains unresolved.
Typed unknown/timeout consumes its check and permits later cells to proceed while
budget remains. Malformed output or execution failures remain errors. Claims
with unsupported values or more than 256 finite entries are rejected; field
equivalent representatives are normalized before blocking and comparison.

Global `Refuted` takes priority when any claimed domain is wrong, even if other
cells are incomplete. Otherwise limits/unknown keep the report incomplete; an
analyzed report can contain `NoDomainClaim` cells that are not certified. Always
inspect individual cell evidence, not only the global status.

The original SMT-only comparison does not run this optional pass. The separate
[recovery profile measurements](private-recovery-profile-measurements.md) now
measure its additional time and checks alongside each recovery configuration.
The demo's timings remain single debug observations, not general recovery-rate
or speedup estimates.

## Demo And Regressions

```text
Intrinsic:
s*s - 2*s + 1 = 0
next = s + 2
An unrelated public value is supplied.

Publication-dependent:
public first = 100, second = 142
first = secret + mask
second = 2*secret + mask
```

SMT recovers intrinsic s=1 even though UCP's baseline has no domain. The control
labels it `AlreadyImplied`. The two publications jointly recover secret=42 and
mask=58, while original satisfying alternatives exist without the concrete
observations; the control labels both claims `ObservationDependent`.

```sh
cargo test --offline -p korrekt demo_public_observation_control -- --nocapture --test-threads=1
cargo test --offline -p korrekt privacy_observation -- --test-threads=1
```

Regressions cover original-SMT versus UCP precision, exact and finite-domain
claims, range gates and real imported lookup gadgets, copied instances/fixed
constants, reused-mask composition, false claims, empty/oversized sets, field
equivalence, no-domain partial discovery, every budget boundary, typed unknown,
fatal errors, original inconsistency, changed public inputs, duplicate targets,
scope isolation, and ignored actual advice assignments. Tests must run serially
because SMT output paths are currently shared.

## Verification Snapshot

Default Zcash/Pasta backend, offline debug build, serial execution:

- Focused observation control: 26 tests passed (9 classification-driver tests and
  17 actual Halo2/SMT regressions).
- New observation-control demo: 1 test passed.
- Full `korrekt` suite: 361 passed, 0 failed, 2 ignored, 55.35 seconds.
- `cargo check --offline -p korrekt --all-targets`, touched-file rustfmt checks,
  and `git diff --check` passed. Existing unrelated compiler warnings remain.

The two ignored tests are the explicit resource-bounded Poseidon inversion run
and the repeated measurement suite. Neither was run for this snapshot. Other
Halo2 backend feature combinations were not checked in this step. These results
are regression evidence, not a formal soundness proof or a universal recovery
rate measurement.
