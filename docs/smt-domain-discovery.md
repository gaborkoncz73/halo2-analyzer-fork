# Bounded SMT Domain Discovery Without UCP Candidates

## Purpose

An ordinary uniqueness query can recover one exact value or prove that at least
two values are possible. Existing finite-domain refinement checks an already
inferred small UCP superset. Neither operation discovers a complete multi-value
projection when UCP has no candidate domain.

Optional domain discovery now searches the original constraints and concrete
public observations directly. It enumerates distinct values of a selected private
cell, without an initial UCP candidate set. Only a final UNSAT answer certifying
exhaustion permits exporting a finite domain into Delta. UCP then runs again and
may recover other cells from that information.

This extends the abstract's analysis of narrowed private possibilities beyond
syntactically inferred ranges. It does not guarantee complete or fast inversion
of arbitrary circuits.

## Configuration

```rust
use korrekt::circuit_analyzer::ucp::{
    privacy::PrivacyAnalysisOptions,
    privacy_discovery::PrivacyDomainDiscoveryOptions,
};

let options = PrivacyAnalysisOptions {
    solver_timeout_ms: Some(2_000),
    domain_discovery: PrivacyDomainDiscoveryOptions {
        max_solver_checks: 64,
        max_values_per_cell: 16,
        max_checks_per_round: 1,
        ..Default::default()
    },
    ..Default::default()
};
```

Pass these options to `analyze_private_recoverability`. Discovery is disabled by
default (`max_solver_checks = 0`), so existing default analyses do not pay for
enumeration. Full option literals require the scheduling fields or `..Default::default()`.

Only explicitly selected private cells without any current Delta domain are
enumerated. Existing finite sets use the separate, optional
[finite-domain refiner](finite-domain-refinement.md); exact values need no search.
Both options can be enabled together. A completely discovered set is not
redundantly checked by the refiner, preserving its budget for other cells.

An enabled retained-value limit must be between 1 and 256. The hard total check
budget is separate from ordinary semantic queries, finite-domain refinement,
initial satisfiability checks, and optional independent validation. It never
resets after progress. Search state is retained per cell, including every observed
value and each solver invocation. The default scheduler uses one check per cell
per round; it can continue a partial enumeration in later rounds without starting
over. A total allowance smaller than the target count can still leave cells
unattempted.

Invocations initially use the ordinary supervised solver timeout. The uniqueness
retry floor is not inherited. There is no global wall-clock deadline for
synthesis, UCP, or the entire analysis. Full-width field values use the existing
BigInt/signed representation, with a 4096-bit representation limit.

## Scheduling And Continuation

The scheduler selects only cells in the earliest unfinished check round. Within
that pool, a cell already proved unique but missing its value has priority.
Otherwise it uses the existing `choose_query_cell` UCP simulation, including
expected target/cell propagation and expression connectivity. Equal scores use
a stable CellId tie-break. This is a heuristic, not a cost oracle or a guaranteed
optimal ordering. Simulated uniqueness facts never enter the actual K or Delta.

`max_checks_per_round` controls the fairness quantum and must be positive when
discovery is enabled. With a quantum of one, each continuously eligible cell
receives a check before another starts its next round. A quantum of three allows
up to three checks before yielding. Larger quanta may complete a small projection
earlier, but can leave later targets unattempted under a small total allowance.
The hard total never resets or grows, whatever the quantum.

A SAT sample is stored only in that cell's discovery evidence, and all its
previous values are blocked on the next check. Other cells have separate blocking
sets. A cell stops being eligible once UCP or another proof supplies its domain;
any partial discovery evidence remains partial in the report.

An inconclusive check is not repeated just because unrelated UCP facts changed:
the original C/P formula is unchanged. Optional `retry_solver_timeout_ms` permits
continuation only with a strictly larger finite per-process budget, bounded by
`max_retries_per_cell` (default one). The retry timeout is None by default, so no
budget escalation happens unless explicitly configured. The larger budget remains
local to that cell for subsequent checks; other cells retain their initial limit.
An initially unlimited timeout is never shortened or retried as a budget increase.
Repeated unknown at the same budget cannot loop. Every retry counts toward the
same discovery hard total. A value-size/representation failure is not retried.

```rust
let discovery = PrivacyDomainDiscoveryOptions {
    max_solver_checks: 64,
    max_checks_per_round: 1,
    max_retries_per_cell: 1,
    retry_solver_timeout_ms: Some(10_000), // Optional escalation from an initial 2,000 ms.
    ..Default::default()
};
```

The policy identifier is `original-fair-subset-exclusion-resumable-v3`. This scheduling
applies to domain discovery. Existing uniqueness scheduling and finite-candidate
refinement retain their own policies and separate budgets.

Optional `use_targeted_subsets: true` can use literal original subsets to prove
exhaustion. Samples still come exclusively from the full original model. Every
subset probe and full fallback consumes its own check from the same total.
See [Targeted SMT Recovery](targeted-smt-recovery.md) for the safety argument,
selection limits, counters, and an equal-budget demo. This option defaults to false.

## Original-Model Reasoning

Let `C` denote the original circuit, `P` concrete public observations, and `S`
the target values seen so far. Original satisfiability is established first.
Unknown or inconsistent initial contexts produce no recovered domains.

1. Start with an empty S and check `C AND P AND x NOT IN S`.
2. SAT provides a feasible target value v. Normalize it in the actual field and
   add v to S. Do not fix the other witness cells.
3. Repeat, excluding every previously observed target value.
4. UNSAT proves that S contains every possible x. Each value in S already has
   a satisfying witness, so S is the complete marginal projection.
5. Export S to Delta, collapsing a singleton to `Exact`, and resume UCP.

The SMT snapshot is captured before inferred UCP assertions can be written.
Every invocation recreates a separate query file from that immutable snapshot.
Full-model searches additionally reuse established `Exact` advice-cell facts
from the current Delta as redundant equalities. They must already follow from
the original `C AND P`; finite domains, sampled values, and uniqueness facts
without values are not exported. The queried cell and its copy aliases are
excluded. The exact-fact cache is refreshed after propagation, so values learned
through SMT-to-UCP feedback are available to subsequent searches without changing
the original snapshot. Blocking is by target field value, not by whole witness
assignment, so irrelevant free witnesses cannot prevent proving a singleton
projection. Targeted subset checks and independent validation remain free of
these extra equalities. This optimization does not add solver invocations or
reset any search allowance; a runtime improvement is not guaranteed.

With targeted subsets disabled, completing a projection with N values requires N SAT responses and one terminal
UNSAT response. The last probe is allowed even at the retained-value cap: a
two-value projection can complete in three checks with `max_values_per_cell = 2`.
If that probe is SAT instead, it establishes an additional value beyond the cap;
the extra sample is counted but not retained. No domain is exported.

## Partial Results And Reports

`PrivateCellReport.domain_discovery` contains:

- `Complete`: exhaustion proved by original-context UNSAT or a literal-subset UNSAT.
- `Partial`: feasible samples only, not a covering domain.
- `observed_values`, actual `solver_checks`, `models_found`, and `retry_checks`.
- `full_solver_checks`, `subset_solver_checks`, and subset outcome counts partition
  and explain the actual invocation cost when the optional subset path is enabled.
- `witnessed_non_unique` and a typed limitation such as `QueryLimit`,
  `DomainSizeLimit`, `SolverTimeout`, or `SolverUnknown`.

`None` means no discovery attempt. Aggregate counts are in
`report.domain_discovery_statistics`; uniqueness query counts remain separate.
`attempted_cells` counts distinct cells. `resumed_checks` counts checks after a
cell's first invocation; `retry_checks` is a subset of that count, not an extra
cost. Both are already included in `solver_checks`. Successful continuation clears
an earlier discovery timeout, while the cumulative cost and retry count remain.
Two distinct SAT values prove non-uniqueness even if enumeration is incomplete.
One sample alone never becomes `Exact`. Partial samples never enter K or Delta.
Ordinary uniqueness queries may still succeed after a partial discovery attempt;
that success does not relabel the earlier enumeration as complete.

An empty initial UNSAT, duplicate excluded field value, malformed model, field
mismatch, or solver execution error fails the analysis instead of fabricating a
conclusion. A size cap or solver timeout remains an incomplete result, not proof
of secrecy. `Analyzed` alone does not certify completeness: an ambiguous cell
may have partial evidence and no recovered domain.

Complete domains describe each cell separately. Values from different reported
sets need not coexist in one witness, so their Cartesian product is not a joint
solution set. Neither cardinalities nor counts of ambiguous cells measure entropy
or cryptographic security.

Fresh `validate_private_recovery_report` checks original-constraint coverage of
exported domains without assuming the recovered facts. It does not independently
check every sample's feasibility or certify the discovery status label. These
checks rely on the frontend encoding and SMT solver; they are not a formal
verification of the Rust implementation or protocol zero knowledge.

## Demonstration

No lookup, range check, or pre-existing candidate set is supplied:

```text
public product = 21
s*s - 10*s + product = 0
d*(s-5) = 0
```

The quadratic is expanded, so the syntactic UCP ROOT rule does not factor it.
With ordinary uniqueness queries disabled, coarse UCP produces no domain for s
or d. Discovery finds s=3 and s=7, then proves there is no third value. The
complete set `{3,7}` implies s-5 is nonzero; UCP therefore recovers `d = 0`
without querying d. This handoff-focused demo explicitly uses a three-check
quantum, so s can complete before yielding to d. The actual supplied advice
witness is never a recovery fact.

```sh
cargo test --offline -p korrekt demo_smt_discovers_a_private_domain_without_ucp_candidates -- --nocapture --test-threads=1
cargo test --offline -p korrekt demo_fair_domain_discovery_recovers_later_targets_with_a_small_budget -- --nocapture --test-threads=1
cargo test --offline -p korrekt privacy_discovery -- --test-threads=1
```

Tests cover terminal exhaustion, value/check boundaries, injected unknown and
timeout outcomes, original-context isolation, full-width and signed values,
changed public observations, free witnesses, fixed-copy targets, and interaction
with refinement and ordinary uniqueness queries. The demo prints elapsed times
and separately performs fresh coverage validation. It demonstrates extra
analysis capability, not a speedup or a measured general recovery rate.

The fair-scheduling demo has three targets, with the first one unconstrained:

```text
public p = 21
a is free
b*b - 2*p*b + p*p = 0
c - b - 2 = 0
```

With a four-check hard total and one-check rounds, UCP priority selects the later
private chain first, and fairness also gives a a check. SMT proves b=21 and UCP
derives c=23. A prior c model sample is not the justification for its recovery.
The overall report stays query-limited because a is unresolved. A deterministic
scheduler regression also compares equal four-check totals: alternation can
complete a later singleton where spending all four checks on a broad first
projection never reaches it. These are coverage regressions, not recovery-rate
or timing estimates.

Existing schema-v3 recovery benchmarks explicitly disable both enumeration and
refinement and record their zero allowances. New checks are not hidden inside
the old uniqueness count or used to claim the old timings cover stronger analysis.

## Remaining Limits

Search can stop at its total/value/time limits and need not reach every target.
It runs on the currently supported concrete-public privacy frontend, not every
Halo2 feature or unsupported lookup-table form. Wide feasible projections and
hard nonlinear relations can remain unresolved. Correctness arguments, broader
independently authored examples, and repeated discovery measurements remain
separate work toward the abstract.

## Local Verification Snapshot

The initial discovery implementation on the default Zcash/Pasta backend passed 301 tests
with zero failures and two opt-in tests ignored (49.94 seconds). That initial step added
nine deterministic discovery regressions, fourteen Halo2 integration regressions,
and one end-to-end demo. The package all-target check, touched-file formatting
check, and diff whitespace check passed. Other Halo2 feature backends and the
opt-in repeated measurement/full-hash inversion tests were not run in this step.

After fair, resumable scheduling, the serial package suite passed 316 tests with
zero failures and two opt-in tests ignored (47.61 seconds). Ten new deterministic
scheduler regressions, four new Halo2 regressions, and the fair-scheduling demo
passed. The demo used four discovery checks and recovered two private targets;
fresh validation checked their covering claims against the original constraints.
Its single debug run took about 35 ms for recovery and 26 ms for fresh validation,
not a repeated speedup measurement. The ignored tests and other feature backends
remain untested in this step. The package all-target check, touched-file formatting
check, and diff whitespace check also passed after the scheduling changes.

The optional targeted-exclusion step subsequently passed 334 tests with zero
failures and two opt-in tests ignored (48.98 seconds), adding 18 regressions/demo
tests. Its safety argument, counters, disabled default, and verification scope
are recorded in [Targeted SMT Recovery](targeted-smt-recovery.md).
