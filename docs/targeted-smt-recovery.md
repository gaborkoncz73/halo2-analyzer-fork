# Targeted Original Subsets For Private Domain Discovery

## Purpose

Optional domain discovery can now prove exhaustion using a small target-local
subset of literal original gate/copy equations. It still obtains **every feasible
sample from the full original model**. This can reduce the size of a terminal
UNSAT problem without changing the property being established.

This feature only affects [domain discovery](smt-domain-discovery.md). Ordinary
uniqueness queries, finite-candidate refinement, and the SMT-only measurement
reference are unchanged. It is disabled by default and does not guarantee faster
or complete recovery on arbitrary circuits.

## Enable It

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
        use_targeted_subsets: true,
        ..Default::default()
    },
    ..Default::default()
};
```

Pass options to `analyze_private_recoverability` with concrete public observations
and explicitly selected private advice cells. Targeted metadata is collected only
when both discovery and this option are enabled. Existing default callers pay no
metadata capture or subset-query cost.

## Evidence And Safety

Let C be the original constraints, P the concrete public observations, E a
conjunction of some original equations, and V the target's observed values.

1. Establish full original `C AND P` satisfiability, as before. Inconsistent or
   inconclusive initial contexts export no recovered domains.
2. Obtain the first target sample from `C AND P AND x NOT IN V`.
3. Once at least one full-original sample exists, try `E AND P AND x NOT IN V`.
4. Subset UNSAT proves exhaustion for the original model because `C implies E`.
   All retained samples already have full-original witnesses, so V is a complete
   marginal projection. A singleton becomes Exact and feeds the UCP fixed point.
5. Subset SAT or typed unknown/timeout proves no exhaustion and supplies no sample.
   Schedule a separate full-original query with the same blocked values next.
6. Full SAT adds a feasible sample; full UNSAT closes the domain; full unknown
   retains partial evidence and follows the existing explicit retry policy.

The subset never assumes inferred UCP facts, candidate equalities for other
cells, or actual advice assignments. Cached subset text is captured before any
UCP strengthening; each check creates a fresh query file. Blocking sets and
pending-full phases remain independent per cell across fair scheduling rounds.

Subset SAT is deliberately weaker evidence. For example, original gates may
permit roots 3 and 7 while an inline lookup permits only 3. Omitting that lookup
allows a spurious subset witness with root 7, which cannot be recorded as a
feasible original value. The fallback original query excludes it.

This is a conditional correctness argument relative to the original frontend
encoding and trusted solver results, not a formal verification of the Rust code
or a proof of protocol zero knowledge. Independent coverage validation remains
available on the unchanged original circuit.

## Selection And Limits

The existing SMT encoder retains whole original gate/copy assertion bodies and
their canonical variable names. Selection uses encoder metadata, not SMT text
parsing or UCP-generated algebra. Nonlinear gate equations are eligible.

- At most 4,096 original equations are retained when capture is enabled.
- A target subset contains at most 64 equations selected within two variable hops.
- Concrete public variables are leaves; sharing a public observation does not
  pull in otherwise unrelated gates.
- Whole equations can be omitted but are never split, projected, or rewritten.
- Lookup assertions are not collected into targeted subsets in this step. They
  remain in all full-original SAT/exhaustion queries.
- Targets with no selected equations immediately use one full check, with no
  phantom subset invocation counted.

These are efficiency limits, not premises for recovery. A missing distant
constraint, retention cap, or omitted lookup only weakens E. An insufficient
subset therefore needs full fallback, not a stronger conclusion.

## Cost Accounting

Every subset probe and every fallback is a separate solver invocation and consumes
the same hard `max_solver_checks` allowance. The scheduler still performs one
invocation per step and runs UCP again between steps. The hard total never resets.
Subset unknown schedules fallback at the existing timeout, not an automatic retry
escalation. An unknown full check can use the explicitly configured larger timeout.

Reports partition discovery `solver_checks` into `full_solver_checks` and
`subset_solver_checks`. `subset_fallbacks`, `subset_unknown_checks`, and
`subset_unsat_proofs` explain the subset outcomes. Existing model, resumed, and
retry counts keep their meanings; a subset SAT never increases `models_found`.
Initial SAT, ordinary uniqueness, refinement, and independent validation retain
their separate counters.

A singleton can complete in one full SAT plus one subset UNSAT. A two-value set
can require full SAT, subset SAT, full SAT, subset UNSAT: four checks instead of
three full checks. If the budget stops after subset SAT, the result stays Partial;
no uncounted fallback or Exact fact is produced. Mandatory original SAT and
feasible-model search still face the entire circuit, so this does not bypass
hard original satisfiability problems.

Policy identifiers are `original-fair-subset-exclusion-resumable-v3` and
`literal-targeted-exclusion-unsat-only-v1`. Existing schema-v3 measurement metadata
records these identifiers and the disabled default option; old benchmark timings
do not measure this opt-in path.

## Demo And Tests

```text
public amount = 21
s*s - 2*amount*s + amount*amount = 0
next - s - 2 = 0
16 unrelated constraints: v_i*v_i - (amount+i)^2 = 0
```

The expanded quadratic needs semantic reasoning. Full-original SAT supplies s=21;
the first two original gate equations suffice to exclude another value. UCP then
recovers next=23. The independent quadratic cells are not pulled into the subset
through the shared public amount. The demo compares full-only and targeted
discovery with equal check allowances, prints end-to-end timings and actual check
counts, then independently validates the exported covering claims.

```sh
cargo test --offline -p korrekt demo_targeted_subset_exclusion -- --nocapture --test-threads=1
cargo test --offline -p korrekt privacy_discovery -- --test-threads=1
cargo test --offline -p korrekt privacy_subset -- --test-threads=1
cargo test --offline -p korrekt validation_subset_tests -- --test-threads=1
```

Regression tests also cover exact literal provenance, disabled capture, selection
caps, per-cell fallback persistence, typed unknown, fatal malformed output,
budget exhaustion, missing target metadata, long omitted links, infeasible lookup
alternatives, and isolation from subsequent UCP strengthening. SMT tests must
remain serial because the analyzer currently shares output paths.

## Local Verification Snapshot

On the default Zcash/Pasta backend, the serial package suite passed 334 tests with
zero failures and two opt-in tests ignored (48.98 seconds). This step added 18
tests: three pure selection regressions, five discovery state regressions, eight
Halo2 integration regressions, one encoder-provenance regression, and one demo.
The all-target check, touched-file rustfmt check, and diff whitespace check passed.
Other Halo2 feature backends, the ignored full-hash inversion test, and repeated
release performance measurements were not run. The demo's elapsed times are
single debug measurements, not evidence of a general speedup or recovery rate.
