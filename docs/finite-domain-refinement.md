# Bounded Finite-Domain SMT Refinement

## Purpose

Uniqueness queries distinguish one possible value from at least two. They do not
normally recover a complete multi-value projection. UCP may therefore report
`Candidates({0,...,15})` when the original circuit permits only `3` and `7`.

Optional finite-domain refinement checks an existing small candidate superset
against the original Halo2-to-SMT encoding and concrete public observations.
It removes impossible candidates and feeds the smaller Delta back into UCP.
This implements the abstract's analysis of narrowed private possibilities, not
only exact recovery. It is an extension to the recovery pipeline, not a new
claim that all practically recoverable secrets will be found.

## Configuration

```rust
use korrekt::circuit_analyzer::ucp::{
    privacy::PrivacyAnalysisOptions,
    privacy_domain::PrivacyDomainRefinementOptions,
};

let options = PrivacyAnalysisOptions {
    solver_timeout_ms: Some(2_000),
    domain_refinement: PrivacyDomainRefinementOptions {
        max_solver_checks: 64,
        max_candidates_per_cell: 16,
    },
    ..Default::default()
};
```

Pass these options to `analyze_private_recoverability` as before. Refinement is
disabled by default (`max_solver_checks = 0`); existing callers using default
options incur no extra domain checks. Full struct literals need the new field
or `..Default::default()`.

Only explicitly selected private cells with an existing `FiniteSet` of at most
`max_candidates_per_cell` distinct field values are examined. An enabled size
limit must be between 2 and 256, the existing UCP representation cap. No interval
variant is introduced. Unbounded cells are not enumerated across the field.
Exact values do not need this additional search.

The separate [SMT domain discovery](smt-domain-discovery.md) option now handles
selected cells with no inferred domain. It enumerates target values and exports
only after original-model exhaustion. Both searches can be enabled together;
already complete discovered sets are not redundantly refined.

The domain budget is a separate hard total on actual solver invocations, including
covering checks. It never resets on progress. A full attempt with N candidates
costs at most N+1 checks. The usual uniqueness-query allowance, bridge/retry
limits, initial SAT checks, and optional fresh validation remain separate.
Each domain check uses the initial per-process timeout, not the uniqueness retry
floor. Total report time includes refinement; no global wall-clock deadline for
synthesis, UCP, or the entire analysis is promised.

## Cell Selection

`RefineNext` ranks eligible cells instead of always taking the first CellId.
The policy is `coverage-candidate-feasibility-cost-domain-gain-v2` and is also
recorded in measurement metadata. Existing eligibility, one-attempt-per-cell
bookkeeping, and the hard total solver-check cap are unchanged.

A cell with N distinct field candidates has a full-attempt cost estimate of
N+1 invocations, including coverage. Cells whose full attempt fits the remaining
allowance take priority. A cheap shortlist keeps at most 32 cells, ordered by
budget fit, candidate count, then CellId. Unselected cells remain eligible later.

For each shortlisted cell, up to four evenly spaced candidates are hypothetically
excluded, one per simulation. Each simulation runs the complete UCP problem,
including lookup projections, on cloned K/Delta state. This can expose useful
non-singleton refinements: excluding 5 from {3,5,7}, for example, can force d=0
in d*(s-5)=0 without recovering s. Field-equivalent singleton domains are
simulated by canonicalizing the remaining value instead of excluding it.

Scores compare, lexicographically, the mean simulated gain per estimated solver
invocation: newly exact targets, refined target domains, new unique targets,
refined cell domains, then new unique cells. Ties prefer fewer checks and the
smaller CellId. Rates use exact integer cross-products, not floating-point
weights. With one eligible cell or only one remaining check, simulations are
skipped and the cheap ordering decides.

These are bounded conditional-gain estimates, not feasibility probabilities or
SMT-runtime predictions. Simulated exclusions and their consequences never enter
the actual recovery state. They consume no solver checks; only the chosen cell's
original-model queries can justify exclusions. Simulation work is not an
end-to-end CPU deadline, and neither optimal ordering nor a speedup is guaranteed.

## Original-Model Reasoning

Let `C` denote original constraints, `P` public observations, and `D` a proposed
candidate superset. Original satisfiability must already have been established.

1. Check `C AND P AND x NOT IN D`. Only UNSAT establishes coverage.
2. For each candidate v, check `C AND P AND x = v` independently.
3. UNSAT excludes v. SAT certifies v as feasible. Unknown or untested values stay.
4. Merge the retained superset into Delta. Run UCP to a fixed point again only
   if the merge changes Delta; otherwise continue searching with the existing
   fixpoint and updated refinement evidence.

An immutable original snapshot is captured before ordinary semantic queries can
write inferred facts. Each domain check writes a separate SMT file from that
snapshot. Coverage checks add only the domain-exclusion assertion. Candidate
feasibility checks also reuse current, established `Exact` advice-cell facts as
redundant equalities; finite domains, model samples, and uniqueness without a
value are not exported. The queried cell and its copy aliases are excluded from
these extra equalities. The proposed covering domain is never assumed.
Candidate assumptions do not accumulate between checks, and later strengthening
of the ordinary analyzer cannot strengthen the snapshot. Full gates, copy
equalities, and correlated lookup tuples are retained. Independent report
validation still uses only the original constraints and observations.

The analyzer also remembers whether UCP assertions have ever been written.
Clearing its export vectors cannot make an already strengthened SMT file usable
as a fresh validation context or original snapshot.

If coverage is SAT, a circuit-valid value lies outside the proposed set: the run
fails rather than exporting a false covering claim. If coverage is unknown, no
SMT exclusions from that attempt are exported. Candidate timeout results do not
exclude that value or prevent checking later candidates while budget remains.
Malformed output and execution errors remain errors, not inconclusive proofs.
An empty retained set contradicts original SAT and also fails the run.

## Report Meaning

`PrivateCellReport.domain_refinement` records candidate counts, actual check
counts, and one of:

- `Complete`: coverage checked and every remaining value established feasible.
- `Partial`: coverage checked; unresolved candidates remain in the superset.
- `CoverageUnknown`: coverage could not be checked; no new exclusions exported.
- `None`: no finite-domain attempt; this does not certify projection completeness.

A covering singleton is a special case: original SAT and exclusion of every
other value already establish its feasibility and exact value, even if its own
candidate query was unknown or unattempted. Two distinct feasible values prove
non-uniqueness even if other candidates are still unresolved.

Aggregate counts are in `report.domain_refinement_statistics`. Uniqueness-query
attempts remain separate. `Analyzed` is not a promise that every finite domain
is complete; inspect the per-cell domain evidence and budget-exhaustion flag.
Progress can make additional selected cells eligible, but each cell receives
at most one domain attempt in a run, and the shared total cap is unchanged.

Complete sets are marginal projections: every remaining value has some valid
witness, not necessarily the same witness. Cartesian products of separately
reported sets need not be jointly feasible. Their sizes are not entropy or
cryptographic security scores. Fresh `validate_private_recovery_report` still
checks covering claims only; it does not separately certify each feasible
candidate or the new completeness label.

## Demonstration

The fixture has public product 21 and these constraints:

```text
s in {0,...,15}
s*s - 10*s + 21 = 0
d*(s-5) = 0
```

The quadratic is expanded, so the syntactic UCP ROOT rule does not directly
factor it. With ordinary semantic queries disabled, UCP alone retains sixteen
candidates for s and does not recover d. Refinement uses one original covering
check plus sixteen feasibility checks. It recovers the complete projection
`s in {3,7}`, excluding fourteen candidates. Since s-5 is now provably nonzero,
UCP learns `d = 0` without a separate uniqueness query for d. Both s=3 and s=7
are checked as valid witnesses with MockProver; analysis does not read their
assigned values as recovery facts.

```sh
cargo test --offline -p korrekt demo_finite_domain_refinement_restarts_ucp_without_guessing_the_secret -- --nocapture --test-threads=1
cargo test --offline -p korrekt privacy_domain -- --test-threads=1
```

The demo prints elapsed times, budgets, candidate evidence, and fresh independent
coverage validation. It demonstrates extra recovery, not a speedup claim. Tests
also cover exact private-input recovery, newly eligible domains after feedback,
partial budgets, injected timeout/unknown outcomes, signed representatives,
equivalent field values, public-observation changes, lookup tuple correlations,
forged covering domains, and initial inconsistency.

## Limits

This is bounded refinement of already inferred small sets, not a complete
finite-field inversion algorithm or automatic discovery of every narrow domain.
The independent checks rely on the SMT encoding, field interpretation, and solver.
They are not a formal proof of the Rust implementation or of protocol zero
knowledge. The abstract still needs a correctness argument, wider independently
authored applications, and representative repeated recovery measurements.

Existing schema-v3 performance measurements keep refinement and discovery disabled
and record those policies explicitly. The new demo's extra checks must not be hidden inside
the old per-cell uniqueness count or used to claim the old speedup applies to
the stronger analysis.

## Local Verification Snapshot

On the default Zcash/Pasta backend, the serial package suite passed 277 tests with
zero failures and two opt-in tests ignored (46.70 seconds). Six new deterministic
logic regressions, ten new Halo2 regressions, and the new end-to-end demo passed.
The demo measured approximately 14 ms for the coarse UCP-only result, 103 ms for
the stronger analysis including 17 domain checks, and 42 ms for separate fresh
coverage validation. These are illustrative single debug runs, not repeated
performance estimates. Other Halo2 feature backends were not tested in this step.
