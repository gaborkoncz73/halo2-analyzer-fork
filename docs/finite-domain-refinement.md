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

Pass these options to `analyze_private_recoverability` as before. The outer
`PrivacyAnalysisOptions::default()` enables refinement with 160 checks and at most
128 candidates per cell, alongside discovery and fast probes. The standalone
`PrivacyDomainRefinementOptions::default()` has zero checks, so assigning it
explicitly disables candidate checking. Use the named ablation profiles for
component comparisons; see [the standard configuration](unified-private-recovery.md#standard-and-ablation-configurations).

Selected private cells, and optionally useful non-target advice cells, with an
existing `FiniteSet` of at most `max_candidates_per_cell` distinct field values
are examined. Non-target work shares the bridge allowance and cannot spend the
reserved first-target checks. An enabled size
limit must be between 2 and 256, the existing UCP representation cap. No interval
variant is introduced. Unbounded cells are not enumerated across the field.
Exact values do not need this additional search.

The separate [SMT domain discovery](smt-domain-discovery.md) option now handles
selected cells with no inferred domain. It enumerates target values and exports
only after original-model exhaustion. Both searches can be enabled together;
already complete discovered sets are not redundantly refined.

The domain budget is a separate hard total on actual candidate-feasibility solver
invocations. Recovery inherits coverage from the established Delta invariant
instead of rechecking it. It never resets on progress. An initial full attempt
with N candidates costs at most N checks. Progress-gated continuations share the same
remaining allowance and reuse previous proofs. The usual uniqueness-query
allowance, bridge/retry limits, initial SAT checks, and optional fresh validation
remain separate.
Each domain check uses the initial per-process timeout, not the uniqueness retry
floor. Total report time includes refinement; no global wall-clock deadline for
synthesis, UCP, or the entire analysis is promised.

The [joint scheduler](unified-private-recovery.md) can choose refinement's internal
fast uniqueness strategy if fewer than two feasible values are known and its
estimated cost is lower than candidate enumeration. It is not a separate third
operation. Feasible values from that attempt are shared: candidate refinement
does not recheck them. Coverage is inherited from Delta, not inferred from cached
samples. Probe attempts retain their separate semantic
allowance and retry history; they do not spend candidate-refinement checks.

## Cell Selection

`RefineNext` ranks eligible cells instead of always taking the first CellId.
The policy is `established-domain-refinement-v7` and is also
recorded in measurement metadata. Complete domains are never selected again.
Partial attempts can resume only after the global knowledge
generation advances: established uniqueness or value-domain information must
change, not merely sample caches or statistics. At most one attempt per cell is
permitted in a generation. All continuations retain the original hard check cap.

An attempt deliberately yielded to propagation is resumed first once a new
knowledge generation makes it eligible. This is not an unchanged-state retry:
yielding requires a newly proved candidate exclusion, and all checks retain the
same cumulative allowance. Otherwise fresh eligible cells take priority over retries. Among retries, the oldest
knowledge generation and then the least recent attempt take priority. Cost and
conditional-gain scoring apply within this fairness shortlist; they cannot
repeatedly promote a recently retried cell ahead of older eligible refinements.
Other operation families retain the joint scheduler's existing ordering.

A cell with N distinct field candidates has a full-attempt cost estimate of
N invocations, with no coverage recheck. Cells whose full attempt fits the remaining
allowance take priority. A cheap shortlist keeps at most 32 cells, ordered by
budget fit, candidate count, then CellId. Unselected cells remain eligible later.

Before general scoring, the scheduler looks for critical candidates derived from
affine zero roots of factors in existing product equations. For `a*(c*v+d)=0`,
excluding a possible root of `c*v+d` may establish the missing nonzero premise.
The root is computed with existing field-aware expression-domain projection;
it is not inserted into Delta or treated as an infeasibility proof. Recognition
examines at most 64 factors per equation and does not factor expanded polynomials.

Critical exclusions are included before evenly spaced samples in the existing
limit of four hypothetical exclusions per cell. Each simulation runs the complete UCP problem,
including lookup projections, on cloned K/Delta state. This can expose useful
non-singleton refinements: excluding 5 from {3,5,7}, for example, can force d=0
in d*(s-5)=0 without recovering s. Field-equivalent singleton domains are
simulated by canonicalizing the remaining value instead of excluding it.

If a budget-fitting critical exclusion predicts a new exact target or a tighter
domain for another target, that premise-unlocking shortlist is used without
scoring all general alternatives. Otherwise the earlier general shortlist is
retained. Within the shortlist, budget fit and predicted premise-unlocking target
gain precede the mean simulated gain per estimated solver
invocation: newly exact targets, refined target domains, new unique targets,
refined cell domains, then new unique cells. Ties prefer fewer checks and the
smaller CellId. Rates use exact integer cross-products, not floating-point
weights. With one eligible cell, ordinary simulations are skipped unless critical
candidate planning is needed. With only one remaining check the cheap ordering
decides. Existing score caching also retains the candidate order and predicted
yield points. Joint action selection reuses this benefit instead of simulating
the same planned operation again or replacing it with a uniqueness-only probe.

These are bounded conditional-gain estimates, not feasibility probabilities or
SMT-runtime predictions. Simulated exclusions and their consequences never enter
the actual recovery state. They consume no solver checks; only the chosen cell's
original-model queries can justify exclusions. Simulation work is not an
end-to-end CPU deadline, and neither optimal ordering nor a speedup is guaranteed.

## Original-Model Reasoning

Let `C` denote original constraints, `P` public observations, and `D` an already
established covering domain from the current Delta. Original satisfiability must
already have been established. Arbitrary proposed candidate sets are not valid
recovery premises; they require independent verification first.
Let `R` denote redundant exact and small-domain assertions established for other
cells under `C AND P`; the queried cell and its copy aliases are omitted.

1. Reuse the established coverage of `D`, including domains tightened by UCP.
2. For each candidate v in `D`, check `C AND P AND R AND x = v` independently.
3. UNSAT excludes v. SAT certifies v as feasible. Unknown or untested values stay.
4. Merge the retained superset into Delta. Run UCP to a fixed point again only
   if the merge changes Delta; otherwise continue searching with the existing
   fixpoint and updated refinement evidence.

Candidate checks start with the planned critical exclusions. After an actual
UNSAT exclusion with predicted propagation benefit, refinement can yield a
partial covering domain immediately, before checking the remaining candidates.
This deliberate yield is `Partial`, not a timeout or exhausted budget. SAT,
UNKNOWN, or a simulation alone cannot exclude a candidate or trigger this yield.
After real propagation, the suspended attempt reuses the new Delta coverage and proved values
when valid and continues under the original total budget. It may finish without
further shrinking, by certifying the feasibility of the retained values.

Step 2 skips a candidate already witnessed by a full-context SAT model in the
same analysis run. Such values count as feasible, but skipped checks consume no
solver allowance. Unknown, untested, and merely hypothesized values are not
cached as feasible. Continuations also remember earlier SAT candidates and
UNSAT exclusions without relying on the caller to resend those samples.
Each SAT candidate model also supplies samples for other incomplete target
domains. These enter W only, not Delta, and may certify completeness or
non-uniqueness without another solver invocation. The
[shared-model description](shared-model-samples.md) gives the data flow and
distinguishes per-cell projections from joint assignments.
An updated domain is accepted as covering because it comes from the established
recovery state, even if its tightening was performed by UCP rather than SMT.
A domain contradicting cached feasibility fails closed. Coverage alone does not
certify that every remaining candidate is feasible or make the domain complete.

An immutable original snapshot is captured before ordinary semantic queries can
write inferred facts. Each domain check writes a separate SMT file from that
snapshot. Candidate feasibility and full discovery checks reuse
established exact advice-cell values and bounded finite covering domains.
Each finite set must already be a sound Delta-domain; it need not be complete.
Model samples, hypothetical domains, and uniqueness without value information
are not exported. The queried cell and its copy aliases are excluded from
the added assertions. The proposed covering domain is never assumed.
At most 16 raw entries per finite domain and 512 candidate equalities across
multi-value domains are exported, preferring smaller domains with stable ties.
Larger sets are omitted whole, never truncated; singleton facts remain available.
The assertions in `R` follow from `C AND P` and do not change its solution set.
Recovery trusts sound propagation and previously established domain facts. It
does not add `x IN D` and ask `x NOT IN D` as a circular coverage proof.
Candidate assumptions do not accumulate between checks, and later strengthening
of the ordinary analyzer cannot strengthen the snapshot. Full gates, copy
equalities, and correlated lookup tuples are retained. Independent report
validation still uses only the original constraints and observations.

The analyzer also remembers whether UCP assertions have ever been written.
Clearing its export vectors cannot make an already strengthened SMT file usable
as a fresh validation context or original snapshot.

Independent report validation still asks coverage queries against the original
context without assuming recovered claims, and can refute forged domains.
Standalone test helpers retain explicit verification for arbitrary proposed sets;
the production recovery path always uses established coverage. Candidate timeout results do not
exclude that value or prevent checking later candidates while budget remains.
Malformed output and execution errors remain errors, not inconclusive proofs.
An empty retained set contradicts original SAT and also fails the run.

## Report Meaning

`PrivateCellReport.domain_refinement` records the latest attempt's candidate
counts, cumulative actual solver checks across that cell's attempts, and one of:

- `Complete`: coverage established and every remaining value established feasible.
- `Partial`: coverage established; unresolved candidates remain in the superset.
- `CoverageUnknown`: retained for standalone checks and historical reports; not
  produced by recovery refinement of established Delta domains.
- `None`: no finite-domain attempt; this does not certify projection completeness.

The separate `PrivateCellReport.domain_is_complete` flag describes the final
domain, not just the last refinement attempt. It also recognizes singleton
domains and covering sets whose members were all certified feasible by other
operations. The same certificate is available to UCP and the scheduler through
`UcpValueFacts::domain_is_complete`; complete targets are not narrowed or retried,
but their values remain usable when reasoning about other cells. A false flag
means completeness was not established. A true flag is scoped to the current
original context, not reusable under changed public observations or speculative
assumptions. Independent validation does not trust the flag as a coverage proof.

A covering singleton is a special case: original SAT and exclusion of every
other value already establish its feasibility and exact value, even if its own
candidate query was unknown or unattempted. Two distinct feasible values prove
non-uniqueness even if other candidates are still unresolved.

Aggregate counts are in `report.domain_refinement_statistics`. Uniqueness-query
attempts remain separate. `Analyzed` is not a promise that every finite domain
is complete; inspect the per-cell domain evidence and budget-exhaustion flag.
Progress can make additional cells eligible or reopen a partial attempt.
`attempted_cells` counts distinct cells, not retries; `complete_domains` counts
completed cells once, and `removed_candidates` counts newly proved SMT exclusions
without charging cached exclusions again. The shared total cap is unchanged.

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
