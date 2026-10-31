# Joint Cell And Operation Scheduling

## Workflow

UCP now also preserves supported finite lookup tuple correlations and performs
bounded conditional filtering of finite radix domains. See
[Relational UCP Propagation](ucp-relational-propagation.md) for premises and
effort limits. Earlier invocation measurements below predate these stronger
rules and are not measurements of the new propagation engine.

`recover_private_inputs` in `privacy.rs` selects a cell and an operation together,
instead of exhausting refinement, then discovery, then uniqueness queries.
`privacy_search.rs` contains the attempt/retry state, action shortlisting,
cross-operation heuristic, internal strategy selection, and shared feasible
samples. `privacy_report.rs` contains report types, summary and formatting,
re-exported through the existing `privacy` API. There are only two top-level operations:
`Refine` and `Discover`. `PrivacyAnalysisOptions::default()` enables candidate
refinement, domain discovery, and the internal fast-probe strategy together.
The scheduler chooses eligible work from the current knowledge and remaining
allowances; no circuit-specific switch selects which capabilities are available.

## Standard And Ablation Configurations

The standard configuration uses cumulative allowances of 256 semantic attempts,
160 candidate-refinement solver invocations, and 64 discovery solver invocations.
Candidate checking accepts domains of at most 128 values; discovery retains at
most 16 values per cell. These are configurable effort limits, not guarantees of
complete recovery. Progress never replenishes the cumulative allowances.

`PrivacyAnalysisProfile::Standard` preserves all configured allowances.
`with_profile(PropagationOnly | FastProbeOnly | RefinementOnly | DiscoveryOnly)`
masks unrelated search allowances for explicit component comparisons and focused
tests. Applying a profile does not replenish previously disabled or exhausted
allowances. Construct a new standard configuration before choosing an ablation.
The standalone refinement/discovery option types still default to zero checks;
the outer `PrivacyAnalysisOptions` explicitly supplies their enabled budgets.

All invoice variants obtain their options from the same `recovery_options`
helper. Their normal profile is `standard`; `combined` is a compatible name for
the same full configuration. Environment overrides change budgets, not the
algorithm based on the circuit identity. Component-disabled runs are ablations,
not the default implementation of the paper's recovery algorithm.
Previously recorded timings below and in the example notes used their recorded
historical configurations; they are not measurements of these new defaults.

## Recovery Loop

After the mandatory satisfiability check and initial UCP fixpoint:

1. Shortlist eligible operations: refine an existing covering domain or discover
   a domain for a cell without one. Select an eligible internal strategy for each
   proposed action, respecting its own allowance and previous attempts.
2. Consider selected targets and useful non-target advice cells. Non-target
   domain work must fit the shared bridge allowance and leave reserved checks
   for fresh targets. It must have predicted propagation benefit for a target.
3. Select one cell/operation pair, using established uniqueness, target priority,
   simulated propagation gain per estimated check, reusable samples, and stable
   tie-breaks. Execute only that operation, within its remaining allowance.
4. Share feasible samples, but merge only established uniqueness and covering
   domains into K/Delta. Run UCP again only if K/Delta actually changed.
5. Repeat until no permitted action remains. Report limits and partial evidence;
   failure to recover a value is not evidence of confidentiality.

`initialize_knowledge` only copies extracted constants/domains and inserts the
concrete public observations. It does not run UCP without those observations.
The first recovery propagation therefore starts from public values directly.
The SMT guard may independently use public-value UCP hints for its initial SAT
check; the verified-witness route needs no such solver hint.

The optional `PrivacyAnalysisOptions::compute_structural_baseline` defaults to
`false`. When enabled, a separate UCP run without concrete public values occurs
**after** recovery, solely for report comparisons. It does not seed recovery or
change solver exports, scheduling, or resource allowances. Reports expose
`structural_baseline_computed`; when false, `baseline_domain=None` and
`domain_refined_from_baseline=false` mean the comparison was not performed,
not that no information was recovered. `summary.refined_domains` counts only
these optional comparisons. Public-observation dependence remains a separate
original-context SMT control, not a conclusion from baseline differences.
The measurement suite's `Profile::Baseline` names a search configuration; it is
not this optional unobserved structural analysis. Its recorded options distinguish
the two, and per-cell exports include `structural_baseline_computed` explicitly.

Fast-probe domain exports compare against `problem.initial_value_facts`, not
an unobserved UCP fixpoint. Exact values and domains beyond those extracted
inputs are exported; unchanged extracted memberships may be omitted as already
encoded constraints. See [the export policy](selective-smt-domain-export.md).

There is no `RecoveryAction::Unique` and no separate final uniqueness phase.
`RecoveryStrategy::FastProbe` is an internal strategy of refinement or discovery.
It can resolve a singleton projection in one solver invocation with a cached
feasible value, or two invocations without one, without testing
every member of a large candidate superset. Candidate refinement may execute a
batch; ordinary discovery executes one check per step. An exact-only discovery
probe may execute two checks. An action is not necessarily one SMT invocation.

The existing low-level `Analyzer::query_ucp_cell_uniqueness_with_value` method
remains available to the legacy underconstrainedness pipeline. Recovery uses
the [snapshot-based seeded probe](seeded-fast-probes.md), sharing exact/domain
assertions and model projection with candidate refinement. Neither is a third
operation in the privacy scheduler.

The report also records the actual recovery timeline as `RecoveryPhase` values.
UCP entries count only selected private targets; consecutive solver actions share
one SMT phase until real propagation resumes. Per-action checks count actual
solver processes, not semantic attempts, and retain samples, state updates and
limitations separately. This observation does not execute extra queries or feed
trace data into K/Delta. `phase_report()` is the compact presentation used by
the demos; see [phase reporting](private-recovery-phase-report.md).

## Algorithm Names In Code

The original `analyze_prepared` driver was renamed, not replaced by another
implementation. Paper procedure names use PascalCase; the corresponding Rust
names use idiomatic snake_case. Public callers still use
`analyze_private_recoverability`, which validates options, prepares the circuit,
sets the solver timeout, and enters `recover_private_inputs`. The driver itself
invokes `check_sat` before initializing recovery knowledge or search. It records
the actual initial-check count on both diagnostic and recovery reports, including
any SAT-hint fallback. No public API rename is required.

`PrivacyAnalysisOptions::initial_sat_timeout_ms` optionally overrides the timeout
only for the initial SAT stage, including its hint and original-context fallback
invocations. `None` preserves the analyzer's normal timeout. The driver restores
that timeout before constructing search snapshots or running recovery, including
on diagnostic exits. Reports retain both options; neither is a whole-run deadline.

For callers that have an actual circuit witness,
`analyze_private_recoverability_with_witness` uses the same preparation and recovery
driver, but first runs `MockProver` with the supplied public observations. Only a
successful `run` **and** full `verify` establish existence. The checker discards the
prover and its private assignments; it transfers no witness values into K, Delta,
E, W, SMT assertions or scheduler simulations. Missing instance rows are padded
only for this witness check, not added to the analysis premises. A satisfying
completion of those unobserved rows is sufficient to prove existence under the
original, weaker observations.

A failed or unavailable witness check is not UNSAT: it falls back to the existing
SMT SAT path. Reports identify successful witness evidence as
`SatisfiabilityEvidence::VerifiedWitness`, with zero initial SMT checks; solver-based
existence is `Smt`. Inconsistent or inconclusive initial contexts carry no
satisfiability evidence. The ordinary `analyze_private_recoverability` entry point
remains SMT-based, and independent domain validation still checks its original SMT
context. The witness route additionally requires `F: Ord`, as required by the
backend's MockProver, without narrowing the existing public API's field bound.

Both routes assume faithful extraction/SMT encoding and a stable circuit shape,
fixed values and selectors between synthesis and witness verification. MockProver
checks the Halo2 constraints, not the correctness of the separate SMT translation.

| Paper Procedure | Rust Function Or Method | File |
| --- | --- | --- |
| `RecoverPrivateInputs` | `recover_private_inputs` | [privacy.rs](../korrekt/src/circuit_analyzer/ucp/privacy.rs) |
| `OriginalContext` | `original_context` | privacy.rs |
| `CheckSAT` | `check_sat` | privacy.rs |
| `DiagnosticReport` | `diagnostic_report` | privacy.rs |
| `InitializeKnowledge` | `initialize_knowledge` | privacy.rs |
| `InitializeSearch` | `RecoverySearchState::initialize_search` | privacy_search.rs |
| `PropagateToFixpoint` | `propagate_to_fixpoint` | privacy.rs |
| `ObserveProgress` | `RecoverySearchState::observe_progress` | privacy_search.rs |
| Exact facts and bounded domain export | `established_search_facts` | privacy.rs |
| `ShortlistActions` | `shortlist_actions` | privacy_search.rs |
| `ChooseAction` | `choose_action` | [privacy_search.rs](../korrekt/src/circuit_analyzer/ucp/privacy_search.rs) |
| `RefineDomain` | `RecoveryOperations::refine_domain` | privacy.rs |
| `DiscoverDomain` | `RecoveryOperations::discover_domain` | privacy.rs |
| `RememberFeasibleSamples` | `RecoveryEvidence::remember_feasible_samples` | privacy_search.rs |
| `MergeEstablishedResults` | `merge_established_results` | privacy.rs |
| `FactsChanged` | `facts_changed` | privacy.rs |
| `RecoveryReport` | `recovery_report` | [privacy_report.rs](../korrekt/src/circuit_analyzer/ucp/privacy_report.rs) |

The paper still abstracts over argument lists and bookkeeping. The driver dispatches
only to `RecoveryOperations::refine_domain` or `discover_domain`. Each method owns
both strategies: domain search delegates to the corresponding lower-level state
method, while fast probing delegates to the private `RecoveryOperations::fast_probe`
helper. There is no shared fast-probe continuation after the driver's match.

Each operation returns a `RecoveryStepResult`, corresponding to r in the paper:
cell identity, feasible samples, established domain/uniqueness claims, and any
limitation/retry information. Operations borrow K/Delta read-only. The driver
first remembers the samples, then calls `merge_established_results` to update
K/Delta and non-uniqueness, limitation, and retry bookkeeping in one place.
Solver costs are charged during execution, not again at merge time.
`facts_changed` consumes change flags returned by the merge, avoiding full state
copies merely to compare old/new facts.
The original SMT encoding already exists at initial SAT time; the separate
immutable query snapshot is materialized when domain searches or fast probes need it.
The SAT-check and semantic-query callbacks are injectable for deterministic tests;
the production entry point supplies the real `check_sat` function, not a previously
computed SAT result.
Shared feasible samples W (`evidence`) and redundant SMT facts (`search_facts`)
are initialized empty before the loop. The propagation flag starts true, so the
first iteration propagates the initial knowledge, observes progress, and populates
the exact facts E and selected small covering domains before scheduling any search. Later iterations use the same block only after
K/Delta changes.

The naming/extraction refactor passed the 402-test serial package suite and the
all-targets build check. All 60 paired measurement runs retained their invocation
counts, final domains, uniqueness labels, and statuses: 462 solver calls in both
versions. This refactor does not introduce a new search policy.

The subsequent operation-encapsulation refactor passed 403 tests (four opt-in
tests ignored), including a regression exercising both operations' fast-probe
strategies with actual solver results and injected timeouts. K/Delta remain
unchanged until the common merge, and probe costs are charged once. The same
60 paired runs again retained all results and the 462-call total. Formatting,
all-targets build, and whitespace checks also passed.

## Selection Heuristic

Within-operation shortlists retain finite-domain exclusion simulations and fair
discovery rounds. The joint chooser prioritizes a known-unique target needing its
value, then target work over optional bridge work. It compares conditional UCP
uniqueness gain per estimated solver invocation, prefers completing existing
sample sets, then lower cost and a stable cell/operation order. It skips joint
simulation when only one action is available.

Estimated costs are two checks for fast uniqueness, uncached candidates for
refinement, and one discovery check if feasible samples
already exist (otherwise two). The discovery estimate is a heuristic for useful
progress, not a prediction that every projection has only one value. Conditional
simulations never become evidence. Shortlists and benefit filters can miss
useful work; the ordering is neither globally optimal nor complete.

### Internal Strategy

`integrate_fast_probe` combines an eligible probe proposal with the domain-action
shortlist; it never adds a third operation. Probe eligibility still uses the
bounded attempt/retry planner in `privacy_search.rs`.

For refinement, a cached pair of distinct feasible values rules out uniqueness,
so no fast probe is proposed. Otherwise, if candidate refinement is available,
compare its estimated cost (uncached candidates) with two probe
checks. At a cost of at most two, keep candidate refinement; above two, choose
the probe. If candidate enumeration is disabled, ineligible, or already attempted,
an independently permitted probe can still perform exact-only recovery.

For discovery, keep the existing enumerator whenever it is available in the
current search pool. A singleton is recognized by its ordinary terminal UNSAT
check. Do not insert a probe to bypass another cell's discovery fairness turn.
If enumeration is unavailable, a bounded fast probe supplies exact-only recovery
without enabling full multi-value enumeration.

A successful probe merges an exact value and resumes UCP. A non-unique probe
shares its feasible samples and does not repeat the same decisive result.
Unknown/timeout results export no exact value; candidate refinement or discovery
may still run under their separate allowances. Probe retries require the existing
progress/larger-timeout conditions and hard caps. Integration never resets them.

## Shared Evidence And Correctness Boundary

The per-run cache associates each cell with normalized field values observed in
full-context satisfying models. Fast uniqueness contributes its first and
counterexample values when public observations are concrete; candidate refinement
contributes SAT values, and discovery contributes full-model samples. Literal
subset SAT results and speculative scheduling simulations never populate it.

Refinement skips cached feasible candidates. Discovery starts by blocking its
imported samples, rather than paying to find them again. Reuse is bounded by the
retained-value limit and is counted separately from discovery-produced models.
Two distinct samples establish non-uniqueness, but are not a covering domain.
One sample is not an exact recovered value. Only an appropriate UNSAT exclusion
proof establishes coverage or uniqueness; unknown/timeout results do not.

For a cell with a recorded domain, the invariant is
`W(v) subseteq Feasible_Gamma(v) subseteq Delta(v)`: samples are an inner
approximation, whereas Delta is a covering outer approximation. An absent domain
does not imply confidentiality. Exact facts E are established singleton claims,
not merely singleton sample sets in W.

`UcpValueFacts::domain_is_complete(cell)` exposes a context-scoped completeness
certificate. Under the already verified satisfiable premises, singleton covering
domains are complete automatically. Multi-value domains become complete only
when normalized full-context feasible samples cover every recorded candidate.
Uniqueness in K, a few samples, an UNKNOWN result, or a truncated enumeration
cannot set the certificate. False means unproved completeness, not necessarily
an actually incomplete projection. Field aliases are deduplicated and a sample
outside the recorded covering domain is an error.

The driver checks completeness after merging samples/results and after propagation,
so even domains completed by a different operation or a later UCP deduction are
recognized. Metadata-only completion does not restart propagation or advance the
knowledge generation. A newly explicit exact value obtained by field-alias
canonicalization does restart propagation. Complete cells are excluded from
refinement, fast probes, and optional bridge selection. UCP skips narrowing a
complete target while retaining its domain as an operand for other deductions;
the central domain-update method also prevents further narrowing.

Completeness is not transferred to derived finite domains merely because their
operands are complete: independently feasible marginals do not certify all joint
combinations. Conditional scheduling simulations use
`for_hypothetical_reasoning()`, which copies covering values without multi-value
completeness certificates. No hypothetical result is merged into the real state.
Runs with different public observations build fresh knowledge and sample caches.

`PrivateCellReport.domain_is_complete`, verbose/compact reports, and per-cell
profile exports expose the result. Fresh report validation still checks covering
claims against the original context and never trusts this flag to skip proof
queries; it does not independently recheck every feasible domain member.
The current search policy is `standard-all-searches-v10`. Earlier
measurement files are historical results, not measurements of this policy.

Candidate refinement now requests other incomplete targets' values from the same
full SAT model. These projections are shared through W, so later actions can
reuse them without extra solver invocations. Two distinct samples establish
non-uniqueness; covering-domain members all witnessed feasible establish
completeness. A model sample alone never creates a covering or exact domain.
Subset SAT results remain ineligible as sample sources. See
[shared-model samples](shared-model-samples.md) for the scope and trace fields.

The immutable original SMT snapshot and concrete public observations remain the
reference. Full recovery searches reuse established exact values and selected
small covering domains from Delta as redundant assertions. The queried cell's
own domain and all its copy aliases are omitted. Feasible samples W, hypothetical
results, and uniqueness without value information are never exported as covering
constraints. Domain completeness is not required: sound coverage suffices.
The export retains at most 16 raw entries per finite domain and at most 512
candidate equalities across multi-value domains, preferring shorter sets and
stable SMT-name ordering. Oversized or over-budget sets are omitted whole;
Delta is never truncated. Singleton facts retain their existing unrestricted
export. Finite-field aliases are normalized and copy domains are intersected;
empty intersections fail closed. Facts are rebuilt after real K/Delta progress,
using the current observations, not reused across separate analysis runs.
Literal subset proofs and independent report validation retain their original,
unstrengthened premises. No private
witness assignment is used as an analysis premise. These invariants preserve the
existing soundness conditions; regression tests are not a formal correctness proof.

## Limits And Accounting

- `max_semantic_queries`: internal fast-probe cell attempts, including retries
  and bridges; a cached feasible value saves the initial model search, so one
  attempt needs one or two solver invocations. The historical
  public option name and report counters remain compatible.
- `domain_refinement.max_solver_checks`: actual candidate-feasibility invocations.
  Established Delta coverage is reused without a solver call; a skipped cached
  candidate also consumes no check.
- `domain_discovery.max_solver_checks`: actual discovery invocations, including
  subset probes, full fallbacks, and retries.
- `search.max_bridge_queries`: semantic bridge attempts plus actual non-target
  domain checks. This mixed historical allowance is not a global SMT-call cap.
  `bridge_domain_checks` is a subset of the domain totals, not an additional cost.

All totals remain monotone. Propagation progress does not reset them. Semantic
and discovery retry rules remain distinct. Partial refinement can resume once
per global K/Delta knowledge generation, preserving feasible candidates, proven
exclusions, and the current established Delta coverage. An attempt deliberately yielded
after a proved, premise-unlocking exclusion resumes first after new knowledge.
Otherwise fresh refinements precede retries, and older attempts precede recent ones. Complete domains are not retried;
new samples alone do not reopen a partial refinement. Each continuation spends
the same remaining hard refinement allowance. The refinement policy metadata is
`established-domain-refinement-v7`; the earlier measurement files
remain historical data from before this change.

The [premise-guided refinement planner](finite-domain-refinement.md#cell-selection)
derives critical candidates from product factors and includes them in bounded
exclusion simulations. Predicted target gain guides selection only. A candidate
must still be excluded by an original-context SMT proof before refinement can
yield its partial domain to UCP. Cached planning benefit is reused in the joint
selector; complete enumeration is not required before useful propagation resumes.
The original final-report status conventions are retained: `Analyzed` alone does
not certify that every domain search is complete. Inspect per-cell evidence.

## Invocation Measurement

The opt-in test `privacy_search_invocation_measurements` counts actual successful
solver process starts using test-only instrumentation in `smt_solver/process.rs`.
It includes initial SAT and recovery searches, but excludes independent validation,
which runs after the counter is sampled. No inferred formula such as
`2 * semantic_queries` is used for this comparison.

```sh
PRIVACY_SEARCH_MEASUREMENT_OUTPUT=/tmp/privacy-search-after.tsv \
cargo test --offline -p korrekt --lib privacy_search_invocation_measurements \
  -- --ignored --test-threads=1
```

The before/after comparison uses baseline commit
`a1c49765493b1fda99b9b57c6810bcc2035fbe1e`, with the same measurement harness and
counter applied to both versions. Each of five synthetic circuits is run with
semantic-only, refinement-enabled, discovery-enabled, and combined options.
There is one warmup and three recorded repetitions for each case/profile.
Each invocation has the same 2000 ms limit; semantic retry escalation is disabled.
Semantic/refinement/discovery allowances are 8/32/16 when enabled, respectively.
Fresh validation must accept each produced covering claim.

The original v2 comparison remains recorded as historical evidence. The integrated
v3 scheduler is measured separately with the same harness; historical raw files
must not silently be relabeled as the new version. Results are recorded in
[the comparison summary](unified-private-recovery-measurements.md).
