# UCP Module Layout

Runtime modules stay together in this directory. Regression tests, existing demos,
measurements and upstream fixtures live below `tests/`. The cohesive examples
prepared for the thesis live in the sibling directory `thesis_examples/`.

Optional phase profiling and bounded, analysis-local caches are described in
[UCP performance](../../../../docs/ucp-performance.md). The private engine child
`propagation_cache.rs` reuses expression-local results; `privacy_domain.rs` caches
refinement benefits only while the problem, knowledge and targets are unchanged.
Neither adds inference rules or weakens solver/probe limits.

## Recommended Reading Order

Read the production sections first; leave inline test modules for a second pass.
This is a dependency-based learning order, not the runtime call order.

1. `cell.rs`: cell identities, column kinds, and readable names; no witness values.
2. `expr.rs`: symbolic expression trees and exact/abstract scalar information.
3. `facts.rs`: established uniqueness facts K.
4. `value.rs`: covering domains Delta, exact values, completeness metadata and
   expression evaluation. Its child module `value_inference.rs` contains the
   inference algorithms; read those alongside the corresponding rules.
   Its private descendant `linear_domains.rs` combines linear elimination,
   wrap-aware interval contraction and bounded finite-row support checks.
5. `rules.rs`: expression uniqueness and assignment-style inference.
6. `base_conv.rs`: positional representations, no-wrap conditions, and digit decoding.
7. `bigint_mul.rs`: uniqueness from invertible linear systems over the field.
8. `all_but_one.rs`: the multi-equation all-but-one-zero rule.
9. `lookup.rs`: propagation through finite correlated tuple memberships.
10. `engine.rs`: how rules run together, reach a fixpoint, and filter finite radix candidates.
11. `plonkish.rs`: converting Halo2 expressions, selectors, fixed values, and rotations.
12. `extractor.rs`: assembling the circuit-level `UcpProblem` used by the engine.
    Its child module `lookup_extractor.rs` extracts lookup projections and tuple
    relations; `lookup.rs` propagates through those already extracted relations.
13. `choose_var.rs`: estimating which semantic query could unlock more propagation.
14. `pipeline.rs`: the simpler underconstrainedness UCP/SMT feedback loop.
15. `privacy.rs`: private recovery options, preparation and the main pipeline.
    First read `analyze_private_recoverability` and `recover_private_inputs`;
    revisit the operation adapters after the next four modules. The child module
    `privacy_report.rs` defines the report types, summary and text formatting.
16. `privacy_search.rs`: search generations, retries, action shortlisting and
    selection, stop planning and feasible-sample bookkeeping W.
17. `privacy_domain.rs`: refining an existing covering domain.
18. `privacy_discovery.rs`: collecting samples and proving a new covering domain.
19. `privacy_subset.rs`: selecting literal original constraints for subset proofs.
20. `privacy_validation.rs`: fresh independent checking of reported domain claims.
21. `privacy_observation.rs`: determining whether a claim depends on public observations.
22. `../../io/analyzer_io_type.rs`: public observation inputs and analyzer modes.
23. `../analyzer.rs`: the SMT backend. Focus on context preparation, original query
    snapshots, uniqueness/domain queries, and solver invocation before reading
    the older analysis functions.
24. `../../smt_solver/smt.rs`, `process.rs`, and `smt_parser.rs`: SMT-LIB generation,
    supervised solver execution, and interpretation of SAT/UNSAT/unknown responses.
25. `tests/demos/risk_audit_demo_tests.rs`: follow one concrete end-to-end example
    through the modules above. Then use the other tests as targeted examples.

On a second pass, trace the runtime route: public recovery entry point -> circuit
preparation -> SAT guard -> UCP fixpoint -> action selection -> SMT operation ->
result merge -> renewed propagation or report.

`privacy::analyze_private_recoverability` retains the original SMT SAT guard.
`privacy::analyze_private_recoverability_with_witness` verifies an actual Halo2
witness with the given public observations first and uses SMT as fallback only.
It does not expose witness values to recovery. Reports distinguish `VerifiedWitness`
from `Smt` existence evidence; initial SMT checks are zero on the verified-witness
route. Regression tests for this boundary live in `tests/privacy_witness_tests.rs`.

## Entry Points And Pipelines

| File | Role |
| --- | --- |
| `privacy.rs` | Private recovery entry point, initialization, main recovery loop and SMT operation adapters |
| `privacy_report.rs` | Report types, result summary and text formatting; child of `privacy` |
| `pipeline.rs` | QED-style underconstrainedness pipeline combining UCP and SMT |
| `privacy_search.rs` | Joint cell/action scheduling, retry state and shared feasible samples |
| `privacy_domain.rs` | Refinement of existing finite covering domains |
| `privacy_discovery.rs` | Domain discovery without an initial candidate set |
| `privacy_subset.rs` | Selection of original SMT assertion subsets |
| `privacy_validation.rs` | Independent checking of recovery domain claims |
| `privacy_observation.rs` | Controls for dependence on public observations |

## Extraction And Propagation

`extractor.rs` and `plonkish.rs` translate Halo2 structure into the UCP problem.
The extractor delegates lookup-specific extraction to `lookup_extractor.rs`.
`engine.rs` runs the propagation fixpoint. `rules.rs`, `base_conv.rs`,
`bigint_mul.rs`, `all_but_one.rs` and `lookup.rs` implement inference families;
`choose_var.rs` supplies semantic-query selection. `cell.rs`, `expr.rs`,
`facts.rs` and `value.rs` define the shared representation and knowledge state.
`value_inference.rs` contains concrete-value and domain inference, separate from
the value store and expression evaluation.
`linear_domains.rs` is a private child of value inference: it retains useful
consequences of underdetermined systems without pretending that a local
candidate is a feasible full-circuit witness. See
[the relational inference description](../../../../docs/ucp-relational-propagation.md).

The implementation helpers are private child modules declared with `#[path]` in
their owning modules. Existing public paths such as `value::UcpValueDomain`,
`value::infer_value_domains_from_zero_equation` and `privacy::PrivacyAnalysisReport`
remain available. The main recovery loop, result merge and SMT adapters stay
together in `privacy.rs`; shortlisting and choosing actions stay together in
`privacy_search.rs`. Inline test module names and command-line filters are unchanged.

## Test Sources

```text
thesis_examples/     Connected thesis examples, reference models and measurements
tests/
  *_tests.rs          Recovery, soundness, relational and full-width regressions
  demos/             Synthetic and sample-circuit demonstrations
  measurements/      Timing, invocation-count and ablation measurements
  external/          Adapters and checks for upstream circuits/gadgets
    fixtures/        Unmodified upstream sources, provenance and license
```

The invoice example in `thesis_examples/` audits one shopping cart through its
catalog lines, discounts, rounded tax, shipping and supplier split. Its
[guide](thesis_examples/README.md) separates mathematical reference results from
actual UCP/SMT measurements and lists the run commands.

`mod.rs` uses test-only path attributes to retain the original logical module
names. This preserves sibling imports, test identifiers and command-line filters.
The risk-audit module remains a child of `demo_tests`. Inline unit tests remain
next to the implementation they exercise.

Run solver-backed tests serially because the analyzer currently uses shared SMT
output paths:

```bash
cargo test --offline -p korrekt -- --test-threads=1
cargo test --offline -p korrekt --lib demo_risk_audit -- --nocapture --test-threads=1
```

Long measurements remain opt-in via `--ignored`; moving their files does not
enable them or change their allowances. Production API paths are unchanged.

## Multi-Stage Recovery Demo

`tests/demos/settlement_audit_demo_tests.rs` combines a linear tariff system,
correlated lookup, one-hot allocation, finite catalog domains, an expanded
nonlinear calibration, bit decomposition, copy constraints and a rotated chain.
The standalone UCP fixpoint cannot recover the masked amount; SMT domain
refinement unlocks another UCP phase. No production inference rule is changed
for this fixture. See [the demo guide](../../../../docs/settlement-audit-demo.md)
for constraints, controls, measured quantities and opt-in scaling experiments.

```bash
cargo test --offline -p korrekt --lib settlement_audit_ -- --nocapture --test-threads=1
```
