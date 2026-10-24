//! Original-model checks, finite projection recovery and Delta-to-UCP feedback.
//! SMT tests must run serially because the analyzer uses shared output paths.

use super::{
    cell::CellId,
    privacy::{
        analyze_private_recoverability, prepare_privacy_analysis, PrivacyAnalysisOptions,
        PrivacyAnalysisReport, PrivacyAnalysisStatus, PrivateCellUniqueness, RecoveryLimitation,
    },
    privacy_domain::{
        DomainRefinementState, PrivacyDomainRefinementOptions, PrivateDomainRefinementStatus,
    },
    privacy_validation::{validate_private_recovery_report, RecoveryValidationStatus},
    value::{UcpValueDomain, UcpValueFacts},
};
use crate::{
    circuit_analyzer::{analyzer::SMT_FILE_PATH, halo2_proofs_libs::*},
    io::analyzer_io_type::{AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod},
    smt_solver::smt_parser::Satisfiability,
};
use num_bigint::BigInt;
use std::collections::HashMap;

const K: u32 = 5;

fn field(value: i64) -> Fr {
    if value < 0 {
        -Fr::from(value.unsigned_abs())
    } else {
        Fr::from(value as u64)
    }
}

fn observations(value: i64) -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput::new(HashMap::from([("I-0-0".to_owned(), value)]), 1),
        lookup_method: LookupMethod::InlineConstraints,
    }
}

fn candidates(values: &[i64]) -> UcpValueDomain {
    UcpValueDomain::finite_set(values.iter().copied().map(BigInt::from)).unwrap()
}

fn options(checks: usize) -> PrivacyAnalysisOptions {
    PrivacyAnalysisOptions {
        // Isolate domain refinement: no ordinary uniqueness or bridge queries are allowed.
        max_semantic_queries: 0,
        solver_timeout_ms: Some(2_000),
        domain_refinement: PrivacyDomainRefinementOptions {
            max_solver_checks: checks,
            max_candidates_per_cell: 16,
        },
        ..Default::default()
    }
}

// A public product and a fixed sum narrow a range-checked private input to two roots.
// The expanded quadratic deliberately cannot use the syntactic ROOT rule.
#[derive(Clone)]
pub(super) struct FiniteProjectionCircuit<const NEGATIVE: bool, const WITH_OFFSET: bool = false> {
    secret: Fr,
}

#[derive(Clone)]
pub(super) struct FiniteProjectionConfig {
    secret: Column<Advice>,
    derived: Column<Advice>,
    offset: Option<Column<Advice>>,
    selector: Selector,
    table: TableColumn,
}

impl<const NEGATIVE: bool, const WITH_OFFSET: bool> FiniteProjectionCircuit<NEGATIVE, WITH_OFFSET> {
    pub(super) fn new(secret: i64) -> Self {
        Self {
            secret: field(secret),
        }
    }
}

impl<const NEGATIVE: bool, const WITH_OFFSET: bool> Circuit<Fr>
    for FiniteProjectionCircuit<NEGATIVE, WITH_OFFSET>
{
    type Config = FiniteProjectionConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(0)
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let secret = meta.advice_column();
        let derived = meta.advice_column();
        let offset = WITH_OFFSET.then(|| meta.advice_column());
        let public = meta.instance_column();
        let selector = meta.complex_selector();
        let table = meta.lookup_table_column();
        meta.lookup(|meta| {
            let q = meta.query_selector(selector);
            let s = meta.query_advice(secret, Rotation::cur());
            vec![(q * s, table)]
        });
        meta.create_gate("public product with fixed sum", |meta| {
            let q = meta.query_selector(selector);
            let s = meta.query_advice(secret, Rotation::cur());
            let d = meta.query_advice(derived, Rotation::cur());
            let product = meta.query_instance(public, Rotation::cur());
            let offset_expr = offset.map(|column| meta.query_advice(column, Rotation::cur()));
            let dependent = if let Some(offset) = &offset_expr {
                d - s.clone() - offset.clone()
            } else {
                d * (s.clone() - Expression::Constant(Fr::from(5)))
            };
            let mut constraints = vec![
                q.clone()
                    * (s.clone() * s.clone() - Expression::Constant(Fr::from(10)) * s.clone()
                        + product),
                // Initially s may be 5. Once SMT proves s in {3,7}, s-5 is nonzero, so UCP learns d=0.
                q.clone() * dependent,
            ];
            if let Some(offset) = offset_expr {
                constraints.push(q * offset.clone() * (offset - Expression::Constant(Fr::from(1))));
            }
            constraints
        });
        FiniteProjectionConfig {
            secret,
            derived,
            offset,
            selector,
            table,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "sixteen candidate inputs",
            |mut table| {
                for row in 0..16 {
                    let value = row as i64 - i64::from(NEGATIVE);
                    table.assign_cell(
                        || "candidate",
                        config.table,
                        row,
                        || Value::known(field(value)),
                    )?;
                }
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "private input and derived cell",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                region.assign_advice(
                    || "secret",
                    config.secret,
                    0,
                    || Value::known(self.secret),
                )?;
                region.assign_advice(
                    || "derived",
                    config.derived,
                    0,
                    || {
                        Value::known(if WITH_OFFSET {
                            self.secret
                        } else {
                            Fr::from(0)
                        })
                    },
                )?;
                if let Some(offset) = config.offset {
                    region.assign_advice(
                        || "boolean offset",
                        offset,
                        0,
                        || Value::known(Fr::from(0)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

pub(super) fn finite_projection_demo_options() -> PrivacyAnalysisOptions {
    options(17)
}

pub(super) fn finite_projection_demo_input() -> AnalyzerInput {
    observations(21)
}

pub(super) fn finite_projection_demo_targets() -> [CellId; 2] {
    [CellId::advice(0, 0), CellId::advice(1, 0)]
}

fn analyze<const NEGATIVE: bool>(
    secret: i64,
    product: i64,
    checks: usize,
) -> PrivacyAnalysisReport {
    let circuit = FiniteProjectionCircuit::<NEGATIVE>::new(secret);
    MockProver::run(K, &circuit, vec![vec![field(product)]])
        .unwrap()
        .assert_satisfied();
    analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &observations(product),
        finite_projection_demo_targets(),
        options(checks),
    )
    .unwrap()
}

#[test]
fn finite_projection_recovers_two_values_then_ucp_recovers_a_different_cell() {
    let coarse = analyze::<false>(3, 21, 0);
    assert_eq!(
        coarse.cells[0].domain,
        UcpValueDomain::finite_set((0..16).map(BigInt::from))
    );
    assert_eq!(coarse.cells[1].domain, None);
    assert_eq!(coarse.status, PrivacyAnalysisStatus::QueryLimitReached);
    let report = analyze::<false>(3, 21, 17);
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.cells[0].domain, Some(candidates(&[3, 7])));
    assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
    assert_eq!(report.cells[1].domain, Some(candidates(&[0])));
    assert_eq!(report.cells[1].uniqueness, PrivateCellUniqueness::Unique);
    assert_eq!(
        report.cells[0].domain_refinement.as_ref().unwrap().status,
        PrivateDomainRefinementStatus::Complete
    );
    assert!(report.cells[1].domain_refinement.is_none()); // Derived by UCP, not an SMT cell query.
    assert_eq!(report.semantic_queries, 0);
    assert_eq!(report.search_statistics.unqueried_targets, 0);
    assert_eq!(report.domain_refinement_statistics.solver_checks, 17);
    assert_eq!(report.domain_refinement_statistics.removed_candidates, 14);
    assert_eq!(report.domain_refinement_statistics.complete_domains, 1);
    assert_eq!(report.search_statistics.propagation_runs, 2);
    // The refinement and its UCP consequences arrive in the same next fixed-point round.
    assert!(report.search_statistics.progress_rounds >= 1);
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(
            &FiniteProjectionCircuit::<false>::new(3),
            K,
            &observations(21),
            &report
        )
        .unwrap()
        .status,
        RecoveryValidationStatus::VerifiedDomains
    );
    // This run really uses the other valid witness; both runs recover the same public-dependent set.
    assert_eq!(
        analyze::<false>(7, 21, 17).cells[0].domain,
        report.cells[0].domain
    );
}

#[test]
fn partial_refinement_preserves_unchecked_values_and_reports_its_cost() {
    let report = analyze::<false>(3, 21, 4); // Coverage + rejection of 0,1,2; all other values remain.
    assert_eq!(
        report.cells[0].domain,
        UcpValueDomain::finite_set((3..16).map(BigInt::from))
    );
    assert_eq!(report.cells[1].domain, None);
    let evidence = report.cells[0].domain_refinement.as_ref().unwrap();
    assert_eq!(evidence.status, PrivateDomainRefinementStatus::Partial);
    assert_eq!(evidence.feasible_candidates, 0);
    assert_eq!(evidence.unresolved_candidates, 13);
    assert_eq!(evidence.limitation, Some(RecoveryLimitation::QueryLimit));
    assert_eq!(report.domain_refinement_statistics.solver_checks, 4);
    assert!(report.domain_refinement_statistics.budget_exhausted);
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(
            &FiniteProjectionCircuit::<false>::new(3),
            K,
            &observations(21),
            &report
        )
        .unwrap()
        .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

#[test]
fn projections_use_the_actual_public_observation_and_signed_field_representatives() {
    assert_eq!(
        analyze::<false>(2, 16, 17).cells[0].domain,
        Some(candidates(&[2, 8]))
    );
    let negative = analyze::<true>(-1, -11, 17);
    assert_eq!(negative.cells[0].domain, Some(candidates(&[-1, 11])));
    assert_eq!(negative.cells[1].domain, Some(candidates(&[0])));
    assert_eq!(
        negative.cells[0].domain_refinement.as_ref().unwrap().status,
        PrivateDomainRefinementStatus::Complete
    );
}

#[test]
fn a_newly_small_domain_is_refined_in_the_next_ucp_round_under_the_same_total_cap() {
    let circuit = FiniteProjectionCircuit::<false, true>::new(3);
    MockProver::run(K, &circuit, vec![vec![Fr::from(21)]])
        .unwrap()
        .assert_satisfied();
    for checks in [18, 22] {
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            K,
            &observations(21),
            finite_projection_demo_targets(),
            options(checks),
        )
        .unwrap();
        assert_eq!(report.cells[0].domain, Some(candidates(&[3, 7])));
        let complete = checks == 22;
        // d=s+offset starts with 17 candidates, above the configured per-cell cap of 16.
        // Refining s makes d eligible; these four values still need feasibility checks.
        assert_eq!(report.cells[1].domain, Some(candidates(&[3, 4, 7, 8])));
        assert_eq!(report.domain_refinement_statistics.solver_checks, checks);
        assert_eq!(report.domain_refinement_statistics.attempted_cells, 2);
        assert_eq!(report.search_statistics.propagation_runs, 2);
        assert_eq!(
            report.cells[1].domain_refinement.as_ref().unwrap().status,
            if complete {
                PrivateDomainRefinementStatus::Complete
            } else {
                PrivateDomainRefinementStatus::Partial
            }
        );
        if complete {
            assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
            assert_eq!(report.summary.non_unique_cells, 2);
            assert_eq!(
                validate_private_recovery_report::<Fr, _>(&circuit, K, &observations(21), &report)
                    .unwrap()
                    .status,
                RecoveryValidationStatus::VerifiedDomains
            );
        } else {
            assert!(report.domain_refinement_statistics.budget_exhausted);
        }
    }
}

#[test]
fn finite_refinement_can_recover_an_exact_private_input_then_propagate_it() {
    // The other quadratic root is -1, outside this circuit's nonnegative lookup table.
    let report = analyze::<false>(11, -11, 17);
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.cells[0].domain, Some(candidates(&[11])));
    assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
    assert_eq!(report.cells[1].domain, Some(candidates(&[0])));
    assert_eq!(report.summary.exact_values, 2);
    assert_eq!(report.search_statistics.propagation_runs, 2);
    assert_eq!(
        report.cells[0].domain_refinement.as_ref().unwrap().status,
        PrivateDomainRefinementStatus::Complete
    );
    assert_eq!(report.semantic_queries, 0);
}

#[test]
fn original_snapshot_is_not_strengthened_by_later_inferred_assertions_or_other_candidates() {
    let mut context = prepare_privacy_analysis::<Fr, _, _>(
        &FiniteProjectionCircuit::<false>::new(3),
        K,
        &observations(21),
        finite_projection_demo_targets(),
    )
    .unwrap();
    assert_eq!(
        context
            .analyzer
            .check_ucp_satisfiability(&context.analyzer_input)
            .unwrap(),
        Satisfiability::Satisfiable
    );
    let original = context
        .analyzer
        .original_private_query_context(&context.analyzer_input, &context.private_cells)
        .unwrap();
    let secret = &context.private_cells[0];
    let mut untrusted_hint = UcpValueFacts::new();
    untrusted_hint.mark_known(secret.clone(), 3.into());
    context.analyzer.set_ucp_value_facts(&untrusted_hint);
    context
        .analyzer
        .query_ucp_cell_uniqueness_with_value(&context.analyzer_input, secret)
        .unwrap();
    let before = std::fs::read_to_string(&*SMT_FILE_PATH).unwrap();
    for (value, expected) in [
        (3, Satisfiability::Satisfiable),
        (7, Satisfiability::Satisfiable),
        (4, Satisfiability::Unsatisfiable),
        (7, Satisfiability::Satisfiable),
    ] {
        assert_eq!(
            original
                .check_membership::<Fr>(secret, &candidates(&[value]), false, Some(2_000))
                .unwrap(),
            expected
        );
    }
    assert_eq!(std::fs::read_to_string(&*SMT_FILE_PATH).unwrap(), before);
    context.analyzer.set_ucp_value_facts(&UcpValueFacts::new());
    context.analyzer.set_ucp_unique_cells([]);
    // Clearing the exports cannot make an already strengthened file original again.
    assert!(context
        .analyzer
        .original_private_query_context(&context.analyzer_input, &context.private_cells)
        .is_err());
    assert!(context
        .analyzer
        .query_private_domain_entailment_after_sat(
            &context.analyzer_input,
            secret,
            &candidates(&[3])
        )
        .is_err());
}

#[test]
fn a_forged_covering_domain_is_rejected_without_circular_candidate_assumptions() {
    let mut context = prepare_privacy_analysis::<Fr, _, _>(
        &FiniteProjectionCircuit::<false>::new(3),
        K,
        &observations(21),
        finite_projection_demo_targets(),
    )
    .unwrap();
    let original = context
        .analyzer
        .original_private_query_context(&context.analyzer_input, &context.private_cells)
        .unwrap();
    let secret = context.private_cells[0].clone();
    let mut values = UcpValueFacts::new();
    values.mark_domain(secret.clone(), candidates(&[3, 4])); // Feasible 7 is deliberately omitted.
    let mut state = DomainRefinementState::new(options(3).domain_refinement);
    let result = state.refine_next(
        &[secret],
        &context.problem,
        &context
            .problem
            .analyze_with_values(context.problem.initial_facts.clone(), values),
        |cell, domain, exclude| original.check_membership::<Fr>(cell, domain, exclude, Some(2_000)),
    );
    assert!(result.unwrap_err().to_string().contains("does not cover"));
}

#[derive(Clone)]
struct RefinementPriorityCircuit;

impl Circuit<Fr> for RefinementPriorityCircuit {
    type Config = ([Column<Advice>; 3], Selector);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let columns = std::array::from_fn(|_| meta.advice_column());
        let selector = meta.selector();
        meta.create_gate("refinement priority", |meta| {
            let idle = meta.query_advice(columns[0], Rotation::cur());
            let secret = meta.query_advice(columns[1], Rotation::cur());
            let derived = meta.query_advice(columns[2], Rotation::cur());
            let q = meta.query_selector(selector);
            let constant = |value| Expression::Constant(Fr::from(value));
            let roots = |value: Expression<Fr>, roots: &[u64]| {
                roots.iter().fold(constant(1), |product, root| {
                    product * (value.clone() - constant(*root))
                })
            };
            vec![
                q.clone() * roots(idle, &[0, 1, 2]),
                q.clone() * roots(secret.clone(), &[3, 5, 7]),
                q.clone()
                    * (secret.clone() * secret.clone() - constant(10) * secret.clone()
                        + constant(21)),
                q * derived * (secret - constant(5)),
            ]
        });
        (columns, selector)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "refinement candidates",
            |mut region| {
                config.1.enable(&mut region, 0)?;
                for (column, value) in config.0.iter().zip([0, 3, 0]) {
                    region.assign_advice(
                        || "private value",
                        *column,
                        0,
                        || Value::known(Fr::from(value)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

#[test]
fn refinement_priority_recovers_a_dependent_cell_before_spending_the_budget_on_an_idle_cell() {
    let circuit = RefinementPriorityCircuit;
    MockProver::run(K, &circuit, vec![])
        .unwrap()
        .assert_satisfied();
    let input = AnalyzerInput {
        verification_method: VerificationMethod::None,
        verification_input: VerificationInput {
            instance_cells: HashMap::new(),
            iterations: 1,
        },
        lookup_method: LookupMethod::InlineConstraints,
    };
    let targets = [
        CellId::advice(0, 0),
        CellId::advice(1, 0),
        CellId::advice(2, 0),
    ];
    let report =
        analyze_private_recoverability::<Fr, _, _>(&circuit, K, &input, targets, options(4))
            .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::QueryLimitReached);
    assert_eq!(report.domain_refinement_statistics.solver_checks, 4);
    assert_eq!(report.domain_refinement_statistics.attempted_cells, 1);
    assert_eq!(report.semantic_queries, 0);
    assert_eq!(report.search_statistics.propagation_runs, 2);
    assert_eq!(report.cells[0].domain, Some(candidates(&[0, 1, 2])));
    assert!(report.cells[0].domain_refinement.is_none());
    assert_eq!(
        report.cells[1].baseline_domain,
        Some(candidates(&[3, 5, 7]))
    );
    assert_eq!(report.cells[1].domain, Some(candidates(&[3, 7])));
    assert!(report.cells[1].domain_refinement.is_some());
    assert_eq!(report.cells[2].baseline_domain, None);
    assert_eq!(report.cells[2].domain, Some(candidates(&[0])));
    assert!(report.cells[2].domain_refinement.is_none());
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &input, &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

#[test]
fn finite_target_uses_an_internal_probe_with_or_without_candidate_search() {
    let circuit = FiniteProjectionCircuit::<false>::new(11);
    for checks in [0, 32] {
        let mut options = options(checks);
        options.max_semantic_queries = 1;
        options.search.max_bridge_queries = 0;
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            K,
            &observations(-11),
            [CellId::advice(0, 0)],
            options,
        )
        .unwrap();
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.cells[0].domain, Some(candidates(&[11])));
        assert_eq!(report.semantic_queries, 1);
        assert_eq!(report.domain_refinement_statistics.solver_checks, 0);
        assert_eq!(report.domain_discovery_statistics.solver_checks, 0);
        assert_eq!(report.cells[0].query_attempts, 1);
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, K, &observations(-11), &report)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
    }
}

#[test]
fn shared_semantic_samples_save_two_refinement_solver_invocations() {
    let circuit = FiniteProjectionCircuit::<false>::new(3);
    let mut options = options(17);
    options.max_semantic_queries = 1;
    options.search.max_bridge_queries = 0;
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &observations(21),
        [CellId::advice(0, 0)],
        options,
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.cells[0].domain, Some(candidates(&[3, 7])));
    assert_eq!(report.semantic_queries, 1);
    assert_eq!(report.domain_refinement_statistics.solver_checks, 15);
    assert_eq!(
        report.cells[0]
            .domain_refinement
            .as_ref()
            .unwrap()
            .feasible_candidates,
        2
    );
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &observations(21), &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

#[test]
fn domain_refinement_can_use_a_non_target_bridge_without_exceeding_its_allowance() {
    let circuit = RefinementPriorityCircuit;
    let input = AnalyzerInput {
        verification_method: VerificationMethod::None,
        verification_input: VerificationInput {
            instance_cells: HashMap::new(),
            iterations: 1,
        },
        lookup_method: LookupMethod::InlineConstraints,
    };
    for allowance in [3, 4] {
        let mut options = options(4);
        options.search.max_bridge_queries = allowance;
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            K,
            &input,
            [CellId::advice(2, 0)],
            options,
        )
        .unwrap();
        assert_eq!(report.semantic_queries, 0);
        assert!(report.search_statistics.bridge_domain_checks <= allowance);
        if allowance == 4 {
            assert_eq!(report.cells[0].domain, Some(candidates(&[0])));
            assert_eq!(report.search_statistics.bridge_domain_checks, 4);
            assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
            assert_eq!(
                validate_private_recovery_report::<Fr, _>(&circuit, K, &input, &report)
                    .unwrap()
                    .status,
                RecoveryValidationStatus::VerifiedDomains
            );
        } else {
            assert!(report.cells[0].domain.is_none());
            assert_eq!(report.domain_refinement_statistics.solver_checks, 0);
        }
    }
}

#[test]
fn inconsistent_original_context_never_reports_a_finite_projection() {
    let report = analyze_private_recoverability::<Fr, _, _>(
        &FiniteProjectionCircuit::<false>::new(3),
        K,
        &observations(100),
        finite_projection_demo_targets(),
        options(17),
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::Inconsistent);
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.domain.is_none() && cell.domain_refinement.is_none()));
    assert_eq!(report.domain_refinement_statistics.solver_checks, 0);
}

#[test]
fn invalid_refinement_options_are_rejected_before_synthesis() {
    for max_candidates in [0, 1, 257] {
        let mut options = options(1);
        options.domain_refinement.max_candidates_per_cell = max_candidates;
        let error = analyze_private_recoverability::<Fr, _, _>(
            &FiniteProjectionCircuit::<false>::new(3),
            K,
            &observations(21),
            finite_projection_demo_targets(),
            options,
        )
        .unwrap_err();
        assert!(error.to_string().contains("candidates per cell"));
    }
}

// A correlated table: public class=0 permits secrets 0 or 1, class=1 permits 2 or 3.
// Per-column UCP projections alone cannot filter the table using the observed class.
#[derive(Clone)]
struct CorrelatedLookupCircuit;

#[derive(Clone)]
struct CorrelatedLookupConfig {
    advice: [Column<Advice>; 2],
    table: [TableColumn; 2],
    selector: Selector,
}

impl Circuit<Fr> for CorrelatedLookupCircuit {
    type Config = CorrelatedLookupConfig;
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        self.clone()
    }
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column()];
        let table = [meta.lookup_table_column(), meta.lookup_table_column()];
        let selector = meta.complex_selector();
        let public = meta.instance_column();
        meta.lookup(|meta| {
            let q = meta.query_selector(selector);
            advice
                .iter()
                .zip(table.iter())
                .map(|(column, table)| {
                    (
                        q.clone() * meta.query_advice(*column, Rotation::cur()),
                        *table,
                    )
                })
                .collect::<Vec<_>>()
        });
        meta.create_gate("observed class", |meta| {
            vec![
                meta.query_selector(selector)
                    * (meta.query_advice(advice[1], Rotation::cur())
                        - meta.query_instance(public, Rotation::cur())),
            ]
        });
        CorrelatedLookupConfig {
            advice,
            table,
            selector,
        }
    }
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "correlated classes",
            |mut table| {
                for row in 0..4 {
                    for (index, value) in [row, row / 2].into_iter().enumerate() {
                        table.assign_cell(
                            || "table entry",
                            config.table[index],
                            row,
                            || Value::known(Fr::from(value as u64)),
                        )?;
                    }
                }
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "classified secret",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                for column in config.advice {
                    region.assign_advice(
                        || "private value",
                        column,
                        0,
                        || Value::known(Fr::from(0)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

#[test]
fn finite_refinement_preserves_full_lookup_tuple_correlations() {
    let circuit = CorrelatedLookupCircuit;
    MockProver::run(K, &circuit, vec![vec![Fr::from(0)]])
        .unwrap()
        .assert_satisfied();
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &observations(0),
        finite_projection_demo_targets(),
        options(5),
    )
    .unwrap();
    assert_eq!(
        report.cells[0].baseline_domain,
        Some(candidates(&[0, 1, 2, 3]))
    );
    assert_eq!(report.cells[0].domain, Some(candidates(&[0, 1])));
    assert_eq!(
        report.cells[0].domain_refinement.as_ref().unwrap().status,
        PrivateDomainRefinementStatus::Complete
    );
    assert_eq!(report.cells[1].domain, Some(candidates(&[0])));
    assert_eq!(report.domain_refinement_statistics.solver_checks, 5);
}
