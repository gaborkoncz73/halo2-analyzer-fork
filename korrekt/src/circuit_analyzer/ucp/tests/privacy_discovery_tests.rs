//! Domain discovery with no lookup/range seed, plus original-context isolation.
//! Run SMT tests serially: the analyzer uses shared output paths.

use super::{
    cell::CellId,
    privacy::{
        analyze_private_recoverability, prepare_privacy_analysis,
        prepare_privacy_analysis_with_capture, PrivacyAnalysisOptions, PrivacyAnalysisReport,
        PrivacyAnalysisStatus, PrivateCellUniqueness, RecoveryLimitation,
    },
    privacy_discovery::{PrivacyDomainDiscoveryOptions, PrivateDomainDiscoveryStatus},
    privacy_validation::{validate_private_recovery_report, RecoveryValidationStatus},
    value::{UcpValueDomain, UcpValueFacts},
};
use crate::smt_solver::smt_parser::Satisfiability;
use crate::{
    circuit_analyzer::{analyzer::SMT_FILE_PATH, halo2_proofs_libs::*},
    io::analyzer_io_type::{AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod},
};
use num_bigint::BigInt;
use std::collections::{BTreeSet, HashMap};

const K: u32 = 4;
pub(super) const TWO_ROOTS: u8 = 0;
pub(super) const UNIQUE: u8 = 1;
const FREE_SUM: u8 = 2;
pub(super) const INCONSISTENT: u8 = 3;
const UNIQUE_WITH_FREE_WITNESS: u8 = 4;
pub(super) const COPIED_CONSTANT: u8 = 5;
const WIDE_ROOTS: u8 = 6;
const BOOLEAN: u8 = 7;
const WITH_BOOLEAN_OFFSET: u8 = 8;
pub(super) const FREE_FIRST_RECOVERABLE_CHAIN: u8 = 9;
const LOOKUP_PINNED_ROOT: u8 = 10;

// Two expanded roots over the whole field; no range check supplies a candidate list.
// A dependent product becomes useful only after discovery excludes secret=5.
#[derive(Clone)]
pub(super) struct UnboundedProjectionCircuit<const CASE: u8> {
    secret: Fr,
    dependent: Fr,
}

impl<const CASE: u8> UnboundedProjectionCircuit<CASE> {
    pub(super) fn new(secret: Fr, dependent: Fr) -> Self {
        Self { secret, dependent }
    }
}

#[derive(Clone)]
pub(super) struct ProjectionConfig {
    secret: Column<Advice>,
    dependent: Column<Advice>,
    offset: Option<Column<Advice>>,
    selector: Selector,
    lookup_table: Option<TableColumn>,
}

impl<const CASE: u8> Circuit<Fr> for UnboundedProjectionCircuit<CASE> {
    type Config = ProjectionConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(Fr::from(0), Fr::from(0))
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let secret = meta.advice_column();
        let dependent = meta.advice_column();
        let offset = matches!(CASE, WITH_BOOLEAN_OFFSET | FREE_FIRST_RECOVERABLE_CHAIN)
            .then(|| meta.advice_column());
        let selector = if CASE == LOOKUP_PINNED_ROOT {
            meta.complex_selector()
        } else {
            meta.selector()
        };
        let public = meta.instance_column();
        let lookup_table = (CASE == LOOKUP_PINNED_ROOT).then(|| {
            let table = meta.lookup_table_column();
            meta.lookup(|meta| {
                let q = meta.query_selector(selector);
                let s = meta.query_advice(secret, Rotation::cur());
                // Disabled rows use the same legal table value, not an unconstrained tuple.
                vec![(
                    q * (s - Expression::Constant(Fr::from(3))) + Expression::Constant(Fr::from(3)),
                    table,
                )]
            });
            table
        });
        if CASE == COPIED_CONSTANT {
            let fixed = meta.fixed_column();
            meta.enable_constant(fixed);
            meta.enable_equality(secret);
        }
        meta.create_gate("projection without a candidate seed", |meta| {
            let s = meta.query_advice(secret, Rotation::cur());
            let d = meta.query_advice(dependent, Rotation::cur());
            let q = meta.query_selector(selector);
            let p = meta.query_instance(public, Rotation::cur());
            let constant = |value| Expression::Constant(Fr::from(value));
            let square_root = s.clone() * s.clone() - constant(2) * s.clone() + constant(1);
            let equations = match CASE {
                TWO_ROOTS | LOOKUP_PINNED_ROOT => vec![
                    s.clone() * s.clone() - constant(10) * s.clone() + p,
                    d * (s - constant(5)),
                ],
                UNIQUE => vec![square_root, d - s - constant(2)],
                FREE_SUM => vec![s + d - p],
                INCONSISTENT => vec![s.clone(), s - constant(1)],
                UNIQUE_WITH_FREE_WITNESS => vec![square_root],
                COPIED_CONSTANT => vec![s - d],
                WIDE_ROOTS => vec![s.clone() * s.clone() - p, d * (s - constant(5))],
                BOOLEAN => vec![s.clone() * (s - constant(1))],
                WITH_BOOLEAN_OFFSET => {
                    let b = meta.query_advice(offset.unwrap(), Rotation::cur());
                    vec![
                        s.clone() * s.clone() - constant(10) * s.clone() + p,
                        d - s - b.clone(),
                        b.clone() * (b - constant(1)),
                    ]
                }
                FREE_FIRST_RECOVERABLE_CHAIN => {
                    let next = meta.query_advice(offset.unwrap(), Rotation::cur());
                    // The first advice cell is free. The later private chain equals p, then p+2.
                    vec![
                        d.clone() * d.clone() - constant(2) * p.clone() * d.clone() + p.clone() * p,
                        next - d - constant(2),
                    ]
                }
                _ => unreachable!(),
            };
            equations
                .into_iter()
                .map(|expr| q.clone() * expr)
                .collect::<Vec<_>>()
        });
        ProjectionConfig {
            secret,
            dependent,
            offset,
            selector,
            lookup_table,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        if let Some(table) = config.lookup_table {
            layouter.assign_table(
                || "one allowed root",
                |mut region| {
                    region.assign_cell(|| "root three", table, 0, || Value::known(Fr::from(3)))
                },
            )?;
        }
        layouter.assign_region(
            || "unbounded private input",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                let secret = region.assign_advice(
                    || "secret",
                    config.secret,
                    0,
                    || Value::known(self.secret),
                )?;
                region.assign_advice(
                    || "dependent",
                    config.dependent,
                    0,
                    || Value::known(self.dependent),
                )?;
                if CASE == COPIED_CONSTANT {
                    region.constrain_constant(secret.cell(), Fr::from(7))?;
                }
                if let Some(offset) = config.offset {
                    region.assign_advice(
                        || "boolean offset",
                        offset,
                        0,
                        || {
                            Value::known(if CASE == FREE_FIRST_RECOVERABLE_CHAIN {
                                self.dependent + Fr::from(2)
                            } else {
                                Fr::from(0)
                            })
                        },
                    )?;
                }
                Ok(())
            },
        )
    }
}

pub(super) fn discovery_demo_input() -> AnalyzerInput {
    observations(21.into())
}

fn observations(value: BigInt) -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput::new(HashMap::from([("I-0-0".to_owned(), value)]), 1),
        lookup_method: LookupMethod::InlineConstraints,
    }
}

pub(super) fn discovery_demo_targets() -> [CellId; 2] {
    [CellId::advice(0, 0), CellId::advice(1, 0)]
}

pub(super) fn discovery_demo_options() -> PrivacyAnalysisOptions {
    options(3, 2)
}

fn options(checks: usize, values: usize) -> PrivacyAnalysisOptions {
    PrivacyAnalysisOptions {
        max_semantic_queries: 0,
        solver_timeout_ms: Some(2_000),
        domain_discovery: PrivacyDomainDiscoveryOptions {
            max_solver_checks: checks,
            max_values_per_cell: values,
            // This fixture focuses on the three-check root-to-UCP handoff, not fair scheduling.
            max_checks_per_round: 3,
            ..Default::default()
        },
        ..PrivacyAnalysisOptions::fast_probe_only()
    }
}

fn subset_options(checks: usize, values: usize) -> PrivacyAnalysisOptions {
    let mut options = options(checks, values);
    options.domain_discovery.use_targeted_subsets = true;
    options.domain_discovery.max_checks_per_round = checks.max(1);
    options
}

#[test]
fn targeted_singleton_exclusion_recovers_and_feeds_ucp_using_one_full_check() {
    let circuit = UnboundedProjectionCircuit::<UNIQUE>::new(Fr::from(1), Fr::from(3));
    let input = discovery_demo_input();
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &input,
        discovery_demo_targets(),
        subset_options(2, 1),
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed, "{report}");
    assert_eq!(report.cells[0].domain, Some(domain(&[1])));
    assert_eq!(report.cells[1].domain, Some(domain(&[3])));
    let stats = &report.domain_discovery_statistics;
    assert_eq!(stats.solver_checks, 2);
    assert_eq!(stats.full_solver_checks, 1);
    assert_eq!(stats.subset_solver_checks, 1);
    assert_eq!(stats.subset_unsat_proofs, 1);
    assert_eq!(stats.subset_fallbacks, 0);
    assert_eq!(report.semantic_queries, 0);
    assert!(report.cells[1].domain_discovery.is_none());
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &input, &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

#[test]
fn targeted_two_root_search_counts_every_subset_probe_and_full_fallback() {
    let circuit = UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0));
    let input = discovery_demo_input();
    for checks in [2, 3, 4] {
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            K,
            &input,
            discovery_demo_targets(),
            subset_options(checks, 2),
        )
        .unwrap();
        let evidence = report.cells[0].domain_discovery.as_ref().unwrap();
        let stats = &report.domain_discovery_statistics;
        assert_eq!(stats.solver_checks, checks);
        assert_eq!(stats.full_solver_checks, if checks == 2 { 1 } else { 2 });
        assert_eq!(stats.subset_fallbacks, 1);
        assert_eq!(stats.models_found, if checks == 2 { 1 } else { 2 });
        assert_eq!(
            stats.full_solver_checks + stats.subset_solver_checks,
            checks
        );
        if checks < 4 {
            assert_eq!(evidence.status, PrivateDomainDiscoveryStatus::Partial);
            assert!(report.cells.iter().all(|cell| cell.domain.is_none()));
            assert_eq!(evidence.limitation, Some(RecoveryLimitation::QueryLimit));
        } else {
            assert_eq!(evidence.status, PrivateDomainDiscoveryStatus::Complete);
            assert_eq!(report.cells[0].domain, Some(domain(&[3, 7])));
            assert_eq!(report.cells[1].domain, Some(domain(&[0])));
            assert_eq!(stats.subset_unsat_proofs, 1);
            assert_eq!(
                validate_private_recovery_report::<Fr, _>(&circuit, K, &input, &report)
                    .unwrap()
                    .status,
                RecoveryValidationStatus::VerifiedDomains
            );
        }
    }
}

#[test]
fn targeted_snapshots_are_original_and_exclusions_do_not_accumulate() {
    let circuit = UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0));
    let input = discovery_demo_input();
    let mut context = prepare_privacy_analysis_with_capture::<Fr, _, _>(
        &circuit,
        K,
        &input,
        discovery_demo_targets(),
        true,
    )
    .unwrap();
    assert_eq!(
        context.analyzer.check_ucp_satisfiability(&input).unwrap(),
        Satisfiability::Satisfiable
    );
    let original = context
        .analyzer
        .original_private_query_context(&input, &context.private_cells)
        .unwrap();
    let secret = &context.private_cells[0];
    let dependent = &context.private_cells[1];
    assert!(original.has_targeted_subset(secret));
    assert_eq!(
        original
            .check_unseen_subset::<Fr>(secret, &BTreeSet::from([3.into()]), Some(2_000))
            .unwrap(),
        Satisfiability::Satisfiable
    );
    assert_eq!(
        original
            .check_unseen_subset::<Fr>(secret, &BTreeSet::from([3.into(), 7.into()]), Some(2_000))
            .unwrap(),
        Satisfiability::Unsatisfiable
    );
    assert_eq!(
        original
            .check_unseen_subset::<Fr>(secret, &BTreeSet::new(), Some(2_000))
            .unwrap(),
        Satisfiability::Satisfiable
    );
    let mut wrong = UcpValueFacts::new();
    wrong.mark_known(secret.clone(), 9.into());
    context.analyzer.set_ucp_value_facts(&wrong);
    assert_eq!(
        context.analyzer.check_ucp_satisfiability(&input).unwrap(),
        Satisfiability::Unsatisfiable
    );
    assert_eq!(
        original
            .check_unseen_subset::<Fr>(secret, &BTreeSet::new(), Some(2_000))
            .unwrap(),
        Satisfiability::Satisfiable
    );
    assert!(original
        .query_unseen_value::<Fr>(secret, &BTreeSet::new(), Some(2_000))
        .unwrap()
        .is_some());
    assert_eq!(
        original
            .check_unseen_subset::<Fr>(dependent, &BTreeSet::from([0.into()]), Some(2_000))
            .unwrap(),
        Satisfiability::Unsatisfiable
    );
}

#[test]
fn a_missing_targeted_subset_uses_full_checks_without_a_phantom_probe() {
    let circuit =
        UnboundedProjectionCircuit::<UNIQUE_WITH_FREE_WITNESS>::new(Fr::from(1), Fr::from(9));
    let input = discovery_demo_input();
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &input,
        [CellId::advice(1, 0)],
        subset_options(3, 2),
    )
    .unwrap();
    let stats = &report.domain_discovery_statistics;
    assert_eq!(stats.solver_checks, 3);
    assert_eq!(stats.full_solver_checks, 3);
    assert_eq!(stats.subset_solver_checks, 0);
    assert!(report.cells[0].domain.is_none());
    assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
}

#[test]
fn targeted_search_cannot_turn_an_inconsistent_original_model_into_recovery() {
    let circuit = UnboundedProjectionCircuit::<INCONSISTENT>::new(Fr::from(0), Fr::from(0));
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &discovery_demo_input(),
        discovery_demo_targets(),
        subset_options(4, 2),
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::Inconsistent);
    assert_eq!(report.domain_discovery_statistics.solver_checks, 0);
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.domain.is_none() && cell.domain_discovery.is_none()));
}

#[test]
fn a_subset_sat_value_can_be_infeasible_in_the_original_lookup_context() {
    let circuit = UnboundedProjectionCircuit::<LOOKUP_PINNED_ROOT>::new(Fr::from(3), Fr::from(0));
    check_witness(&circuit, Fr::from(21));
    let input = discovery_demo_input();
    let mut context = prepare_privacy_analysis_with_capture::<Fr, _, _>(
        &circuit,
        K,
        &input,
        discovery_demo_targets(),
        true,
    )
    .unwrap();
    assert_eq!(
        context.analyzer.check_ucp_satisfiability(&input).unwrap(),
        Satisfiability::Satisfiable
    );
    let original = context
        .analyzer
        .original_private_query_context(&input, &context.private_cells)
        .unwrap();
    let secret = &context.private_cells[0];
    let blocked = BTreeSet::from([3.into()]);
    // Original gates allow 7, but the original inline lookup forbids it.
    assert_eq!(
        original
            .check_unseen_subset::<Fr>(secret, &blocked, Some(2_000))
            .unwrap(),
        Satisfiability::Satisfiable
    );
    assert!(original
        .query_unseen_value::<Fr>(secret, &blocked, Some(2_000))
        .unwrap()
        .is_none());
    assert_eq!(
        original
            .query_unseen_value::<Fr>(secret, &BTreeSet::new(), Some(2_000))
            .unwrap(),
        Some(3.into())
    );
}

// A small relevant component sits beside many nonlinear gates sharing the same public amount.
// Their private values remain ambiguous; they must not be pulled in merely through that public cell.
#[derive(Clone)]
pub(super) struct LocalizedRecoveryCircuit<const NOISE: usize> {
    pub amount: u64,
}

#[derive(Clone)]
pub(super) struct LocalizedRecoveryConfig<const NOISE: usize> {
    secret: Column<Advice>,
    next: Column<Advice>,
    unrelated: [Column<Advice>; NOISE],
    selector: Selector,
}

impl<const NOISE: usize> Circuit<Fr> for LocalizedRecoveryCircuit<NOISE> {
    type Config = LocalizedRecoveryConfig<NOISE>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { amount: 0 }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let secret = meta.advice_column();
        let next = meta.advice_column();
        let unrelated = std::array::from_fn(|_| meta.advice_column());
        let public = meta.instance_column();
        let selector = meta.selector();
        meta.create_gate("localized recovery beside unrelated quadratics", |meta| {
            let s = meta.query_advice(secret, Rotation::cur());
            let d = meta.query_advice(next, Rotation::cur());
            let p = meta.query_instance(public, Rotation::cur());
            let q = meta.query_selector(selector);
            let two = Expression::Constant(Fr::from(2));
            // Expanded (s-p)^2, then a linear handoff to UCP once s is recovered.
            let mut equations = vec![
                s.clone() * s.clone() - two.clone() * p.clone() * s.clone() + p.clone() * p.clone(),
                d - s - two,
            ];
            for (index, column) in unrelated.iter().enumerate() {
                let v = meta.query_advice(*column, Rotation::cur());
                let shift = p.clone() + Expression::Constant(Fr::from(index as u64 + 1));
                equations.push(v.clone() * v - shift.clone() * shift);
            }
            equations
                .into_iter()
                .map(|e| q.clone() * e)
                .collect::<Vec<_>>()
        });
        LocalizedRecoveryConfig {
            secret,
            next,
            unrelated,
            selector,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "relevant and independent nonlinear cells",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                region.assign_advice(
                    || "secret",
                    config.secret,
                    0,
                    || Value::known(Fr::from(self.amount)),
                )?;
                region.assign_advice(
                    || "dependent",
                    config.next,
                    0,
                    || Value::known(Fr::from(self.amount + 2)),
                )?;
                for (index, column) in config.unrelated.iter().enumerate() {
                    region.assign_advice(
                        || "independent two-root value",
                        *column,
                        0,
                        || Value::known(Fr::from(self.amount + index as u64 + 1)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

#[test]
fn unrelated_nonlinear_gates_do_not_expand_the_targeted_public_leaf_component() {
    let input = discovery_demo_input();
    let circuit = LocalizedRecoveryCircuit::<16> { amount: 21 };
    MockProver::run(K, &circuit, vec![vec![Fr::from(21)]])
        .unwrap()
        .assert_satisfied();
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &input,
        discovery_demo_targets(),
        subset_options(2, 1),
    )
    .unwrap();
    assert_eq!(report.summary.exact_values, 2, "{report}");
    assert_eq!(report.domain_discovery_statistics.full_solver_checks, 1);
    assert_eq!(report.domain_discovery_statistics.subset_unsat_proofs, 1);
    let subset = std::fs::read_to_string("src/output/private_recovery_subset.smt2").unwrap();
    assert_eq!(
        subset
            .lines()
            .filter(|line| line.starts_with("(assert (and ( = ("))
            .count(),
        2
    );
    for column in 2..18 {
        assert!(!subset.contains(&format!("(declare-fun A-{column}-0 ")));
    }
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &input, &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

// Four links are intentionally longer than the subset's two-hop selection radius.
#[derive(Clone)]
struct FarConstraintCircuit;

impl Circuit<Fr> for FarConstraintCircuit {
    type Config = ([Column<Advice>; 4], Selector);
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        Self
    }
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let columns: [Column<Advice>; 4] = std::array::from_fn(|_| meta.advice_column());
        let selector = meta.selector();
        let public = meta.instance_column();
        meta.create_gate("far expanded root", |meta| {
            let v: Vec<_> = columns
                .iter()
                .map(|c| meta.query_advice(*c, Rotation::cur()))
                .collect();
            let p = meta.query_instance(public, Rotation::cur());
            let q = meta.query_selector(selector);
            vec![
                q.clone() * (v[0].clone() - v[1].clone()),
                q.clone() * (v[1].clone() - v[2].clone()),
                q.clone() * (v[2].clone() - v[3].clone()),
                q * (v[3].clone() * v[3].clone()
                    - Expression::Constant(Fr::from(2)) * p.clone() * v[3].clone()
                    + p.clone() * p),
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
            || "long recovery component",
            |mut region| {
                config.1.enable(&mut region, 0)?;
                for column in config.0 {
                    region.assign_advice(
                        || "linked value",
                        column,
                        0,
                        || Value::known(Fr::from(21)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

#[test]
fn a_far_omitted_constraint_requires_full_exhaustion_without_spurious_values() {
    let input = discovery_demo_input();
    MockProver::run(K, &FarConstraintCircuit, vec![vec![Fr::from(21)]])
        .unwrap()
        .assert_satisfied();
    let report = analyze_private_recoverability::<Fr, _, _>(
        &FarConstraintCircuit,
        K,
        &input,
        [CellId::advice(0, 0)],
        subset_options(3, 1),
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed, "{report}");
    assert_eq!(report.cells[0].domain, Some(domain(&[21])));
    assert_eq!(report.domain_discovery_statistics.solver_checks, 3);
    assert_eq!(report.domain_discovery_statistics.full_solver_checks, 2);
    assert_eq!(report.domain_discovery_statistics.subset_fallbacks, 1);
    assert_eq!(report.domain_discovery_statistics.models_found, 1);
    assert_eq!(report.domain_discovery_statistics.subset_unsat_proofs, 0);
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&FarConstraintCircuit, K, &input, &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

fn domain(values: &[i64]) -> UcpValueDomain {
    UcpValueDomain::finite_set(values.iter().copied().map(BigInt::from)).unwrap()
}

fn check_witness<const CASE: u8>(circuit: &UnboundedProjectionCircuit<CASE>, public: Fr) {
    MockProver::run(K, circuit, vec![vec![public]])
        .unwrap()
        .assert_satisfied();
}

fn analyze<const CASE: u8>(
    circuit: &UnboundedProjectionCircuit<CASE>,
    input: &AnalyzerInput,
    checks: usize,
    values: usize,
) -> PrivacyAnalysisReport {
    analyze_private_recoverability::<Fr, _, _>(
        circuit,
        K,
        input,
        discovery_demo_targets(),
        options(checks, values),
    )
    .unwrap()
}

#[test]
fn discovery_samples_resume_without_propagation_until_a_covering_domain_is_established() {
    let circuit = UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0));
    for checks in [1, 2, 3] {
        let mut options = options(checks, 2);
        options.domain_discovery.max_checks_per_round = 1;
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            K,
            &discovery_demo_input(),
            [CellId::advice(0, 0)],
            options,
        )
        .unwrap();
        assert_eq!(report.domain_discovery_statistics.solver_checks, checks);
        assert_eq!(report.semantic_queries, 0);
        assert_eq!(
            report.search_statistics.propagation_runs,
            if checks == 3 { 2 } else { 1 }
        );
        if checks == 3 {
            assert_eq!(report.cells[0].domain, Some(domain(&[3, 7])));
            assert_eq!(
                report
                    .ucp_result
                    .as_ref()
                    .unwrap()
                    .value_facts
                    .known_value(&CellId::advice(1, 0)),
                Some(&BigInt::from(0))
            );
        } else {
            assert!(report.cells[0].domain.is_none());
            assert_eq!(
                report.cells[0].domain_discovery.as_ref().unwrap().status,
                PrivateDomainDiscoveryStatus::Partial
            );
        }
    }
}

#[test]
fn discovers_a_complete_two_value_projection_without_an_initial_domain_then_restarts_ucp() {
    let circuit = UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0));
    check_witness(&circuit, Fr::from(21));
    let input = discovery_demo_input();
    let coarse = analyze(&circuit, &input, 0, 2);
    assert!(coarse.cells.iter().all(|cell| cell.domain.is_none()));
    assert!(coarse.cells.iter().all(|cell| !cell.domain_is_complete));
    let report = analyze(&circuit, &input, 3, 2);
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.cells[0].domain, Some(domain(&[3, 7])));
    assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
    assert_eq!(report.cells[1].domain, Some(domain(&[0])));
    assert_eq!(report.cells[1].uniqueness, PrivateCellUniqueness::Unique);
    assert!(report.cells.iter().all(|cell| cell.domain_is_complete));
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.baseline_domain.is_none()));
    assert_eq!(
        report.cells[0].domain_discovery.as_ref().unwrap().status,
        PrivateDomainDiscoveryStatus::Complete
    );
    assert!(report.cells[1].domain_discovery.is_none()); // Learned by UCP after Delta feedback.
    assert_eq!(report.domain_discovery_statistics.solver_checks, 3);
    assert_eq!(report.domain_discovery_statistics.complete_domains, 1);
    assert_eq!(report.domain_refinement_statistics.solver_checks, 0);
    assert_eq!(report.semantic_queries, 0);
    assert_eq!(report.search_statistics.unqueried_targets, 0);
    assert!(report.search_statistics.progress_rounds >= 1);
    let validated =
        validate_private_recovery_report::<Fr, _>(&circuit, K, &input, &report).unwrap();
    assert_eq!(validated.status, RecoveryValidationStatus::VerifiedDomains);
    let alternate = UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(7), Fr::from(0));
    check_witness(&alternate, Fr::from(21));
    assert_eq!(analyze(&alternate, &input, 3, 2).cells, report.cells);
    // An incorrect supplied witness must not change what the original constraints entail.
    let incorrect = UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(9), Fr::from(1));
    assert!(MockProver::run(K, &incorrect, vec![vec![Fr::from(21)]])
        .unwrap()
        .verify()
        .is_err());
    assert_eq!(analyze(&incorrect, &input, 3, 2).cells, report.cells);
}

#[test]
fn discovery_and_existing_domain_refinement_share_feedback_but_not_budgets() {
    let circuit = UnboundedProjectionCircuit::<WITH_BOOLEAN_OFFSET>::new(Fr::from(3), Fr::from(3));
    check_witness(&circuit, Fr::from(21));
    let mut options = options(3, 2);
    options.domain_refinement = super::privacy_domain::PrivacyDomainRefinementOptions {
        max_solver_checks: 4,
        max_candidates_per_cell: 4,
    };
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &discovery_demo_input(),
        discovery_demo_targets(),
        options,
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed, "{report}");
    assert_eq!(report.cells[0].domain, Some(domain(&[3, 7])));
    assert_eq!(report.cells[1].domain, Some(domain(&[3, 4, 7, 8])));
    assert!(report.cells[0].domain_discovery.is_some());
    assert!(report.cells[0].domain_refinement.is_none()); // No duplicate completeness checks.
    assert!(report.cells[1].domain_discovery.is_none());
    assert!(report.cells[1].domain_refinement.is_some());
    assert_eq!(report.domain_discovery_statistics.solver_checks, 3);
    assert_eq!(report.domain_refinement_statistics.solver_checks, 4);
    assert_eq!(report.summary.non_unique_cells, 2);
    assert_eq!(report.semantic_queries, 0);
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &discovery_demo_input(), &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

#[test]
fn two_sat_samples_without_exhaustion_are_non_unique_but_not_a_delta_domain() {
    let circuit = UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0));
    let report = analyze(&circuit, &discovery_demo_input(), 2, 2);
    assert!(report.cells.iter().all(|cell| cell.domain.is_none()));
    assert!(report.cells.iter().all(|cell| !cell.domain_is_complete));
    assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
    assert_eq!(report.cells[1].uniqueness, PrivateCellUniqueness::Unknown);
    let evidence = report.cells[0].domain_discovery.as_ref().unwrap();
    assert_eq!(evidence.status, PrivateDomainDiscoveryStatus::Partial);
    assert_eq!(
        evidence.observed_values,
        BTreeSet::from([3.into(), 7.into()])
    );
    assert_eq!(evidence.limitation, Some(RecoveryLimitation::QueryLimit));
    assert_eq!(report.domain_discovery_statistics.solver_checks, 2);
    assert!(report.domain_discovery_statistics.budget_exhausted);
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &discovery_demo_input(), &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::NoDomainClaims
    );
}

#[test]
fn one_sat_sample_is_not_recovered_but_a_singleton_exhaustion_recovers_and_propagates() {
    let circuit = UnboundedProjectionCircuit::<UNIQUE>::new(Fr::from(1), Fr::from(3));
    check_witness(&circuit, Fr::from(21));
    let partial = analyze(&circuit, &discovery_demo_input(), 1, 1);
    assert_eq!(partial.cells[0].domain, None);
    assert_eq!(partial.search_statistics.propagation_runs, 1);
    assert_eq!(
        partial.cells[0]
            .domain_discovery
            .as_ref()
            .unwrap()
            .observed_values,
        BTreeSet::from([1.into()])
    );
    let report = analyze(&circuit, &discovery_demo_input(), 2, 1);
    assert_eq!(report.summary.exact_values, 2);
    assert_eq!(report.search_statistics.propagation_runs, 2);
    assert_eq!(report.cells[0].domain, Some(domain(&[1])));
    assert_eq!(report.cells[1].domain, Some(domain(&[3])));
    assert_eq!(report.domain_discovery_statistics.solver_checks, 2);
    assert!(report.cells[1].domain_discovery.is_none());
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &discovery_demo_input(), &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

#[test]
fn partial_discovery_does_not_replace_a_later_uniqueness_proof() {
    let circuit = UnboundedProjectionCircuit::<UNIQUE>::new(Fr::from(1), Fr::from(3));
    let mut options = options(1, 1);
    options.max_semantic_queries = 1;
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &discovery_demo_input(),
        discovery_demo_targets(),
        options,
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.cells[0].domain, Some(domain(&[1])));
    assert_eq!(report.cells[1].domain, Some(domain(&[3])));
    let samples = report.cells[0].domain_discovery.as_ref().unwrap();
    assert_eq!(samples.status, PrivateDomainDiscoveryStatus::Partial);
    assert_eq!(samples.limitation, Some(RecoveryLimitation::QueryLimit));
    assert_eq!(report.domain_discovery_statistics.complete_domains, 0);
    assert_eq!(report.domain_discovery_statistics.solver_checks, 1);
    // Ordinary SMT establishes uniqueness; only then does the value propagate to the other cell.
    assert_eq!(report.cells[0].query_attempts, 1);
    assert_eq!(report.cells[1].query_attempts, 0);
    assert_eq!(report.semantic_queries, 1);
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &discovery_demo_input(), &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

#[test]
fn broad_projections_hit_the_value_cap_without_claiming_a_small_covering_set() {
    let circuit = UnboundedProjectionCircuit::<FREE_SUM>::new(Fr::from(3), Fr::from(18));
    check_witness(&circuit, Fr::from(21));
    let report = analyze(&circuit, &discovery_demo_input(), 6, 2);
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.summary.non_unique_cells, 2);
    assert_eq!(report.summary.finite_domains, 0);
    assert!(report.cells.iter().all(|cell| cell.domain.is_none()));
    for cell in &report.cells {
        let evidence = cell.domain_discovery.as_ref().unwrap();
        assert_eq!(evidence.status, PrivateDomainDiscoveryStatus::Partial);
        assert_eq!(evidence.observed_values.len(), 2);
        assert_eq!(evidence.models_found, 3);
        assert_eq!(
            evidence.limitation,
            Some(RecoveryLimitation::DomainSizeLimit)
        );
    }
    assert_eq!(report.domain_discovery_statistics.solver_checks, 6);
    assert_eq!(report.domain_discovery_statistics.complete_domains, 0);
    assert_eq!(report.search_statistics.propagation_runs, 1);
}

#[test]
fn only_target_values_are_blocked_not_whole_witness_assignments() {
    let circuit =
        UnboundedProjectionCircuit::<UNIQUE_WITH_FREE_WITNESS>::new(Fr::from(1), Fr::from(37));
    check_witness(&circuit, Fr::from(21));
    let report = analyze(&circuit, &discovery_demo_input(), 4, 1);
    assert_eq!(report.cells[0].domain, Some(domain(&[1])));
    assert_eq!(
        report.cells[0]
            .domain_discovery
            .as_ref()
            .unwrap()
            .solver_checks,
        2
    );
    assert_eq!(report.cells[1].domain, None);
    assert_eq!(report.cells[1].uniqueness, PrivateCellUniqueness::NonUnique);
    // The second model for the free cell lies outside its one stored sample.
    let free = report.cells[1].domain_discovery.as_ref().unwrap();
    assert_eq!(free.observed_values.len(), 1);
    assert_eq!(free.models_found, 2);
    assert!(free.witnessed_non_unique);
}

#[test]
fn discovered_domains_use_concrete_public_observations_and_signed_representatives() {
    for (secret, public, expected) in [
        (Fr::from(2), BigInt::from(16), domain(&[2, 8])),
        (-Fr::from(1), BigInt::from(-11), domain(&[-1, 11])),
    ] {
        let circuit = UnboundedProjectionCircuit::<TWO_ROOTS>::new(secret, Fr::from(0));
        let field_public = if public < 0.into() {
            -Fr::from(11)
        } else {
            Fr::from(16)
        };
        check_witness(&circuit, field_public);
        let report = analyze(&circuit, &observations(public), 3, 2);
        assert_eq!(report.cells[0].domain, Some(expected));
        assert_eq!(report.cells[1].domain, Some(domain(&[0])));
    }
}

#[test]
fn full_width_discovered_values_are_not_limited_to_machine_integers() {
    let mut wide = Fr::from(1);
    for _ in 0..200 {
        wide = wide + wide;
    }
    let public = wide * wide;
    let public_integer = BigInt::parse_bytes(
        format!("{:?}", public).trim_start_matches("0x").as_bytes(),
        16,
    )
    .unwrap();
    let circuit = UnboundedProjectionCircuit::<WIDE_ROOTS>::new(wide, Fr::from(0));
    check_witness(&circuit, public);
    let input = observations(public_integer);
    let report = analyze(&circuit, &input, 3, 2);
    let wide_integer = BigInt::from(1) << 200_usize;
    assert_eq!(
        report.cells[0].domain,
        UcpValueDomain::finite_set([wide_integer.clone(), -wide_integer])
    );
    assert_eq!(
        report.cells[0].domain_discovery.as_ref().unwrap().status,
        PrivateDomainDiscoveryStatus::Complete
    );
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &input, &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

#[test]
fn discovery_refreshes_exact_search_facts_after_runtime_recovery_and_ucp_feedback() {
    let circuit =
        UnboundedProjectionCircuit::<FREE_FIRST_RECOVERABLE_CHAIN>::new(Fr::from(37), Fr::from(21));
    let input = discovery_demo_input();
    let mut options = options(5, 16);
    options.domain_discovery.max_checks_per_round = 1;
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &input,
        [CellId::advice(0, 0), CellId::advice(1, 0)],
        options,
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.domain_discovery_statistics.solver_checks, 5);
    assert_eq!(report.semantic_queries, 0);
    assert!(report.cells[0].domain.is_none());
    assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
    assert_eq!(report.cells[1].domain, Some(domain(&[21])));
    let query = std::fs::read_to_string("src/output/private_domain_discovery.smt2").unwrap();
    assert!(query.contains("( = A-1-0 (as ff21 F))"));
    // This cell is not a target: its value is obtained by propagation after recovering A-1-0.
    assert!(query.contains("( = A-2-0 (as ff23 F))"));
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &input, &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

#[test]
fn original_enumeration_ignores_later_strengthening_and_does_not_modify_the_main_file() {
    let circuit = UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0));
    let mut context = prepare_privacy_analysis::<Fr, _, _>(
        &circuit,
        K,
        &discovery_demo_input(),
        discovery_demo_targets(),
    )
    .unwrap();
    let original = context
        .analyzer
        .original_private_query_context(&context.analyzer_input, &context.private_cells)
        .unwrap();
    let secret = context.private_cells[0].clone();
    let mut hint = UcpValueFacts::new();
    hint.mark_known(secret.clone(), 3.into());
    context.analyzer.set_ucp_value_facts(&hint);
    context
        .analyzer
        .query_ucp_cell_uniqueness_with_value(&context.analyzer_input, &secret)
        .unwrap();
    let before = std::fs::read_to_string(&*SMT_FILE_PATH).unwrap();
    let first = original
        .query_unseen_value::<Fr>(&secret, &BTreeSet::new(), Some(2_000))
        .unwrap()
        .unwrap();
    let second = original
        .query_unseen_value::<Fr>(&secret, &BTreeSet::from([first.clone()]), Some(2_000))
        .unwrap()
        .unwrap();
    assert_ne!(first, second);
    assert_eq!(
        BTreeSet::from([first.clone(), second.clone()]),
        BTreeSet::from([3.into(), 7.into()])
    );
    assert!(original
        .query_unseen_value::<Fr>(&secret, &BTreeSet::from([first, second]), Some(2_000))
        .unwrap()
        .is_none());
    assert!(original
        .query_unseen_value::<Fr>(&secret, &BTreeSet::new(), Some(2_000))
        .unwrap()
        .is_some());
    assert_eq!(std::fs::read_to_string(&*SMT_FILE_PATH).unwrap(), before);
}

#[test]
fn fixed_copy_targets_can_be_enumerated_without_requesting_a_constant_model_expression() {
    let circuit = UnboundedProjectionCircuit::<COPIED_CONSTANT>::new(Fr::from(7), Fr::from(7));
    check_witness(&circuit, Fr::from(21));
    let mut context = prepare_privacy_analysis::<Fr, _, _>(
        &circuit,
        K,
        &discovery_demo_input(),
        discovery_demo_targets(),
    )
    .unwrap();
    let original = context
        .analyzer
        .original_private_query_context(&context.analyzer_input, &context.private_cells)
        .unwrap();
    let secret = &context.private_cells[0];
    assert_eq!(
        original
            .query_unseen_value::<Fr>(secret, &BTreeSet::new(), Some(2_000))
            .unwrap(),
        Some(7.into())
    );
    assert!(original
        .query_unseen_value::<Fr>(secret, &BTreeSet::from([7.into()]), Some(2_000))
        .unwrap()
        .is_none());
}

#[test]
fn inconsistent_initial_context_never_starts_discovery_or_exports_samples() {
    let circuit = UnboundedProjectionCircuit::<INCONSISTENT>::new(Fr::from(0), Fr::from(0));
    let report = analyze(&circuit, &discovery_demo_input(), 3, 2);
    assert_eq!(report.status, PrivacyAnalysisStatus::Inconsistent);
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.domain.is_none() && cell.domain_discovery.is_none()));
    assert_eq!(report.domain_discovery_statistics.solver_checks, 0);
}

#[test]
fn known_ucp_domains_use_the_existing_refiner_not_blind_discovery() {
    let circuit = UnboundedProjectionCircuit::<BOOLEAN>::new(Fr::from(1), Fr::from(0));
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &discovery_demo_input(),
        [CellId::advice(0, 0)],
        options(3, 2),
    )
    .unwrap();
    assert_eq!(report.cells[0].domain, Some(domain(&[0, 1])));
    assert!(report.cells[0].domain_discovery.is_none());
    assert_eq!(report.domain_discovery_statistics.solver_checks, 0);
}

#[test]
fn invalid_discovery_sizes_are_rejected_before_synthesis() {
    for size in [0, 257] {
        let error = analyze_private_recoverability::<Fr, _, _>(
            &UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0)),
            K,
            &discovery_demo_input(),
            discovery_demo_targets(),
            options(3, size),
        )
        .unwrap_err();
        assert!(error.to_string().contains("values per cell"));
    }
}

#[test]
fn fair_rounds_preserve_separate_blocking_sets_until_each_projection_is_complete() {
    let circuit = UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0));
    let mut options = options(5, 2);
    options.domain_discovery.max_checks_per_round = 1;
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &discovery_demo_input(),
        discovery_demo_targets(),
        options,
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.cells[0].domain, Some(domain(&[3, 7])));
    assert_eq!(report.cells[1].domain, Some(domain(&[0])));
    let roots = report.cells[0].domain_discovery.as_ref().unwrap();
    let dependent = report.cells[1].domain_discovery.as_ref().unwrap();
    assert_eq!(roots.observed_values, BTreeSet::from([3.into(), 7.into()]));
    assert_eq!(dependent.observed_values, BTreeSet::from([0.into()]));
    assert_eq!(roots.solver_checks, 3);
    assert_eq!(dependent.solver_checks, 2);
    assert_eq!(report.domain_discovery_statistics.solver_checks, 5);
    assert_eq!(report.domain_discovery_statistics.attempted_cells, 2);
    assert_eq!(report.domain_discovery_statistics.resumed_checks, 3);
    assert_eq!(report.domain_discovery_statistics.retry_checks, 0);
    assert_eq!(report.semantic_queries, 0);
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &discovery_demo_input(), &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

#[test]
fn fair_budget_stop_does_not_promote_one_sample_per_target() {
    let circuit = UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0));
    let mut options = options(2, 2);
    options.domain_discovery.max_checks_per_round = 1;
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &discovery_demo_input(),
        discovery_demo_targets(),
        options,
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::QueryLimitReached);
    assert_eq!(report.domain_discovery_statistics.solver_checks, 2);
    assert_eq!(report.domain_discovery_statistics.attempted_cells, 2);
    assert!(report.domain_discovery_statistics.budget_exhausted);
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.domain.is_none() && cell.uniqueness == PrivateCellUniqueness::Unknown));
    for cell in &report.cells {
        let evidence = cell.domain_discovery.as_ref().unwrap();
        assert_eq!(evidence.solver_checks, 1);
        assert_eq!(evidence.observed_values.len(), 1);
        assert_eq!(evidence.status, PrivateDomainDiscoveryStatus::Partial);
        assert_eq!(evidence.limitation, Some(RecoveryLimitation::QueryLimit));
    }
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &discovery_demo_input(), &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::NoDomainClaims
    );
}

#[test]
fn ucp_priority_and_fairness_recover_later_private_targets_without_sampling_the_witness() {
    let circuit =
        UnboundedProjectionCircuit::<FREE_FIRST_RECOVERABLE_CHAIN>::new(Fr::from(37), Fr::from(21));
    check_witness(&circuit, Fr::from(21));
    let mut options = options(4, 16);
    options.domain_discovery.max_checks_per_round = 1;
    let targets = [
        CellId::advice(0, 0),
        CellId::advice(1, 0),
        CellId::advice(2, 0),
    ];
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &discovery_demo_input(),
        targets.clone(),
        options,
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::QueryLimitReached);
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.baseline_domain.is_none()));
    assert_eq!(report.cells[0].domain, None);
    assert_eq!(report.cells[1].domain, Some(domain(&[21])));
    assert_eq!(report.cells[2].domain, Some(domain(&[23])));
    assert_eq!(report.domain_discovery_statistics.solver_checks, 4);
    assert_eq!(report.domain_discovery_statistics.attempted_cells, 3);
    assert_eq!(report.domain_discovery_statistics.complete_domains, 1);
    assert_eq!(report.summary.exact_values, 2);
    assert_eq!(
        report.cells[0]
            .domain_discovery
            .as_ref()
            .unwrap()
            .solver_checks,
        1
    );
    assert_eq!(
        report.cells[1]
            .domain_discovery
            .as_ref()
            .unwrap()
            .solver_checks,
        2
    );
    // UCP recovers the final target before its singleton exhaustion check is needed.
    assert_eq!(
        report.cells[2].domain_discovery.as_ref().unwrap().status,
        PrivateDomainDiscoveryStatus::Partial
    );
    assert_eq!(report.semantic_queries, 0);
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, K, &discovery_demo_input(), &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
    let alternate =
        UnboundedProjectionCircuit::<FREE_FIRST_RECOVERABLE_CHAIN>::new(Fr::from(99), Fr::from(21));
    check_witness(&alternate, Fr::from(21));
    let other = analyze_private_recoverability::<Fr, _, _>(
        &alternate,
        K,
        &discovery_demo_input(),
        targets,
        options,
    )
    .unwrap();
    assert_eq!(other.cells, report.cells);
}

#[test]
fn invalid_round_or_retry_options_fail_before_analysis() {
    for settings in [
        PrivacyDomainDiscoveryOptions {
            max_checks_per_round: 0,
            ..Default::default()
        },
        PrivacyDomainDiscoveryOptions {
            retry_solver_timeout_ms: Some(0),
            ..Default::default()
        },
    ] {
        let mut options = options(4, 2);
        options.domain_discovery = PrivacyDomainDiscoveryOptions {
            max_solver_checks: 4,
            ..settings
        };
        assert!(analyze_private_recoverability::<Fr, _, _>(
            &UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0)),
            K,
            &discovery_demo_input(),
            discovery_demo_targets(),
            options,
        )
        .is_err());
    }
}
