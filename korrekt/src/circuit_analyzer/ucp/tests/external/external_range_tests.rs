//! Aggregation harnesses importing real upstream range-check implementations.
//! These are local circuits around external gadgets, not unchanged external applications.

use super::{
    cell::CellId,
    external_circuit_tests::observations,
    privacy::{
        analyze_private_recoverability, PrivacyAnalysisOptions, PrivacyAnalysisStatus,
        PrivateCellUniqueness,
    },
    privacy_validation::{validate_private_recovery_report, RecoveryValidationStatus},
    value::UcpValueDomain,
};
use crate::circuit_analyzer::{analyzable::Analyzable, halo2_proofs_libs::*};
use halo2_gadgets::utilities::{
    decompose_running_sum::RunningSumConfig, lookup_range_check::LookupRangeCheckConfig,
};
use num_bigint::BigInt;

pub(super) const RANGE_K: u32 = 5;
const WINDOW_BITS: usize = 2;
const WINDOWS: usize = 2;

//Two private bounded balances; only their aggregate is public.
//At total=15 several splits remain possible; at total=30 both balances must equal 15.
#[derive(Clone, Debug)]
pub(super) struct RangeAggregateCircuit<const LOOKUP: bool> {
    left: u64,
    right: u64,
}

impl<const LOOKUP: bool> RangeAggregateCircuit<LOOKUP> {
    pub(super) fn new(left: u64, right: u64) -> Self {
        Self { left, right }
    }
}

#[derive(Clone, Debug)]
pub(super) struct RangeAggregateConfig {
    lookup: Option<LookupRangeCheckConfig<Fr, WINDOW_BITS>>,
    polynomial: Option<RunningSumConfig<Fr, WINDOW_BITS>>,
    lookup_table: Option<TableColumn>,
    sum_columns: [Column<Advice>; 3],
    sum_selector: Selector,
    public: Column<Instance>,
}

impl<const LOOKUP: bool> Circuit<Fr> for RangeAggregateCircuit<LOOKUP> {
    type Config = RangeAggregateConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(0, 0)
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let running_sum = meta.advice_column();
        let constants = meta.fixed_column();
        meta.enable_constant(constants);
        let (lookup, polynomial, lookup_table) = if LOOKUP {
            let table = meta.lookup_table_column();
            (
                Some(LookupRangeCheckConfig::configure(meta, running_sum, table)),
                None,
                Some(table),
            )
        } else {
            let selector = meta.selector();
            (
                None,
                Some(RunningSumConfig::configure(meta, selector, running_sum)),
                None,
            )
        };
        let sum_columns = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];
        for column in sum_columns {
            meta.enable_equality(column);
        }
        let public = meta.instance_column();
        meta.enable_equality(public);
        let sum_selector = meta.selector();
        //Only the aggregation gate is ours; all range gates/lookups come from the library.
        meta.create_gate("private bounded aggregate", |meta| {
            let q = meta.query_selector(sum_selector);
            let a = meta.query_advice(sum_columns[0], Rotation::cur());
            let b = meta.query_advice(sum_columns[1], Rotation::cur());
            let total = meta.query_advice(sum_columns[2], Rotation::cur());
            vec![q * (a + b - total)]
        });
        RangeAggregateConfig {
            lookup,
            polynomial,
            lookup_table,
            sum_columns,
            sum_selector,
            public,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let (a, b) = if let Some(lookup) = &config.lookup {
            //Upstream leaves table loading to the caller; its load helper is cfg(test)-only.
            layouter.assign_table(
                || "two-bit range table",
                |mut table| {
                    for value in 0..(1 << WINDOW_BITS) {
                        table.assign_cell(
                            || "range value",
                            config.lookup_table.unwrap(),
                            value,
                            || Value::known(Fr::from(value as u64)),
                        )?;
                    }
                    Ok(())
                },
            )?;
            let left = lookup.witness_check(
                layouter.namespace(|| "range left"),
                Value::known(Fr::from(self.left)),
                WINDOWS,
                true,
            )?;
            let right = lookup.witness_check(
                layouter.namespace(|| "range right"),
                Value::known(Fr::from(self.right)),
                WINDOWS,
                true,
            )?;
            (left[0].clone(), right[0].clone())
        } else {
            let polynomial = config.polynomial.as_ref().unwrap();
            let mut witness = |name, value| {
                layouter.assign_region(
                    || name,
                    |mut region| {
                        polynomial
                            .witness_decompose(
                                &mut region,
                                0,
                                Value::known(Fr::from(value)),
                                true,
                                WINDOW_BITS * WINDOWS,
                                WINDOWS,
                            )
                            .map(|sums| sums[0].clone())
                    },
                )
            };
            (
                witness("range private left", self.left)?,
                witness("range private right", self.right)?,
            )
        };
        let total = layouter.assign_region(
            || "aggregate",
            |mut region| {
                config.sum_selector.enable(&mut region, 0)?;
                a.copy_advice(|| "left", &mut region, config.sum_columns[0], 0)?;
                b.copy_advice(|| "right", &mut region, config.sum_columns[1], 0)?;
                region.assign_advice(
                    || "total",
                    config.sum_columns[2],
                    0,
                    || a.value().copied() + b.value().copied(),
                )
            },
        )?;
        layouter.constrain_instance(total.cell(), config.public, 0)
    }
}

//z_0 is the private input. z_1, z_2 and advice copies are derived witnesses, not extra secrets.
pub(super) fn range_private_inputs<const LOOKUP: bool>(
    circuit: &RangeAggregateCircuit<LOOKUP>,
) -> Vec<CellId> {
    let analyzable = Analyzable::<Fr>::config_and_synthesize(circuit, RANGE_K).unwrap();
    assert_eq!(analyzable.cs.lookups.is_empty(), !LOOKUP);
    let targets: Vec<_> = analyzable
        .regions
        .iter()
        .filter(|region| {
            matches!(
                region.name.as_str(),
                "Witness element" | "range private left" | "range private right"
            )
        })
        .map(|region| {
            let mut rows: Vec<_> = region
                .cells
                .iter()
                .filter(|(column, _)| column.column_type() == &Any::Advice && column.index() == 0)
                .map(|(_, row)| *row)
                .collect();
            rows.sort_unstable();
            rows.dedup();
            assert_eq!(
                rows.len(),
                WINDOWS + 1,
                "Upstream running-sum layout changed"
            );
            assert_eq!(rows[2] - rows[0], WINDOWS);
            CellId::advice(0, i32::try_from(rows[0]).unwrap())
        })
        .collect();
    assert_eq!(targets.len(), 2);
    assert_ne!(targets[0], targets[1]);
    targets
}

fn mock<const LOOKUP: bool>(circuit: &RangeAggregateCircuit<LOOKUP>, total: u64) -> bool {
    zcash_halo2_proofs::dev::MockProver::run(RANGE_K, circuit, vec![vec![Fr::from(total)]])
        .unwrap()
        .verify()
        .is_ok()
}

fn boundary<const LOOKUP: bool>() {
    let circuit = RangeAggregateCircuit::<LOOKUP>::new(15, 15);
    assert!(mock(&circuit, 30));
    let targets = range_private_inputs(&circuit);
    let input = observations(&[30]);
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        RANGE_K,
        &input,
        targets,
        PrivacyAnalysisOptions {
            solver_timeout_ms: Some(2_000),
            ..Default::default()
        },
    )
    .unwrap();
    println!("Imported range gadget (lookup={LOOKUP}), public total=30:\n{report}");
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.summary.exact_values, 2);
    assert_eq!(
        report.semantic_queries, 0,
        "Range domains and sum suffice without cell queries"
    );
    for cell in &report.cells {
        assert_eq!(cell.uniqueness, PrivateCellUniqueness::Unique);
        assert_eq!(cell.domain, Some(UcpValueDomain::exact(BigInt::from(15))));
    }
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, RANGE_K, &input, &report).unwrap();
    println!("Fresh SMT validation:\n{validation}");
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
    let mut wrong = report;
    wrong.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(14)));
    let refuted =
        validate_private_recovery_report::<Fr, _>(&circuit, RANGE_K, &input, &wrong).unwrap();
    assert_eq!(refuted.status, RecoveryValidationStatus::Refuted);
    assert_eq!(refuted.cells[0].counterexample, Some(BigInt::from(15)));
}

fn interior<const LOOKUP: bool>() {
    let circuit = RangeAggregateCircuit::<LOOKUP>::new(3, 12);
    let alternate = RangeAggregateCircuit::<LOOKUP>::new(7, 8);
    assert!(mock(&circuit, 15));
    assert!(mock(&alternate, 15));
    let input = observations(&[15]);
    let analyze = |circuit: &RangeAggregateCircuit<LOOKUP>| {
        analyze_private_recoverability::<Fr, _, _>(
            circuit,
            RANGE_K,
            &input,
            range_private_inputs(circuit),
            PrivacyAnalysisOptions {
                solver_timeout_ms: Some(2_000),
                ..Default::default()
            },
        )
        .unwrap()
    };
    let report = analyze(&circuit);
    println!("Imported range gadget (lookup={LOOKUP}), public total=15:\n{report}");
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.summary.non_unique_cells, 2);
    assert_eq!(report.summary.exact_values, 0);
    assert_eq!(report.summary.finite_domains, 2);
    let range = UcpValueDomain::finite_set((0..16).map(BigInt::from)).unwrap();
    for cell in &report.cells {
        assert_eq!(cell.domain, Some(range.clone()));
        assert_eq!(cell.baseline_domain, Some(range.clone()));
        assert!(!cell.domain_refined_from_baseline);
    }
    assert_eq!(report.cells, analyze(&alternate).cells);
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, RANGE_K, &input, &report).unwrap();
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
    //Alternative witnesses demonstrate ambiguity, not full cryptographic privacy.
}

fn partial_refinement<const LOOKUP: bool>() {
    //Total 16 excludes zero, but leaves 15 possible values for each private input.
    let circuit = RangeAggregateCircuit::<LOOKUP>::new(7, 9);
    assert!(mock(&circuit, 16));
    let input = observations(&[16]);
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        RANGE_K,
        &input,
        range_private_inputs(&circuit),
        PrivacyAnalysisOptions {
            max_semantic_queries: 0,
            solver_timeout_ms: Some(2_000),
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::QueryLimitReached);
    assert_eq!(report.summary.finite_domains, 2);
    assert_eq!(report.summary.exact_values, 0);
    assert_eq!(report.summary.unique_cells, 0);
    assert_eq!(
        report.summary.non_unique_cells, 0,
        "No SMT ambiguity query was made"
    );
    for cell in &report.cells {
        assert_eq!(
            cell.domain,
            UcpValueDomain::finite_set((1..16).map(BigInt::from))
        );
        assert_eq!(
            cell.baseline_domain,
            UcpValueDomain::finite_set((0..16).map(BigInt::from))
        );
        assert!(cell.domain_refined_from_baseline);
    }
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, RANGE_K, &input, &report).unwrap();
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
    //An unjustified tighter claim must be rejected even when it contains the supplied witness.
    let mut wrong = report;
    wrong.cells[0].domain = UcpValueDomain::finite_set((2..16).map(BigInt::from));
    let refuted =
        validate_private_recovery_report::<Fr, _>(&circuit, RANGE_K, &input, &wrong).unwrap();
    assert_eq!(refuted.status, RecoveryValidationStatus::Refuted);
    assert_eq!(refuted.cells[0].counterexample, Some(BigInt::from(1)));
}

#[test]
fn external_range_polynomial_public_total_refines_a_non_singleton_domain() {
    partial_refinement::<false>();
}

#[test]
fn external_range_lookup_public_total_refines_a_non_singleton_domain() {
    partial_refinement::<true>();
}

#[test]
fn external_range_only_assigned_fixed_constants_seed_delta() {
    fn check<const LOOKUP: bool>() {
        use super::{cell::CellKind, extractor::extract_ucp_problem};
        let circuit = RangeAggregateCircuit::<LOOKUP>::new(3, 12);
        let targets = range_private_inputs(&circuit);
        let mut analyzable = Analyzable::<Fr>::config_and_synthesize(&circuit, RANGE_K).unwrap();
        let problem = extract_ucp_problem(&analyzable);
        let baseline = problem.analyze_with_values(
            problem.initial_facts.clone(),
            problem.initial_value_facts.clone(),
        );
        for target in &targets {
            assert_eq!(
                baseline.value_facts.domain(target),
                UcpValueDomain::finite_set((0..16).map(BigInt::from)).as_ref()
            );
        }
        //Both strict decompositions may copy separate fixed zero cells into one equality cycle.
        let fixed: Vec<_> = problem
            .initial_value_facts
            .domains()
            .iter()
            .filter(|(cell, domain)| {
                cell.kind == CellKind::Fixed && domain.exact_value() == Some(&BigInt::from(0))
            })
            .map(|(cell, _)| cell.clone())
            .collect();
        assert!(!fixed.is_empty());
        for unavailable in [CellValue::Unassigned, CellValue::Poison(0)] {
            for cell in &fixed {
                analyzable.fixed[cell.column][cell.row as usize] = unavailable.clone();
            }
            let problem = extract_ucp_problem(&analyzable);
            for cell in &fixed {
                assert!(problem.initial_value_facts.known_value(cell).is_none());
            }
            let result = problem.analyze_with_values(
                problem.initial_facts.clone(),
                problem.initial_value_facts.clone(),
            );
            for target in &targets {
                assert!(
                    result.value_facts.domain(target).is_none(),
                    "Unknown fixed is not zero"
                );
            }
        }
    }
    check::<false>();
    check::<true>();
}

#[test]
fn external_range_polynomial_boundary_recovers_private_balances() {
    boundary::<false>();
}

#[test]
fn external_range_lookup_boundary_recovers_private_balances() {
    boundary::<true>();
}

#[test]
fn external_range_polynomial_interior_preserves_ambiguity() {
    interior::<false>();
}

#[test]
fn external_range_lookup_interior_preserves_ambiguity() {
    interior::<true>();
}

#[test]
fn external_range_gadgets_reject_out_of_range_witnesses() {
    //Same aggregate, but 16 lies outside the strict four-bit range.
    assert!(!mock(&RangeAggregateCircuit::<false>::new(16, 14), 30));
    assert!(!mock(&RangeAggregateCircuit::<true>::new(16, 14), 30));
}

#[test]
fn external_range_impossible_aggregate_does_not_produce_vacuous_recovery() {
    fn check<const LOOKUP: bool>() {
        let circuit = RangeAggregateCircuit::<LOOKUP>::new(15, 15);
        let input = observations(&[31]);
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            RANGE_K,
            &input,
            range_private_inputs(&circuit),
            PrivacyAnalysisOptions {
                solver_timeout_ms: Some(2_000),
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(report.status, PrivacyAnalysisStatus::Inconsistent);
        assert_eq!(report.summary.exact_values, 0);
        assert!(report.ucp_result.is_none());
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, RANGE_K, &input, &report)
                .unwrap()
                .status,
            RecoveryValidationStatus::Inconsistent
        );
    }
    check::<false>();
    check::<true>();
}
