//! Synthetic risk audit: heterogeneous disclosures and SMT-to-UCP feedback.
//! Run solver tests serially. Counts below are reference projections, not entropy estimates.

use super::*;
use crate::circuit_analyzer::ucp::{
    engine::UcpResult, privacy_discovery::PrivacyDomainDiscoveryOptions,
    privacy_domain::PrivacyDomainRefinementOptions,
};
use num_bigint::BigInt;
use std::collections::BTreeSet;

const K: u32 = 8;
const TIERS: [u64; 16] = [0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3];
const X: usize = 0;
const BITS: usize = 1;
const Q7: usize = 11;
const Q9: usize = 12;
const LOW: usize = 13;
const HIGH: usize = 14;
const TIER: usize = 15;
const HI: usize = 16;
const R7: usize = 17;
const WEIGHT: usize = 18;
const LO: usize = 19;
const S: usize = 20;
const H: usize = 21;
const T: usize = 22;
const U: usize = 23;
const PRODUCT: usize = 24;
const DIFFERENCE: usize = 25;
const DIFFERENCE_BITS: usize = 26;
const COLUMNS: usize = 36;
const PUBLIC_COLUMNS: [usize; 5] = [TIER, HI, R7, WEIGHT, LO];

fn disclosures(x: u64) -> [u64; 5] {
    [
        TIERS[(x / 64) as usize],
        u64::from(x > 600),
        x % 7,
        x.count_ones().into(),
        (x % 64) % 9,
    ]
}

fn reference_candidates(published: usize) -> Vec<u64> {
    let observed = disclosures(713);
    (0..1024)
        .filter(|x| disclosures(*x)[..published] == observed[..published])
        .collect()
}

#[derive(Clone)]
struct RiskAuditCircuit<const PUBLISHED: usize, const SEEDED: bool> {
    values: [u64; COLUMNS],
}

impl<const PUBLISHED: usize, const SEEDED: bool> RiskAuditCircuit<PUBLISHED, SEEDED> {
    fn new(x: u64, calibration: u64) -> Self {
        assert!(x < 1024);
        let mut values = [0; COLUMNS];
        values[X] = x;
        for bit in 0..10 {
            values[BITS + bit] = (x >> bit) & 1;
        }
        values[Q7] = x / 7;
        values[Q9] = (x % 64) / 9;
        values[LOW] = x % 64;
        values[HIGH] = x / 64;
        for (column, value) in PUBLIC_COLUMNS.into_iter().zip(disclosures(x)) {
            values[column] = value;
        }
        values[S] = calibration;
        values[T] = x;
        values[U] = 2 * x + 1;
        values[PRODUCT] = 21;
        values[DIFFERENCE] = if x > 600 { x - 601 } else { 600 - x };
        for bit in 0..10 {
            values[DIFFERENCE_BITS + bit] = (values[DIFFERENCE] >> bit) & 1;
        }
        Self { values }
    }

    fn instances(&self) -> Vec<Vec<Fr>> {
        vec![PUBLIC_COLUMNS
            .iter()
            .take(PUBLISHED)
            .map(|column| self.values[*column])
            .chain([self.values[PRODUCT]])
            .map(Fr::from)
            .collect()]
    }

    fn input(&self) -> AnalyzerInput {
        AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput::new(
                PUBLIC_COLUMNS
                    .iter()
                    .take(PUBLISHED)
                    .map(|column| self.values[*column])
                    .chain([self.values[PRODUCT]])
                    .enumerate()
                    .map(|(row, value)| (format!("I-0-{row}"), value)),
                1,
            ),
            lookup_method: LookupMethod::InlineConstraints,
        }
    }
}

#[derive(Clone)]
struct RiskAuditConfig {
    advice: [Column<Advice>; COLUMNS],
    public: Column<Instance>,
    bias: Column<Fixed>,
    selectors: [Selector; 4],
    tables: [TableColumn; 6],
    seed_table: Option<TableColumn>,
}

impl<const PUBLISHED: usize, const SEEDED: bool> Circuit<Fr>
    for RiskAuditCircuit<PUBLISHED, SEEDED>
{
    type Config = RiskAuditConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(0, 0)
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        assert!(PUBLISHED <= PUBLIC_COLUMNS.len());
        let advice = array::from_fn(|_| meta.advice_column());
        let public = meta.instance_column();
        let bias = meta.fixed_column();
        meta.enable_equality(public);
        for column in [X, TIER, HI, R7, WEIGHT, LO, PRODUCT] {
            meta.enable_equality(advice[column]);
        }
        let selectors = array::from_fn(|_| meta.complex_selector());
        let tables = array::from_fn(|_| meta.lookup_table_column());
        let seed_table = SEEDED.then(|| meta.lookup_table_column());
        let constant = |n| Expression::Constant(Fr::from(n));

        meta.create_gate("ten-bit risk score and its disclosures", |meta| {
            let q = meta.query_selector(selectors[0]);
            let a: [Expression<Fr>; COLUMNS] = array::from_fn(|column| {
                if column <= LO || column >= DIFFERENCE {
                    meta.query_advice(advice[column], Rotation::cur())
                } else {
                    constant(0)
                }
            });
            let packed = |start: usize, count: usize, weights: bool| {
                (0..count).fold(constant(0), |sum, bit| {
                    sum + constant(if weights { 1 << bit } else { 1 }) * a[start + bit].clone()
                })
            };
            let mut equations = vec![
                a[X].clone() - packed(BITS, 10, true),
                a[LOW].clone() - packed(BITS, 6, true),
                a[HIGH].clone() - packed(BITS + 6, 4, true),
                a[WEIGHT].clone() - packed(BITS, 10, false),
                a[X].clone() - constant(7) * a[Q7].clone() - a[R7].clone(),
                a[LOW].clone() - constant(9) * a[Q9].clone() - a[LO].clone(),
                a[HI].clone() * (a[HI].clone() - constant(1)),
                a[DIFFERENCE].clone() - packed(DIFFERENCE_BITS, 10, true),
                a[DIFFERENCE].clone()
                    - a[HI].clone() * (a[X].clone() - constant(601))
                    - (constant(1) - a[HI].clone()) * (constant(600) - a[X].clone()),
            ];
            for start in [BITS, DIFFERENCE_BITS] {
                for bit in 0..10 {
                    let b = a[start + bit].clone();
                    equations.push(b.clone() * (b - constant(1)));
                }
            }
            equations
                .into_iter()
                .map(|e| q.clone() * e)
                .collect::<Vec<_>>()
        });
        for (column, table) in [Q7, Q9, R7, LO].into_iter().zip(tables) {
            meta.lookup(|meta| {
                let q = meta.query_selector(selectors[0]);
                vec![(
                    q * meta.query_advice(advice[column], Rotation::cur()),
                    table,
                )]
            });
        }
        meta.lookup(|meta| {
            let q = meta.query_selector(selectors[0]);
            // One tuple membership: projecting its columns separately loses the tier correlation.
            vec![
                (
                    q.clone() * meta.query_advice(advice[HIGH], Rotation::cur()),
                    tables[4],
                ),
                (
                    q * meta.query_advice(advice[TIER], Rotation::cur()),
                    tables[5],
                ),
            ]
        });
        if let Some(table) = seed_table {
            meta.lookup(|meta| {
                let q = meta.query_selector(selectors[1]);
                vec![(q * meta.query_advice(advice[S], Rotation::cur()), table)]
            });
        }
        meta.create_gate("expanded calibration and zero correction", |meta| {
            let q = meta.query_selector(selectors[1]);
            let s = meta.query_advice(advice[S], Rotation::cur());
            let h = meta.query_advice(advice[H], Rotation::cur());
            let p = meta.query_advice(advice[PRODUCT], Rotation::cur());
            let five = meta.query_fixed(bias);
            vec![
                q.clone() * (s.clone() * s.clone() - constant(10) * s.clone() + p),
                q * h * (s - five),
            ]
        });
        meta.create_gate("previous-row private score and correction", |meta| {
            let q = meta.query_selector(selectors[2]);
            vec![
                q * (meta.query_advice(advice[T], Rotation::cur())
                    - meta.query_advice(advice[X], Rotation::prev())
                    - meta.query_advice(advice[H], Rotation::prev())),
            ]
        });
        meta.create_gate("previous-row corrected score", |meta| {
            let q = meta.query_selector(selectors[3]);
            vec![
                q * (meta.query_advice(advice[U], Rotation::cur())
                    - constant(2) * meta.query_advice(advice[T], Rotation::prev())
                    - constant(1)),
            ]
        });
        RiskAuditConfig {
            advice,
            public,
            bias,
            selectors,
            tables,
            seed_table,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "quotient ranges and correlated tiers",
            |mut table| {
                for row in 0..147 {
                    let index = row % 16;
                    let values = [
                        row as u64,
                        (row % 8) as u64,
                        (row % 7) as u64,
                        (row % 9) as u64,
                        index as u64,
                        TIERS[index],
                    ];
                    for (column, value) in config.tables.into_iter().zip(values) {
                        table.assign_cell(
                            || "allowed value",
                            column,
                            row,
                            || Value::known(Fr::from(value)),
                        )?;
                    }
                    if let Some(column) = config.seed_table {
                        table.assign_cell(
                            || "initial calibration superset",
                            column,
                            row,
                            || Value::known(Fr::from(index as u64)),
                        )?;
                    }
                }
                Ok(())
            },
        )?;
        let exposed = layouter.assign_region(
            || "risk audit with rotated dependencies",
            |mut region| {
                for (row, selector) in config.selectors.into_iter().enumerate() {
                    selector.enable(&mut region, row)?;
                }
                let mut cells = Vec::new();
                let x = region.assign_advice(
                    || "private score",
                    config.advice[X],
                    0,
                    || Value::known(Fr::from(self.values[X])),
                )?;
                x.copy_advice(
                    || "same score at calibration row",
                    &mut region,
                    config.advice[X],
                    1,
                )?;
                for column in (BITS..=LO).chain(DIFFERENCE..COLUMNS) {
                    let cell = region.assign_advice(
                        || "risk computation",
                        config.advice[column],
                        0,
                        || Value::known(Fr::from(self.values[column])),
                    )?;
                    if PUBLIC_COLUMNS[..PUBLISHED].contains(&column) {
                        cells.push(cell);
                    }
                }
                region.assign_fixed(
                    || "fixed correction bias",
                    config.bias,
                    1,
                    || Value::known(Fr::from(5)),
                )?;
                for column in [S, H, PRODUCT] {
                    let cell = region.assign_advice(
                        || "private calibration or public product",
                        config.advice[column],
                        1,
                        || Value::known(Fr::from(self.values[column])),
                    )?;
                    if column == PRODUCT {
                        cells.push(cell);
                    }
                }
                for (column, row) in [(T, 2), (U, 3)] {
                    region.assign_advice(
                        || "private derived target",
                        config.advice[column],
                        row,
                        || Value::known(Fr::from(self.values[column])),
                    )?;
                }
                Ok(cells)
            },
        )?;
        for (row, cell) in exposed.into_iter().enumerate() {
            layouter.constrain_instance(cell.cell(), config.public, row)?;
        }
        Ok(())
    }
}

fn targets() -> Vec<CellId> {
    [(X, 0), (S, 1), (H, 1), (T, 2), (U, 3)]
        .map(|(column, row)| CellId::advice(column, row))
        .to_vec()
}

fn expected_projection(cell: &CellId, xs: &[u64]) -> BTreeSet<BigInt> {
    let cells = targets();
    let index = cells.iter().position(|v| v == cell).unwrap();
    match index {
        0 | 3 => xs.iter().copied().map(BigInt::from).collect(),
        1 => [3, 7].into_iter().map(BigInt::from).collect(),
        2 => [BigInt::from(0)].into(),
        4 => xs.iter().map(|x| BigInt::from(2 * x + 1)).collect(),
        _ => unreachable!(),
    }
}

fn domain_values(domain: &UcpValueDomain) -> BTreeSet<BigInt> {
    match domain {
        UcpValueDomain::Exact(value) => [value.clone()].into(),
        UcpValueDomain::FiniteSet(values) => values.clone(),
    }
}

fn kernel<const PUBLISHED: usize, const SEEDED: bool>(
    circuit: &RiskAuditCircuit<PUBLISHED, SEEDED>,
) -> UcpResult {
    kernel_with_calibration_domain(circuit, None)
}

fn kernel_with_calibration_domain<const PUBLISHED: usize, const SEEDED: bool>(
    circuit: &RiskAuditCircuit<PUBLISHED, SEEDED>,
    calibration_domain: Option<UcpValueDomain>,
) -> UcpResult {
    let analyzable =
        crate::circuit_analyzer::analyzable::Analyzable::<Fr>::config_and_synthesize(circuit, K)
            .unwrap();
    let problem = crate::circuit_analyzer::ucp::extractor::extract_ucp_problem(&analyzable);
    let mut values = problem.initial_value_facts.clone();
    for (row, value) in circuit.instances()[0].iter().enumerate() {
        values.mark_known(
            CellId::instance(0, row as i32),
            crate::circuit_analyzer::ucp::plonkish::field_to_bigint(value),
        );
    }
    if let Some(domain) = calibration_domain {
        values.mark_domain(CellId::advice(S, 1), domain);
    }
    problem.analyze_with_values(problem.initial_facts.clone(), values)
}

#[test]
fn demo_risk_audit_reference_and_constraint_checks() {
    assert_eq!(disclosures(713), [2, 1, 6, 5, 0]);
    assert_eq!(
        array::from_fn::<_, 6, _>(|n| reference_candidates(n).len()),
        [1024, 320, 167, 24, 4, 1]
    );
    assert_eq!(reference_candidates(4), [601, 678, 692, 713]);
    assert_eq!(reference_candidates(5), [713]);

    fn check<const PUBLISHED: usize, const SEEDED: bool>() {
        let instances = RiskAuditCircuit::<PUBLISHED, SEEDED>::new(713, 3).instances();
        for x in reference_candidates(PUBLISHED) {
            for s in [3, 7] {
                MockProver::run(
                    K,
                    &RiskAuditCircuit::<PUBLISHED, SEEDED>::new(x, s),
                    instances.clone(),
                )
                .unwrap()
                .assert_satisfied();
            }
        }
        let circuit = RiskAuditCircuit::<PUBLISHED, SEEDED>::new(713, 3);
        for x in [0, 447, 448, 600, 601, 678, 692, 713, 714, 767, 768, 1023] {
            let accepted = MockProver::run(
                K,
                &RiskAuditCircuit::<PUBLISHED, SEEDED>::new(x, 3),
                instances.clone(),
            )
            .unwrap()
            .verify()
            .is_ok();
            assert_eq!(accepted, reference_candidates(PUBLISHED).contains(&x));
        }
        let mut bad_tier = circuit.clone();
        bad_tier.values[TIER] = 3;
        // Both 11 and 3 occur in their table columns, but the tuple (11,3) does not.
        assert!(MockProver::run(K, &bad_tier, bad_tier.instances())
            .unwrap()
            .verify()
            .is_err());
        // Each mutation violates a distinct constraint; no mutation changes the public observations.
        for column in [
            X,
            BITS,
            LOW,
            HIGH,
            TIER,
            HI,
            R7,
            WEIGHT,
            LO,
            Q7,
            Q9,
            DIFFERENCE,
            DIFFERENCE_BITS,
            S,
            H,
            T,
            U,
            PRODUCT,
        ]
        .into_iter()
        .chain((1..10).map(|bit| BITS + bit))
        .chain((1..10).map(|bit| DIFFERENCE_BITS + bit))
        {
            let mut bad = circuit.clone();
            bad.values[column] += 1;
            assert!(
                MockProver::run(K, &bad, instances.clone())
                    .unwrap()
                    .verify()
                    .is_err(),
                "unchecked column {column}"
            );
        }
        for x in [0, 600, 601, 1023] {
            let boundary = RiskAuditCircuit::<PUBLISHED, SEEDED>::new(x, 7);
            MockProver::run(K, &boundary, boundary.instances())
                .unwrap()
                .assert_satisfied();
        }
        let mut bad_remainder = circuit.clone();
        bad_remainder.values[Q7] -= 1;
        bad_remainder.values[R7] += 7;
        assert!(MockProver::run(K, &bad_remainder, instances.clone())
            .unwrap()
            .verify()
            .is_err());
        let mut bad_low = circuit.clone();
        bad_low.values[Q9] -= 1;
        bad_low.values[LO] += 9;
        assert!(MockProver::run(K, &bad_low, instances)
            .unwrap()
            .verify()
            .is_err());
    }
    check::<4, false>();
    check::<5, false>();
    check::<4, true>();
    check::<5, true>();
}

#[test]
fn demo_risk_audit_ucp_kernel_is_sound_and_witness_independent() {
    fn check<const PUBLISHED: usize, const SEEDED: bool>() {
        let circuit = RiskAuditCircuit::<PUBLISHED, SEEDED>::new(713, 3);
        MockProver::run(K, &circuit, circuit.instances())
            .unwrap()
            .assert_satisfied();
        let propagated = kernel(&circuit);
        let xs = reference_candidates(PUBLISHED);
        let alternate = kernel(&RiskAuditCircuit::<PUBLISHED, SEEDED>::new(xs[0], 7));
        for cell in targets() {
            let domain = propagated.value_facts.domain(&cell);
            println!(
                "Risk audit: published={PUBLISHED}, seeded={SEEDED}; UCP {cell}: {}",
                short_demo_domain(domain)
            );
            let feasible = expected_projection(&cell, &xs);
            if cell == CellId::advice(X, 0) {
                assert_eq!(domain.map(domain_values), Some(feasible.clone()));
            }
            if let Some(domain) = domain {
                assert!(feasible.is_subset(&domain_values(domain)));
            }
            if propagated.facts.is_unique(&cell) {
                assert_eq!(feasible.len(), 1);
            }
            assert_eq!(domain, alternate.value_facts.domain(&cell));
            assert_eq!(
                propagated.facts.is_unique(&cell),
                alternate.facts.is_unique(&cell)
            );
        }
        assert_eq!(
            propagated
                .value_facts
                .known_value(&CellId::advice(PRODUCT, 1)),
            Some(&BigInt::from(21))
        );
        if SEEDED {
            assert!(propagated
                .value_facts
                .domain(&CellId::advice(S, 1))
                .is_some());
        } else {
            assert!(propagated
                .value_facts
                .domain(&CellId::advice(S, 1))
                .is_none());
        }
    }
    check::<4, false>();
    check::<5, false>();
    check::<4, true>();
    check::<5, true>();
}

#[test]
fn demo_risk_audit_conditional_domain_feedback_reaches_rotated_targets() {
    let circuit = RiskAuditCircuit::<5, false>::new(713, 3);
    let before = kernel(&circuit);
    assert!(before.value_facts.domain(&CellId::advice(H, 1)).is_none());
    // Unit-test premise, proved algebraically by (s-3)(s-7)=0; not an SMT measurement.
    let roots = UcpValueDomain::finite_set([3, 7].map(BigInt::from)).unwrap();
    let after = kernel_with_calibration_domain(&circuit, Some(roots));
    assert_eq!(
        after.value_facts.known_value(&CellId::advice(H, 1)),
        Some(&BigInt::from(0))
    );
    assert!(after.facts.is_unique(&CellId::advice(H, 1)));
    assert_eq!(
        after.value_facts.domain(&CellId::advice(X, 0)),
        after.value_facts.domain(&CellId::advice(T, 2))
    );
    let corrected = domain_values(after.value_facts.domain(&CellId::advice(T, 2)).unwrap());
    let derived: BTreeSet<_> = corrected.into_iter().map(|x| 2 * x + 1).collect();
    assert_eq!(
        domain_values(after.value_facts.domain(&CellId::advice(U, 3)).unwrap()),
        derived
    );
    println!("Conditional feedback: proved s in {{3,7}} -> h=0 -> domains cross the copy and previous-row queries.");
}

fn timeout_ms(default_ms: u64) -> u64 {
    let timeout = std::env::var("UCP_RISK_TIMEOUT_MS")
        .map_or(default_ms, |v| v.parse().expect("positive timeout in ms"));
    assert!(timeout > 0);
    timeout
}

fn options(seeded: bool, checks: usize, bridges: usize) -> PrivacyAnalysisOptions {
    PrivacyAnalysisOptions {
        compute_structural_baseline: false,
        max_semantic_queries: 0,
        solver_timeout_ms: Some(timeout_ms(2_000)),
        initial_sat_timeout_ms: None,
        search: crate::circuit_analyzer::ucp::privacy::PrivacySearchOptions {
            max_bridge_queries: bridges,
            max_retries_per_target: 0,
            retry_solver_timeout_ms: None,
            ..Default::default()
        },
        domain_refinement: PrivacyDomainRefinementOptions {
            max_solver_checks: if seeded { checks } else { 0 },
            max_candidates_per_cell: 16,
        },
        domain_discovery: PrivacyDomainDiscoveryOptions {
            max_solver_checks: if seeded { 0 } else { checks },
            max_values_per_cell: 4,
            max_retries_per_cell: 0,
            use_targeted_subsets: true,
            ..Default::default()
        },
    }
}

fn large_limits_options() -> PrivacyAnalysisOptions {
    let mut options = options(false, 128, 32);
    options.solver_timeout_ms = Some(timeout_ms(120_000));
    options.max_semantic_queries = 32;
    options.search.max_queries_without_progress = 64;
    options.domain_refinement = PrivacyDomainRefinementOptions {
        max_solver_checks: 512,
        max_candidates_per_cell: 256,
    };
    options.domain_discovery.max_values_per_cell = 16;
    options
}

fn run<const PUBLISHED: usize, const SEEDED: bool>(
    checks: usize,
    bridge_only: bool,
) -> PrivacyAnalysisReport {
    run_with_options::<PUBLISHED, SEEDED>(
        options(SEEDED, checks, if bridge_only { checks } else { 0 }),
        bridge_only,
    )
}

fn run_with_options<const PUBLISHED: usize, const SEEDED: bool>(
    options: PrivacyAnalysisOptions,
    bridge_only: bool,
) -> PrivacyAnalysisReport {
    let circuit = RiskAuditCircuit::<PUBLISHED, SEEDED>::new(713, 3);
    let selected = if bridge_only {
        targets()[3..].to_vec()
    } else {
        targets()
    };
    let mut report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &circuit.input(),
        selected,
        options,
    )
    .unwrap();
    print_privacy_demo(&format!("Risk audit: published={PUBLISHED}, seeded={SEEDED}, bridge_only={bridge_only}; semantic/refinement/discovery budgets={}/{}/{}:", options.max_semantic_queries, options.domain_refinement.max_solver_checks, options.domain_discovery.max_solver_checks), &report);
    println!(
        "Propagation runs: {}; bridge domain checks: {}; timeout ms/invocation: {:?}",
        report.search_statistics.propagation_runs,
        report.search_statistics.bridge_domain_checks,
        options.solver_timeout_ms
    );
    assert_ne!(report.status, PrivacyAnalysisStatus::Inconsistent);
    let xs = reference_candidates(PUBLISHED);
    for cell in &report.cells {
        let feasible = expected_projection(&cell.cell, &xs);
        if let Some(domain) = &cell.domain {
            let recorded = domain_values(domain);
            assert!(
                feasible.is_subset(&recorded),
                "domain lost feasible values for {}",
                cell.cell
            );
            if cell.domain_is_complete {
                assert_eq!(recorded, feasible);
            }
        } else {
            assert!(!cell.domain_is_complete);
        }
        match cell.uniqueness {
            PrivateCellUniqueness::Unique => assert_eq!(feasible.len(), 1),
            PrivateCellUniqueness::NonUnique => assert!(feasible.len() > 1),
            PrivateCellUniqueness::Unknown => {}
        }
    }
    if report.ucp_result.is_none() {
        assert_eq!(report.status, PrivacyAnalysisStatus::SolverUnknown);
        assert!(report.cells.iter().all(|cell| cell.domain.is_none()));
        println!("Initial SAT incomplete: no recovery claim was established.");
    }
    println!(
        "RISK_AUDIT_RESULT published={PUBLISHED} seeded={SEEDED} bridge_only={bridge_only} status={:?} elapsed_ms={} initial_sat_checks={} semantic_attempts={} refinement_checks={} discovery_checks={} exact={} complete={}",
        report.status, report.elapsed.as_millis(), report.satisfiability_checks,
        report.semantic_queries, report.domain_refinement_statistics.solver_checks,
        report.domain_discovery_statistics.solver_checks, report.summary.exact_values,
        report.cells.iter().filter(|cell| cell.domain_is_complete).count()
    );
    if std::env::var("UCP_RISK_VALIDATE").is_ok_and(|value| value == "1") {
        validate_claims(&circuit, &mut report);
    }
    report
}

fn validate_claims<const PUBLISHED: usize, const SEEDED: bool>(
    circuit: &RiskAuditCircuit<PUBLISHED, SEEDED>,
    report: &mut PrivacyAnalysisReport,
) {
    let Some(index) = report.cells.iter().position(|cell| cell.domain.is_some()) else {
        println!("Fresh validation skipped: no domain claim to check.");
        return;
    };
    let timeout = std::env::var("UCP_RISK_VALIDATION_TIMEOUT_MS")
        .ok()
        .map(|v| {
            let value = v.parse::<u64>().expect("positive validation timeout in ms");
            assert!(value > 0);
            value
        });
    let original_domain = report.cells[index].domain.clone();
    for negative in [false, true] {
        if negative {
            // Every selected cell's true projection consists of small nonnegative integers.
            report.cells[index].domain = Some(UcpValueDomain::exact(BigInt::from(-1)));
        }
        match validate_private_recovery_report_with_timeout::<Fr, _>(
            circuit,
            K,
            &circuit.input(),
            report,
            timeout,
        ) {
            Ok(validation) => {
                print_validation_demo(
                    if negative {
                        "Fresh check of an intentionally false risk-audit domain:"
                    } else {
                        "Fresh check of risk-audit covering domains:"
                    },
                    &validation,
                );
                assert_eq!(
                    validation.status,
                    if negative {
                        RecoveryValidationStatus::Refuted
                    } else {
                        RecoveryValidationStatus::VerifiedDomains
                    }
                );
                if negative {
                    let counterexample = validation.cells[index].counterexample.as_ref().unwrap();
                    assert!(expected_projection(
                        &report.cells[index].cell,
                        &reference_candidates(PUBLISHED)
                    )
                    .contains(counterexample));
                }
            }
            Err(error)
                if error
                    .downcast_ref::<crate::smt_solver::smt_parser::UnknownSolverResult>()
                    .is_some() =>
            {
                println!("Fresh risk-audit validation incomplete (negative={negative}): {error:#}");
            }
            Err(error) => panic!("Risk-audit validation failed: {error:#}"),
        }
    }
    report.cells[index].domain = original_domain;
}

#[test]
fn demo_risk_audit_bounded_recovery_preserves_sound_claims() {
    // A bounded solver outcome is allowed to be inconclusive, never fabricated as recovery.
    run::<4, false>(4, false);
    run::<5, true>(18, false);
}

#[test]
fn demo_risk_audit_large_limits_configuration() {
    let options = large_limits_options();
    assert_eq!(options.solver_timeout_ms, Some(timeout_ms(120_000)));
    assert_eq!(options.max_semantic_queries, 32);
    assert_eq!(options.search.max_bridge_queries, 32);
    assert_eq!(options.search.max_queries_without_progress, 64);
    assert_eq!(options.domain_refinement.max_solver_checks, 512);
    assert_eq!(options.domain_refinement.max_candidates_per_cell, 256);
    assert_eq!(options.domain_discovery.max_solver_checks, 128);
    assert_eq!(options.domain_discovery.max_values_per_cell, 16);
    assert!(
        options.domain_refinement.max_candidates_per_cell
            <= crate::circuit_analyzer::ucp::value::MAX_FINITE_DOMAIN_SIZE
    );
}

#[test]
#[ignore = "Large risk-audit allowances (120 seconds per invocation); run explicitly and serially"]
fn demo_risk_audit_large_limits() {
    run_with_options::<5, false>(large_limits_options(), false);
}

#[test]
#[ignore = "Serial risk-audit experiments; set UCP_RISK_TIMEOUT_MS and run with --nocapture"]
fn demo_risk_audit_measurement_matrix() {
    // Same task and timeout within each pair; these are ablations, not an SMT-only benchmark.
    run::<4, false>(0, false);
    run::<4, false>(24, false);
    run::<5, false>(0, false);
    run::<5, false>(24, false);
    run::<4, true>(0, false);
    run::<4, true>(32, false);
    run::<5, true>(0, false);
    run::<5, true>(32, false);
    run::<5, false>(24, true);
    let mut fast_probe = options(false, 0, 0);
    fast_probe.max_semantic_queries = 8;
    run_with_options::<5, false>(fast_probe, false);
    let mut combined = options(false, 24, 8);
    combined.max_semantic_queries = 8;
    combined.domain_refinement = PrivacyDomainRefinementOptions {
        max_solver_checks: 160,
        max_candidates_per_cell: 147,
    };
    run_with_options::<4, false>(combined, false);
    run_with_options::<5, false>(combined, false);
}
