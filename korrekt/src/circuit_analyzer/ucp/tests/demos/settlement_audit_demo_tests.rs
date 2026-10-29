//! Többfázisú elszámolási példa valódi UCP/SMT-visszacsatolással.
//! A teszt referenciája nem kerül az elemző premisszái közé; csak az eredményt ellenőrzi.

use super::{
    all_but_one::infer_all_but_one_zero_with_modulus,
    cell::CellId,
    extractor::extract_ucp_problem,
    facts::UcpFacts,
    privacy::{
        analyze_private_recoverability, PrivacyAnalysisOptions, PrivacyAnalysisReport,
        PrivacyAnalysisStatus, PrivacySearchOptions, PrivateCellUniqueness,
    },
    privacy_discovery::PrivacyDomainDiscoveryOptions,
    privacy_domain::PrivacyDomainRefinementOptions,
    privacy_validation::{validate_private_recovery_report, RecoveryValidationStatus},
    value::{UcpValueDomain, UcpValueFacts},
};
use crate::{
    circuit_analyzer::{
        analyzable::Analyzable,
        analyzer::{Analyzer, SemanticQueryResult},
        halo2_proofs_libs::*,
    },
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerType, LookupMethod, VerificationInput, VerificationMethod,
    },
    smt_solver::{process::invocation_count, smt_parser::Satisfiability},
};
use num_bigint::BigInt;
use std::{array, collections::BTreeSet, time::Instant};

const K: u32 = 7;
const A: usize = 0;
const B: usize = 1;
const ROUTE: usize = 2;
const PLAN: usize = 3;
const CODE: usize = 4;
const MASK: usize = 5;
const AMOUNT: usize = 6;
const BITS_START: usize = 7;

#[derive(Clone, Copy)]
struct Layout {
    fee: usize,
    other_fee: usize,
    buckets: usize,
    public: [usize; 5],
    derived: usize,
}

fn layout(bits: usize) -> Layout {
    let fee = BITS_START + bits;
    let buckets = fee + 2;
    let public = array::from_fn(|i| buckets + 4 + i);
    Layout {
        fee,
        other_fee: fee + 1,
        buckets,
        derived: public[4] + 1,
        public,
    }
}

fn field(value: i64) -> Fr {
    let magnitude = Fr::from(value.unsigned_abs());
    if value < 0 {
        -magnitude
    } else {
        magnitude
    }
}

#[derive(Clone)]
struct SettlementAudit<const BITS: usize, const LINKS: usize, const SEEDED: bool, const LEAK: bool>
{
    values: Vec<i64>,
    chain: Vec<i64>,
}

impl<const BITS: usize, const LINKS: usize, const SEEDED: bool, const LEAK: bool>
    SettlementAudit<BITS, LINKS, SEEDED, LEAK>
{
    fn new() -> Self {
        Self::witness((1 << (BITS - 1)) + 117, 3, 60, 0)
    }

    fn witness(amount: i64, code: i64, fee: i64, mask: i64) -> Self {
        assert!((9..=16).contains(&BITS));
        assert!((1..=16).contains(&LINKS));
        assert!((0..1 << BITS).contains(&amount));
        let l = layout(BITS);
        let mut values = vec![0; l.derived + 1];
        values[A] = 80;
        values[B] = 30;
        values[ROUTE] = 2;
        values[PLAN] = 1;
        values[CODE] = code;
        values[MASK] = mask;
        values[AMOUNT] = amount;
        for bit in 0..BITS {
            values[BITS_START + bit] = (amount >> bit) & 1;
        }
        values[l.fee] = fee;
        values[l.other_fee] = 100 - fee;
        values[l.buckets + 2] = values[A];
        for (column, value) in l.public.into_iter().zip([190, 170, amount + mask, 21, 100]) {
            values[column] = value;
        }
        let mut chain = Vec::with_capacity(LINKS);
        let mut next = 80 * amount + 30;
        for _ in 0..LINKS {
            chain.push(next);
            next = next.checked_mul(2).unwrap().checked_add(1).unwrap();
        }
        Self { values, chain }
    }

    fn public_values(&self) -> Vec<i64> {
        let l = layout(BITS);
        l.public
            .into_iter()
            .map(|column| self.values[column])
            .chain([self.values[PLAN]])
            .collect()
    }

    fn instances(&self) -> Vec<Vec<Fr>> {
        vec![self.public_values().into_iter().map(field).collect()]
    }

    fn input(&self) -> AnalyzerInput {
        AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput::new(
                self.public_values()
                    .into_iter()
                    .enumerate()
                    .map(|(row, value)| (format!("I-0-{row}"), value)),
                1,
            ),
            lookup_method: LookupMethod::InlineConstraints,
        }
    }

    fn targets() -> Vec<CellId> {
        let l = layout(BITS);
        [A, B, ROUTE, CODE, MASK, AMOUNT, l.fee, l.other_fee]
            .into_iter()
            .chain(BITS_START..BITS_START + BITS)
            .chain(l.buckets..l.buckets + 4)
            .map(|column| CellId::advice(column, 0))
            .chain((0..LINKS).map(|i| CellId::advice(l.derived, (i + 2) as i32)))
            .collect()
    }
}

#[derive(Clone)]
struct SettlementConfig {
    advice: Vec<Column<Advice>>,
    public: Column<Instance>,
    bias: Column<Fixed>,
    selectors: [Selector; 3],
    tables: [TableColumn; 4],
    seed: Option<TableColumn>,
}

impl<const BITS: usize, const LINKS: usize, const SEEDED: bool, const LEAK: bool> Circuit<Fr>
    for SettlementAudit<BITS, LINKS, SEEDED, LEAK>
{
    type Config = SettlementConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let l = layout(BITS);
        let advice: Vec<_> = (0..=l.derived).map(|_| meta.advice_column()).collect();
        let public = meta.instance_column();
        let bias = meta.fixed_column();
        let selectors: [_; 3] = array::from_fn(|_| meta.complex_selector());
        let tables = array::from_fn(|_| meta.lookup_table_column());
        let seed = SEEDED.then(|| meta.lookup_table_column());
        meta.enable_equality(public);
        for column in [A, B, AMOUNT, PLAN].into_iter().chain(l.public) {
            meta.enable_equality(advice[column]);
        }
        let c = |value| Expression::Constant(Fr::from(value));
        meta.create_gate("settlement equations and hidden correction", |meta| {
            let q = meta.query_selector(selectors[0]);
            let a: Vec<_> = advice
                .iter()
                .take(l.derived)
                .map(|column| meta.query_advice(*column, Rotation::cur()))
                .collect();
            let packed = (0..BITS).fold(c(0), |sum, bit| {
                sum + c(1 << bit) * a[BITS_START + bit].clone()
            });
            let mut equations = vec![
                c(2) * a[A].clone() + a[B].clone() - a[l.public[0]].clone(),
                a[A].clone() + c(3) * a[B].clone() - a[l.public[1]].clone(),
                a[AMOUNT].clone() + a[MASK].clone() - a[l.public[2]].clone(),
                // A kifejtett polinomot adja át; a gyököket nem írja elő külön kényszerként.
                a[CODE].clone() * a[CODE].clone() - c(10) * a[CODE].clone()
                    + a[l.public[3]].clone(),
                a[l.fee].clone() + a[l.other_fee].clone() - a[l.public[4]].clone(),
                a[AMOUNT].clone() - packed,
                (0..4).fold(c(0), |sum, i| sum + a[l.buckets + i].clone()) - a[A].clone(),
            ];
            for bit in 0..BITS {
                let b = a[BITS_START + bit].clone();
                equations.push(b.clone() * (b - c(1)));
            }
            for i in 0..4 {
                equations.push(a[l.buckets + i].clone() * (a[ROUTE].clone() - c(i as u64)));
            }
            if LEAK {
                // A szivárgó változat a tarifakódhoz köti a maszkolási korrekciót.
                equations.push(a[MASK].clone() * (a[CODE].clone() - meta.query_fixed(bias)));
            }
            equations
                .into_iter()
                .map(|e| q.clone() * e)
                .collect::<Vec<_>>()
        });
        meta.lookup(|meta| {
            let q = meta.query_selector(selectors[0]);
            vec![
                (
                    q.clone() * meta.query_advice(advice[ROUTE], Rotation::cur()),
                    tables[0],
                ),
                (
                    q * meta.query_advice(advice[PLAN], Rotation::cur()),
                    tables[1],
                ),
            ]
        });
        for (column, table, fallback) in [(l.fee, tables[2], 10), (l.other_fee, tables[3], 20)] {
            meta.lookup(|meta| {
                let q = meta.query_selector(selectors[0]);
                // Az inaktív sor bemenetét valódi táblabejegyzésre állítja.
                vec![(
                    q * (meta.query_advice(advice[column], Rotation::cur()) - c(fallback))
                        + c(fallback),
                    table,
                )]
            });
        }
        if let Some(table) = seed {
            meta.lookup(|meta| {
                let q = meta.query_selector(selectors[0]);
                vec![(q * meta.query_advice(advice[CODE], Rotation::cur()), table)]
            });
        }
        meta.create_gate("copied previous-row amount", |meta| {
            let q = meta.query_selector(selectors[1]);
            vec![
                q * (meta.query_advice(advice[l.derived], Rotation::cur())
                    - meta.query_advice(advice[A], Rotation::prev())
                        * meta.query_advice(advice[AMOUNT], Rotation::prev())
                    - meta.query_advice(advice[B], Rotation::prev())),
            ]
        });
        meta.create_gate("rotated dependent audit chain", |meta| {
            let q = meta.query_selector(selectors[2]);
            vec![
                q * (meta.query_advice(advice[l.derived], Rotation::cur())
                    - c(2) * meta.query_advice(advice[l.derived], Rotation::prev())
                    - c(1)),
            ]
        });
        SettlementConfig {
            advice,
            public,
            bias,
            selectors,
            tables,
            seed,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let l = layout(BITS);
        layouter.assign_table(
            || "tariff pairs and finite catalogs",
            |mut table| {
                for row in 0..16 {
                    let pair = [(0, 0), (1, 0), (2, 1), (3, 2)][row % 4];
                    let values = [
                        pair.0,
                        pair.1,
                        10 * (row as u64 % 9 + 1),
                        20 * (row as u64 % 3 + 1),
                    ];
                    for (column, value) in config.tables.into_iter().zip(values) {
                        table.assign_cell(
                            || "allowed table entry",
                            column,
                            row,
                            || Value::known(Fr::from(value)),
                        )?;
                    }
                    if let Some(column) = config.seed {
                        table.assign_cell(
                            || "initial code superset",
                            column,
                            row,
                            || Value::known(Fr::from(row as u64)),
                        )?;
                    }
                }
                Ok(())
            },
        )?;
        let exposed = layouter.assign_region(
            || "settlement with rotated feedback chain",
            |mut region| {
                config.selectors[0].enable(&mut region, 0)?;
                config.selectors[1].enable(&mut region, 2)?;
                for row in 3..=LINKS + 1 {
                    config.selectors[2].enable(&mut region, row)?;
                }
                region.assign_fixed(
                    || "correction pivot",
                    config.bias,
                    0,
                    || Value::known(Fr::from(5)),
                )?;
                let mut cells = Vec::new();
                for column in 0..l.derived {
                    cells.push(region.assign_advice(
                        || "private or exposed settlement value",
                        config.advice[column],
                        0,
                        || Value::known(field(self.values[column])),
                    )?);
                }
                for column in [A, B, AMOUNT] {
                    cells[column].copy_advice(
                        || "same value on the preceding row",
                        &mut region,
                        config.advice[column],
                        1,
                    )?;
                }
                for (i, value) in self.chain.iter().enumerate() {
                    region.assign_advice(
                        || "derived private audit value",
                        config.advice[l.derived],
                        i + 2,
                        || Value::known(field(*value)),
                    )?;
                }
                Ok(l.public
                    .into_iter()
                    .chain([PLAN])
                    .map(|column| cells[column].clone())
                    .collect::<Vec<_>>())
            },
        )?;
        for (row, cell) in exposed.iter().enumerate() {
            layouter.constrain_instance(cell.cell(), config.public, row)?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
enum Profile {
    Propagation,
    FastProbe,
    Refinement,
    Discovery,
    Combined,
}

fn options(profile: Profile) -> PrivacyAnalysisOptions {
    PrivacyAnalysisOptions {
        max_semantic_queries: if matches!(profile, Profile::FastProbe | Profile::Combined) {
            16
        } else {
            0
        },
        solver_timeout_ms: Some(5_000),
        initial_sat_timeout_ms: None,
        search: PrivacySearchOptions {
            max_bridge_queries: 0,
            retry_solver_timeout_ms: None,
            ..Default::default()
        },
        domain_refinement: PrivacyDomainRefinementOptions {
            max_solver_checks: if matches!(profile, Profile::Refinement | Profile::Combined) {
                96
            } else {
                0
            },
            max_candidates_per_cell: 16,
        },
        domain_discovery: PrivacyDomainDiscoveryOptions {
            max_solver_checks: if matches!(profile, Profile::Discovery | Profile::Combined) {
                48
            } else {
                0
            },
            max_values_per_cell: 4,
            max_retries_per_cell: 0,
            ..Default::default()
        },
    }
}

fn entries(domain: &UcpValueDomain) -> BTreeSet<BigInt> {
    match domain {
        UcpValueDomain::Exact(value) => [value.clone()].into(),
        UcpValueDomain::FiniteSet(values) => values.clone(),
    }
}

fn cell(report: &PrivacyAnalysisReport, id: CellId) -> &super::privacy::PrivateCellReport {
    report.cells.iter().find(|item| item.cell == id).unwrap()
}

// A referencia a tarifapolinom gyökeit és a két katalógus metszetét külön számítja ki.
fn reference(column: usize, l: Layout) -> Option<BTreeSet<BigInt>> {
    if column == CODE {
        Some(
            (0i64..16)
                .filter(|s| s * (10 - s) == 21)
                .map(BigInt::from)
                .collect(),
        )
    } else if column == l.fee || column == l.other_fee {
        Some(
            (10..=90)
                .step_by(10)
                .filter(|y| [20, 40, 60].contains(&(100 - y)))
                .map(|y| BigInt::from(if column == l.fee { y } else { 100 - y }))
                .collect(),
        )
    } else {
        None
    }
}

fn check_leaking_report<const BITS: usize, const LINKS: usize, const SEEDED: bool>(
    circuit: &SettlementAudit<BITS, LINKS, SEEDED, true>,
    report: &PrivacyAnalysisReport,
) {
    check_sound_claims(circuit, report);
    let l = layout(BITS);
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    for item in &report.cells {
        let expected = if item.cell.row == 0 {
            reference(item.cell.column, l)
                .unwrap_or_else(|| [BigInt::from(circuit.values[item.cell.column])].into())
        } else {
            [BigInt::from(circuit.chain[item.cell.row as usize - 2])].into()
        };
        assert_eq!(
            entries(item.domain.as_ref().unwrap()),
            expected,
            "{}",
            item.cell
        );
        assert!(item.domain_is_complete, "{}", item.cell);
        assert_eq!(
            item.uniqueness,
            if expected.len() == 1 {
                PrivateCellUniqueness::Unique
            } else {
                PrivateCellUniqueness::NonUnique
            }
        );
    }
}

fn check_sound_claims<const BITS: usize, const LINKS: usize, const SEEDED: bool>(
    circuit: &SettlementAudit<BITS, LINKS, SEEDED, true>,
    report: &PrivacyAnalysisReport,
) {
    assert_ne!(report.status, PrivacyAnalysisStatus::Inconsistent);
    let l = layout(BITS);
    for item in &report.cells {
        let expected = if item.cell.row == 0 {
            reference(item.cell.column, l)
                .unwrap_or_else(|| [BigInt::from(circuit.values[item.cell.column])].into())
        } else {
            [BigInt::from(circuit.chain[item.cell.row as usize - 2])].into()
        };
        if let Some(domain) = &item.domain {
            assert!(expected.is_subset(&entries(domain)), "{}", item.cell);
            if item.domain_is_complete {
                assert_eq!(entries(domain), expected, "{}", item.cell);
            }
        } else {
            assert!(!item.domain_is_complete);
        }
        match item.uniqueness {
            PrivateCellUniqueness::Unique => assert_eq!(expected.len(), 1),
            PrivateCellUniqueness::NonUnique => assert!(expected.len() > 1),
            PrivateCellUniqueness::Unknown => {}
        }
    }
}

fn run<const BITS: usize, const LINKS: usize, const SEEDED: bool, const LEAK: bool>(
    circuit: &SettlementAudit<BITS, LINKS, SEEDED, LEAK>,
    profile: Profile,
) -> PrivacyAnalysisReport {
    println!("SETTLEMENT_BEGIN profile={profile:?} bits={BITS} links={LINKS} seeded={SEEDED} leak={LEAK}");
    let before = invocation_count();
    let report = analyze_private_recoverability::<Fr, _, _>(
        circuit,
        K,
        &circuit.input(),
        SettlementAudit::<BITS, LINKS, SEEDED, LEAK>::targets(),
        options(profile),
    )
    .unwrap();
    println!("SETTLEMENT profile={profile:?} bits={BITS} links={LINKS} seeded={SEEDED} leak={LEAK} status={:?} exact={} finite={} complete={} smt_invocations={} sat_checks={} semantic_attempts={} refinement_checks={} discovery_checks={} propagation_runs={} elapsed_ms={:.3}",
        report.status, report.summary.exact_values, report.summary.finite_domains,
        report.cells.iter().filter(|c| c.domain_is_complete).count(), invocation_count() - before,
        report.satisfiability_checks, report.semantic_queries, report.domain_refinement_statistics.solver_checks,
        report.domain_discovery_statistics.solver_checks, report.search_statistics.propagation_runs,
        report.elapsed.as_secs_f64() * 1000.0);
    println!(
        "SETTLEMENT_VALUES amount={:?} mask={:?} code={:?} fee={:?} final_audit={:?}",
        cell(&report, CellId::advice(AMOUNT, 0)).domain,
        cell(&report, CellId::advice(MASK, 0)).domain,
        cell(&report, CellId::advice(CODE, 0)).domain,
        cell(&report, CellId::advice(layout(BITS).fee, 0)).domain,
        cell(
            &report,
            CellId::advice(layout(BITS).derived, (LINKS + 1) as i32)
        )
        .domain
    );
    report
}

#[test]
fn settlement_audit_constraints_and_secure_control() {
    type Leaking = SettlementAudit<9, 4, true, true>;
    for code in [3, 7] {
        for fee in [40, 60, 80] {
            let circuit = Leaking::witness(373, code, fee, 0);
            zcash_halo2_proofs::dev::MockProver::run(K, &circuit, circuit.instances())
                .unwrap()
                .assert_satisfied();
        }
    }
    let circuit = Leaking::new();
    let mut wrong = circuit.clone();
    wrong.values[CODE] = 5;
    assert!(
        zcash_halo2_proofs::dev::MockProver::run(K, &wrong, circuit.instances())
            .unwrap()
            .verify()
            .is_err()
    );
    let mut wrong = circuit.clone();
    wrong.values[AMOUNT] += 1;
    assert!(
        zcash_halo2_proofs::dev::MockProver::run(K, &wrong, circuit.instances())
            .unwrap()
            .verify()
            .is_err()
    );
    type Safe = SettlementAudit<9, 4, true, false>;
    let first = Safe::witness(373, 3, 60, 0);
    let second = Safe::witness(376, 7, 80, -3);
    assert_eq!(first.public_values(), second.public_values());
    for witness in [first, second] {
        zcash_halo2_proofs::dev::MockProver::run(K, &witness, witness.instances())
            .unwrap()
            .assert_satisfied();
    }
    let longer = SettlementAudit::<9, 12, true, true>::new();
    zcash_halo2_proofs::dev::MockProver::run(K, &longer, longer.instances())
        .unwrap()
        .assert_satisfied();
    let wider = SettlementAudit::<12, 4, false, true>::new();
    zcash_halo2_proofs::dev::MockProver::run(K, &wider, wider.instances())
        .unwrap()
        .assert_satisfied();
}

#[test]
fn settlement_audit_ucp_stalls_before_nonlinear_bridge() {
    type Demo = SettlementAudit<9, 4, true, true>;
    let circuit = Demo::new();
    let analyzable = Analyzable::config_and_synthesize(&circuit, K).unwrap();
    let problem = extract_ucp_problem(&analyzable);
    let mut values = problem.initial_value_facts.clone();
    for (row, value) in circuit.public_values().into_iter().enumerate() {
        values.mark_known(CellId::instance(0, row as i32), value.into());
    }
    let before = invocation_count();
    let result = problem.analyze_with_values(problem.initial_facts.clone(), values.clone());
    assert_eq!(invocation_count(), before);
    let l = layout(9);
    for (column, value) in [(A, 80), (B, 30), (ROUTE, 2)] {
        assert_eq!(
            result.value_facts.known_value(&CellId::advice(column, 0)),
            Some(&BigInt::from(value))
        );
    }
    for i in 0..4 {
        assert_eq!(
            result
                .value_facts
                .known_value(&CellId::advice(l.buckets + i, 0)),
            Some(&BigInt::from(if i == 2 { 80 } else { 0 }))
        );
    }
    // A pontos értékek elhagyása mellett is alkalmazható az All-But-One-0 szabály,
    // mert a tényleges UCP-futás már igazolta a kiválasztó és az összeg egyértelműségét.
    let unique: UcpFacts = [CellId::advice(A, 0), CellId::advice(ROUTE, 0)]
        .into_iter()
        .collect();
    let one_hot = infer_all_but_one_zero_with_modulus(
        &problem.expressions,
        &unique,
        &UcpValueFacts::new(),
        &problem.field_modulus,
    );
    for i in 0..4 {
        assert!(one_hot
            .iter()
            .any(|inference| inference.cell == CellId::advice(l.buckets + i, 0)));
    }
    // A korrelált reláció elhagyásakor a külön oszlopdomainek nem rögzítik az útvonalat.
    let mut projected_only = problem.clone();
    projected_only.lookups.clear();
    let without_tuples =
        projected_only.analyze_with_values(projected_only.initial_facts.clone(), values);
    assert!(without_tuples
        .value_facts
        .known_value(&CellId::advice(ROUTE, 0))
        .is_none());
    assert_eq!(
        result.value_facts.domain(&CellId::advice(l.fee, 0)),
        UcpValueDomain::finite_set([40, 60, 80].map(BigInt::from)).as_ref()
    );
    assert_eq!(
        result.value_facts.domain(&CellId::advice(CODE, 0)),
        UcpValueDomain::finite_set((0..16).map(BigInt::from)).as_ref()
    );
    for bit in 0..9 {
        assert_eq!(
            result
                .value_facts
                .domain(&CellId::advice(BITS_START + bit, 0)),
            UcpValueDomain::finite_set([0, 1].map(BigInt::from)).as_ref()
        );
    }
    for id in [
        CellId::advice(AMOUNT, 0),
        CellId::advice(MASK, 0),
        CellId::advice(l.derived, 2),
    ] {
        assert!(result.value_facts.known_value(&id).is_none(), "{id}");
        assert!(!result.facts.is_unique(&id), "{id}");
    }
    println!("SETTLEMENT_UCP exact={} domains={} amount=unresolved code_domain=0..15 fee_domain=40,60,80", result.value_facts.known_values().len(), result.value_facts.domains().len());
}

#[test]
fn settlement_audit_refinement_restarts_long_ucp_chain() {
    type Demo = SettlementAudit<9, 4, true, true>;
    let circuit = Demo::new();
    let report = run(&circuit, Profile::Refinement);
    check_leaking_report(&circuit, &report);
    assert_eq!(report.semantic_queries, 0);
    assert!(report.domain_refinement_statistics.solver_checks > 0);
    assert!(report.search_statistics.propagation_runs >= 2);
    let l = layout(9);
    for id in [
        CellId::advice(AMOUNT, 0),
        CellId::advice(MASK, 0),
        CellId::advice(l.derived, 2),
    ] {
        let recovered = cell(&report, id);
        assert_eq!(recovered.query_attempts, 0);
        assert!(recovered.domain_refinement.is_none());
        assert!(recovered.domain_discovery.is_none());
    }
}

#[test]
fn settlement_audit_discovery_and_witness_independence() {
    type Demo = SettlementAudit<9, 4, false, true>;
    let circuit = Demo::new();
    let report = run(&circuit, Profile::Combined);
    check_leaking_report(&circuit, &report);
    let alternate = Demo::witness(373, 7, 80, 0);
    let repeated = run(&alternate, Profile::Combined);
    check_leaking_report(&alternate, &repeated);
    for (first, second) in report.cells.iter().zip(&repeated.cells) {
        assert_eq!(first.cell, second.cell);
        assert_eq!(first.domain, second.domain);
        assert_eq!(first.uniqueness, second.uniqueness);
    }
    assert!(report.domain_discovery_statistics.solver_checks > 0);
}

#[test]
fn settlement_audit_fresh_validation_and_false_claim() {
    type Demo = SettlementAudit<9, 4, true, true>;
    let circuit = Demo::new();
    // A validáláshoz külön, a fő állításokra kiválasztott riportot készít.
    let mut report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        K,
        &circuit.input(),
        [A, AMOUNT, CODE, layout(9).fee].map(|column| CellId::advice(column, 0)),
        options(Profile::Refinement),
    )
    .unwrap();
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    let validated =
        validate_private_recovery_report::<Fr, _>(&circuit, K, &circuit.input(), &report).unwrap();
    assert_eq!(validated.status, RecoveryValidationStatus::VerifiedDomains);
    report
        .cells
        .iter_mut()
        .find(|item| item.cell.column == CODE)
        .unwrap()
        .domain = Some(UcpValueDomain::exact(3.into()));
    let refuted =
        validate_private_recovery_report::<Fr, _>(&circuit, K, &circuit.input(), &report).unwrap();
    assert_eq!(refuted.status, RecoveryValidationStatus::Refuted);
    println!(
        "SETTLEMENT_VALIDATION positive={:?} false_claim={:?} checks={}/{}",
        validated.status, refuted.status, validated.solver_checks, refuted.solver_checks
    );
}

#[test]
fn settlement_audit_control_never_invents_exact_recovery() {
    type Demo = SettlementAudit<9, 4, true, false>;
    let circuit = Demo::new();
    let report = run(&circuit, Profile::Combined);
    let amount = cell(&report, CellId::advice(AMOUNT, 0));
    // A két különböző kielégítő értékadást a külön MockProver-teszt ellenőrzi.
    // Solverkorlátnál az elemző bizonytalan eredményét nem minősíti védettségi bizonyítéknak.
    assert_ne!(amount.uniqueness, PrivateCellUniqueness::Unique);
    assert!(!matches!(amount.domain, Some(UcpValueDomain::Exact(_))));
    assert!(!amount.domain_is_complete);
    if amount.uniqueness == PrivateCellUniqueness::Unknown {
        assert!(amount.recovery_limitation.is_some());
    }
}

#[test]
#[ignore = "Soros mérési mátrix; futtatás: --ignored --nocapture --test-threads=1"]
fn settlement_audit_measurement_matrix() {
    let selection = std::env::var("UCP_SETTLEMENT_PROFILES").unwrap_or_else(|_| "all".into());
    assert!(
        selection == "all"
            || selection.split(',').all(|name| [
                "propagation",
                "fast",
                "refinement",
                "discovery",
                "combined",
                "smt-only"
            ]
            .contains(&name)),
        "Unknown UCP_SETTLEMENT_PROFILES: {selection}"
    );
    fn measure<const BITS: usize, const LINKS: usize, const SEEDED: bool>() {
        type Leak<const B: usize, const L: usize, const S: bool> = SettlementAudit<B, L, S, true>;
        let circuit = Leak::<BITS, LINKS, SEEDED>::new();
        let repeats: usize = std::env::var("UCP_SETTLEMENT_REPEATS")
            .ok()
            .map(|v| v.parse().unwrap())
            .unwrap_or(3);
        assert!((1..=20).contains(&repeats));
        for profile in [
            Profile::Propagation,
            Profile::FastProbe,
            Profile::Refinement,
            Profile::Discovery,
            Profile::Combined,
        ] {
            let profile_name = match profile {
                Profile::Propagation => "propagation",
                Profile::FastProbe => "fast",
                Profile::Refinement => "refinement",
                Profile::Discovery => "discovery",
                Profile::Combined => "combined",
            };
            let selected =
                std::env::var("UCP_SETTLEMENT_PROFILES").unwrap_or_else(|_| "all".into());
            if selected != "all" && !selected.split(',').any(|name| name == profile_name) {
                continue;
            }
            for trial in 0..=repeats {
                println!("SETTLEMENT_TRIAL trial={trial} warmup={}", trial == 0);
                let report = run(&circuit, profile);
                // A nagyobb változat időkorlátja is mérési eredmény; a részleges állításokat is ellenőrzi.
                check_sound_claims(&circuit, &report);
            }
        }
        // Az SMT-alapvonal nem kap UCP-tényeket vagy visszacsatolást; ugyanazokat a célokat kérdezi le.
        for trial in 0..=repeats {
            let before = invocation_count();
            let started = Instant::now();
            let input = circuit.input();
            let mut analyzer = Analyzer::<Fr>::new(
                &circuit,
                K,
                AnalyzerType::UnderconstrainedCircuit,
                Some(&input),
            )
            .unwrap();
            analyzer.set_smt_timeout_ms(Some(5_000)).unwrap();
            let initial_sat = match analyzer.check_ucp_satisfiability(&input) {
                Ok(sat) => {
                    assert_eq!(sat, Satisfiability::Satisfiable);
                    true
                }
                Err(error)
                    if error
                        .downcast_ref::<crate::smt_solver::smt_parser::UnknownSolverResult>()
                        .is_some() =>
                {
                    false
                }
                Err(error) => panic!("{error:#}"),
            };
            let mut exact = 0;
            let mut non_unique = 0;
            let mut unknown = 0;
            for id in Leak::<BITS, LINKS, SEEDED>::targets() {
                if !initial_sat {
                    unknown += 1;
                    continue;
                }
                let expected = if id.row == 0 {
                    reference(id.column, layout(BITS))
                        .unwrap_or_else(|| [BigInt::from(circuit.values[id.column])].into())
                } else {
                    [BigInt::from(circuit.chain[id.row as usize - 2])].into()
                };
                match analyzer.query_ucp_cell_uniqueness_with_value(&input, &id) {
                    Ok(answer) => match answer.result {
                        SemanticQueryResult::ProvenUnique => {
                            assert_eq!(expected.len(), 1, "{id}");
                            if let Some(value) = &answer.value {
                                assert!(expected.contains(value), "{id}");
                            }
                            exact += usize::from(answer.value.is_some())
                        }
                        SemanticQueryResult::NotUnique => {
                            assert!(expected.len() > 1, "{id}");
                            non_unique += 1
                        }
                        SemanticQueryResult::Unknown => unknown += 1,
                        SemanticQueryResult::Overconstrained => {
                            panic!("Satisfiable fixture became inconsistent")
                        }
                    },
                    Err(error)
                        if error
                            .downcast_ref::<crate::smt_solver::smt_parser::UnknownSolverResult>()
                            .is_some() =>
                    {
                        unknown += 1
                    }
                    Err(error) => panic!("{error:#}"),
                }
            }
            println!("SETTLEMENT_SMT_ONLY bits={BITS} links={LINKS} seeded={SEEDED} trial={trial} warmup={} initial_sat={initial_sat} exact={exact} non_unique={non_unique} unknown={unknown} smt_invocations={} elapsed_ms={:.3}", trial == 0, invocation_count()-before,started.elapsed().as_secs_f64()*1000.0);
        }
    }
    match std::env::var("UCP_SETTLEMENT_CASE")
        .as_deref()
        .unwrap_or("small")
    {
        "small" => measure::<9, 4, true>(),
        "chain" => measure::<9, 12, true>(),
        "wide" => measure::<12, 4, true>(),
        "unseeded" => measure::<9, 4, false>(),
        "all" => {
            measure::<9, 4, true>();
            measure::<9, 12, true>();
            measure::<12, 4, true>();
            measure::<9, 4, false>();
        }
        other => panic!("Unknown UCP_SETTLEMENT_CASE: {other}"),
    }
}
