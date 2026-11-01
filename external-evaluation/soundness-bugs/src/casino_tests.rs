//! A kulso kaszinocircuitet es a hianyzo osszegzesi lepes helyi kontrolljait vizsgalja.

mod upstream {
    use crate::compat as halo2_proofs;
    include!(concat!(env!("CARGO_MANIFEST_DIR"), "/target/halo2-soundness-bugs-4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4/src/casino/casino2.rs"));
}

mod first_deposit_control {
    use crate::compat as halo2_proofs;
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/target/casino-first-deposit-control/casino2.rs"
    ));
}

mod small_original {
    use crate::compat as halo2_proofs;
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/target/casino-small-lookup-original/casino2.rs"
    ));
}

mod small_repaired {
    use crate::compat as halo2_proofs;
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/target/casino-small-lookup-repaired/casino2.rs"
    ));
}

use korrekt::{
    circuit_analyzer::{
        analyzable::Analyzable,
        halo2_proofs_libs::{Any, Circuit, Fr, MockProver, Value},
        ucp::{
            cell::CellId,
            extractor::extract_ucp_problem,
            privacy::{
                analyze_private_recoverability_with_witness, PrivacyAnalysisOptions,
                PrivacyAnalysisReport, PrivacyAnalysisStatus, PrivateCellUniqueness,
                SatisfiabilityEvidence,
            },
            value::UcpValueDomain,
        },
    },
    io::analyzer_io_type::{AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod},
};
use num_bigint::BigInt;
use std::time::Instant;

const FULL_K: u32 = 10;
const MAX_DEPOSIT: u64 = 999;

// A tabla es az adatsorok melle tartalekot hagy a backend vakito sorainak.
fn circuit_k(count: usize, lookup_size: usize) -> u32 {
    (lookup_size.max(count + 1) + 16)
        .next_power_of_two()
        .trailing_zeros()
        .max(5)
}

fn deposit_count() -> usize {
    let count = std::env::var("UCP_CASINO_DEPOSITS")
        .map(|value| value.parse().expect("Invalid UCP_CASINO_DEPOSITS"))
        .unwrap_or(4);
    assert!(
        (2..=32).contains(&count),
        "UCP_CASINO_DEPOSITS must be in 2..=32"
    );
    count
}

fn witnesses(values: &[u64]) -> Vec<Value<Fr>> {
    values
        .iter()
        .map(|value| Value::known(Fr::from(*value)))
        .collect()
}

fn observations(total: u64) -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput::new([("I-0-0".into(), BigInt::from(total))], 1),
        lookup_method: LookupMethod::InlineConstraints,
    }
}

fn options(count: usize) -> PrivacyAnalysisOptions {
    let timeout = std::env::var("UCP_CASINO_TIMEOUT_MS")
        .map(|value| value.parse().expect("Invalid UCP_CASINO_TIMEOUT_MS"))
        .unwrap_or(3000);
    assert!(timeout > 0);
    let mut options = PrivacyAnalysisOptions::default();
    options.solver_timeout_ms = Some(timeout);
    options.max_semantic_queries = 2 * count + 4;
    options.domain_refinement.max_solver_checks = 32;
    options.domain_discovery.max_solver_checks = 8;
    options.domain_discovery.max_values_per_cell = 4;
    options.search.max_bridge_queries = 2;
    options.search.max_queries_without_progress = 4;
    options.search.max_retries_per_target = 0;
    options.search.retry_solver_timeout_ms = None;
    options
}

// A befizetesi oszlop regiohoz viszonyitott sorait valasztja, nem tanuertekeket keres.
fn deposit_targets<C: Circuit<Fr>>(circuit: &C, count: usize, k: u32) -> Vec<CellId> {
    let analyzable = Analyzable::<Fr>::config_and_synthesize(circuit, k).unwrap();
    assert_eq!(analyzable.cs.lookups.len(), 1);
    let regions: Vec<_> = analyzable
        .regions
        .iter()
        .filter(|region| region.name == "main region")
        .collect();
    assert_eq!(regions.len(), 1);
    let region = regions[0];
    assert_eq!(region.cells.len(), 2 * (count + 1));
    let (start, end) = region.rows.unwrap();
    assert_eq!(end - start, count);
    let mut rows: Vec<_> = region
        .cells
        .keys()
        .filter(|(column, _)| column.index() == 0 && matches!(column.column_type(), Any::Advice(_)))
        .map(|(_, row)| *row)
        .collect();
    rows.sort_unstable();
    assert_eq!(rows, (start..=end).collect::<Vec<_>>());
    rows.into_iter()
        .skip(1)
        .map(|row| CellId::advice(0, i32::try_from(row).unwrap()))
        .collect()
}

fn recover<C: Circuit<Fr>>(
    label: &str,
    circuit: &C,
    total: u64,
    count: usize,
    lookup_size: usize,
) -> PrivacyAnalysisReport {
    let k = circuit_k(count, lookup_size);
    let targets = deposit_targets(circuit, count, k);
    let analyzable = Analyzable::<Fr>::config_and_synthesize(circuit, k).unwrap();
    let problem = extract_ucp_problem(&analyzable);
    // A kicsi egeszosszegekre vonatkozo referencia nem enged testbeli atfordulast.
    assert!(BigInt::from(count * (lookup_size - 1)) < problem.field_modulus);
    let options = options(count);
    println!("\n{label}; {count} private deposits; public total={total}; k={k}");
    println!(
        "{} equations; {} advice cells; {} Halo2 lookup arguments; {lookup_size} lookup rows",
        problem.expressions.len(),
        problem.witness_cells.len(),
        analyzable.cs.lookups.len()
    );
    println!("Standard options: {options:?}");
    let started = Instant::now();
    let report = analyze_private_recoverability_with_witness::<Fr, _, _>(
        circuit,
        k,
        &observations(total),
        targets.clone(),
        options,
    )
    .unwrap();
    println!(
        "{}",
        report.phase_report_with_names(|cell| targets
            .iter()
            .position(|target| target == cell)
            .map(|i| format!("deposit_{}", i + 1)))
    );
    println!(
        "Recovery wall time: {:.3}s",
        started.elapsed().as_secs_f64()
    );
    assert_eq!(
        report.satisfiability_evidence,
        Some(SatisfiabilityEvidence::VerifiedWitness)
    );
    assert_eq!(report.satisfiability_checks, 0);
    assert_eq!(report.cells.len(), count);
    assert_ne!(report.status, PrivacyAnalysisStatus::Inconsistent);
    report
}

#[test]
fn external_casino_native_controls_preserve_range_and_total() {
    let count = deposit_count();
    let mut values = vec![0; count];
    values[0] = MAX_DEPOSIT;
    let original = upstream::CasinoCircuit {
        deposits: witnesses(&values),
    };
    let control = first_deposit_control::CasinoCircuit {
        deposits: witnesses(&values),
    };
    let original_layout = Analyzable::<Fr>::config_and_synthesize(&original, FULL_K).unwrap();
    let repaired_layout = Analyzable::<Fr>::config_and_synthesize(&control, FULL_K).unwrap();
    assert_eq!(
        extract_ucp_problem(&repaired_layout).expressions.len(),
        extract_ucp_problem(&original_layout).expressions.len() + 1
    );
    MockProver::run(FULL_K, &original, vec![vec![Fr::from(MAX_DEPOSIT)]])
        .unwrap()
        .assert_satisfied();
    MockProver::run(FULL_K, &control, vec![vec![Fr::from(MAX_DEPOSIT)]])
        .unwrap()
        .assert_satisfied();
    assert!(
        MockProver::run(FULL_K, &control, vec![vec![Fr::from(MAX_DEPOSIT + 1)]])
            .unwrap()
            .verify()
            .is_err()
    );
    values[0] = MAX_DEPOSIT + 1;
    let outside_range = first_deposit_control::CasinoCircuit {
        deposits: witnesses(&values),
    };
    assert!(MockProver::run(
        FULL_K,
        &outside_range,
        vec![vec![Fr::from(MAX_DEPOSIT + 1)]]
    )
    .unwrap()
    .verify()
    .is_err());
    let empty = first_deposit_control::CasinoCircuit { deposits: vec![] };
    MockProver::run(FULL_K, &empty, vec![vec![Fr::from(0)]])
        .unwrap()
        .assert_satisfied();
}

#[test]
fn external_casino_small_lookup_original_zero_total_keeps_deposits_non_unique() {
    let count = deposit_count();
    let circuit = small_original::CasinoCircuit {
        deposits: witnesses(&vec![0; count]),
    };
    let report = recover(
        "Local 16-entry lookup control; first sum link still missing",
        &circuit,
        0,
        count,
        16,
    );
    assert_eq!(report.summary.exact_values, 0);
    assert_eq!(report.summary.non_unique_cells, count);
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.uniqueness == PrivateCellUniqueness::NonUnique));
    let expected = UcpValueDomain::finite_set((0..16).map(BigInt::from));
    assert!(report.cells.iter().all(|cell| cell.domain == expected));
}

#[test]
fn external_casino_small_lookup_repaired_boundary_totals_recover_all_deposits() {
    let count = deposit_count();
    for deposit in [0, 15] {
        let circuit = small_repaired::CasinoCircuit {
            deposits: witnesses(&vec![deposit; count]),
        };
        let report = recover(
            "Local 16-entry lookup and first-deposit repair; boundary-total disclosure",
            &circuit,
            deposit * count as u64,
            count,
            16,
        );
        assert_eq!(report.summary.exact_values, count);
        assert!(report.cells.iter().all(|cell| cell.domain
            == Some(UcpValueDomain::exact(deposit.into()))
            && cell.uniqueness == PrivateCellUniqueness::Unique
            && cell.domain_is_complete));
    }
}

#[test]
fn external_casino_small_lookup_repaired_interior_total_keeps_deposits_non_unique() {
    let count = deposit_count();
    let mut values = vec![0; count];
    values[0] = 1;
    let circuit = small_repaired::CasinoCircuit {
        deposits: witnesses(&values),
    };
    values.rotate_left(1);
    let alternate = small_repaired::CasinoCircuit {
        deposits: witnesses(&values),
    };
    MockProver::run(circuit_k(count, 16), &alternate, vec![vec![Fr::from(1)]])
        .unwrap()
        .assert_satisfied();
    let report = recover(
        "Local 16-entry lookup and first-deposit repair; ambiguous total",
        &circuit,
        1,
        count,
        16,
    );
    assert_eq!(report.summary.exact_values, 0);
    assert_eq!(report.summary.non_unique_cells, count);
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.uniqueness == PrivateCellUniqueness::NonUnique));
    let expected = UcpValueDomain::finite_set([BigInt::from(0), BigInt::from(1)]);
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.domain == expected && cell.domain_is_complete));
}

#[test]
#[ignore = "original 1000-entry lookup resource measurement; run explicitly and serially"]
fn external_casino_full_lookup_measurement() {
    let count = deposit_count();
    let original = upstream::CasinoCircuit {
        deposits: witnesses(&vec![0; count]),
    };
    let original_report = recover(
        "Unmodified external casino2; missing first sum link",
        &original,
        0,
        count,
        1000,
    );
    // Az eredetiben minden befizetes szabadon valaszthato a tablaban, a publikus nullatol fuggetlenul.
    assert!(original_report
        .cells
        .iter()
        .all(|cell| cell.uniqueness != PrivateCellUniqueness::Unique && cell.domain.is_none()));
    let repaired = first_deposit_control::CasinoCircuit {
        deposits: witnesses(&vec![0; count]),
    };
    let repaired_report = recover(
        "Local first-deposit repair; original 1000-entry lookup",
        &repaired,
        0,
        count,
        1000,
    );
    // A meres megenged bizonytalan eredmenyt, de a valodi nulla erteket kizaro vagy tobbmegoldasu allitast nem.
    for cell in &repaired_report.cells {
        assert_ne!(cell.uniqueness, PrivateCellUniqueness::NonUnique);
        if let Some(domain) = &cell.domain {
            match domain {
                UcpValueDomain::Exact(value) => assert_eq!(*value, BigInt::from(0)),
                UcpValueDomain::FiniteSet(values) => {
                    assert!(values.contains(&BigInt::from(0)));
                    assert!(!cell.domain_is_complete);
                }
            }
        }
    }
}
