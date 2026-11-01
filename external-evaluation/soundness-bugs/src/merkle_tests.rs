//! A valtozatlan, osszeadasos Merkle-pelda het privat bemenetet vizsgalja.

mod upstream {
    use crate::compat as halo2_proofs;

    // Az eredeti FieldValue adapter csak Value::as_ref()-et hiv, kaput nem hoz letre.
    // Az eredeti implementacio: teddav/poseidon-gadget, dfeb9bf, src/utilities.rs.
    mod halo2_poseidon {
        pub mod utilities {
            use backend::{arithmetic::Field, circuit::Value};

            pub trait FieldValue<F: Field> {
                fn value(&self) -> Value<&F>;
            }

            impl<F: Field> FieldValue<F> for Value<F> {
                fn value(&self) -> Value<&F> {
                    self.as_ref()
                }
            }
        }
    }

    include!(concat!(env!("CARGO_MANIFEST_DIR"), "/target/halo2-soundness-bugs-4fd3ec65e88d0f5e401206c0b1d29a9eba4ecce4/src/merkle/merkle_nohash4.rs"));
}

use backend::{circuit::Value, dev::MockProver, halo2curves::pasta::Fp, plonk::Any};
use korrekt::{
    circuit_analyzer::{
        analyzable::Analyzable,
        ucp::{
            cell::CellId,
            extractor::extract_ucp_problem,
            privacy::{
                analyze_private_recoverability_with_witness, PrivacyAnalysisOptions,
                PrivacyAnalysisReport, PrivacyAnalysisStatus, PrivateCellUniqueness, RecoveryPhase,
                SatisfiabilityEvidence,
            },
            value::UcpValueDomain,
        },
    },
    io::analyzer_io_type::{AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod},
};
use num_bigint::BigInt;
use std::collections::BTreeMap;
use upstream::MerkleCircuitNoHash4;

const K: u32 = 5;
const DEPTH: usize = 3;
const ROOT: u64 = 23;

fn circuit(leaf: u64, siblings: [u64; DEPTH], bits: [u64; DEPTH]) -> MerkleCircuitNoHash4 {
    MerkleCircuitNoHash4 {
        leaf: Value::known(Fp::from(leaf)),
        path_elements: siblings
            .into_iter()
            .map(|v| Value::known(Fp::from(v)))
            .collect(),
        path_indices: bits
            .into_iter()
            .map(|v| Value::known(Fp::from(v)))
            .collect(),
    }
}

fn original() -> MerkleCircuitNoHash4 {
    circuit(4, [3, 5, 7], [0, 1, 0])
}

fn observations() -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput::new([("I-0-0".into(), BigInt::from(ROOT))], 1),
        lookup_method: LookupMethod::InlineConstraints,
    }
}

// A bemeneteket a regiok es oszlopok szerepe alapjan valasztja, tanuertek olvasasa nelkul.
fn targets(circuit: &MerkleCircuitNoHash4) -> BTreeMap<CellId, String> {
    let layout = Analyzable::<Fp>::config_and_synthesize(circuit, K).unwrap();
    assert!(layout.cs.lookups.is_empty());
    let mut targets = BTreeMap::new();
    let mut layers = 0;
    let mut leaves = 0;
    for region in &layout.regions {
        let inputs = |column: usize| {
            let row = region.rows.unwrap().0;
            assert!(region.cells.keys().any(|(col, assigned_row)| {
                matches!(col.column_type(), Any::Advice(_))
                    && col.index() == column
                    && *assigned_row == row
            }));
            CellId::advice(column, i32::try_from(row).unwrap())
        };
        match region.name.as_str() {
            "assign leaf" => {
                assert_eq!(region.cells.len(), 2);
                targets.insert(inputs(0), "leaf".into());
                leaves += 1;
            }
            "merkle prove" => {
                assert_eq!(region.cells.len(), 6);
                targets.insert(inputs(1), format!("sibling_{layers}"));
                targets.insert(inputs(2), format!("direction_{layers}"));
                layers += 1;
            }
            _ => (),
        }
    }
    assert_eq!(leaves, 1);
    assert_eq!(layers, DEPTH);
    assert_eq!(targets.len(), 1 + 2 * DEPTH);
    targets
}

fn options() -> PrivacyAnalysisOptions {
    let timeout = std::env::var("UCP_MERKLE_TIMEOUT_MS")
        .map(|value| value.parse().expect("Invalid UCP_MERKLE_TIMEOUT_MS"))
        .unwrap_or(3_000);
    assert!(timeout > 0);
    let mut options = PrivacyAnalysisOptions::default();
    options.solver_timeout_ms = Some(timeout);
    options.initial_sat_timeout_ms = Some(60_000);
    options.search.retry_solver_timeout_ms = None;
    options
}

fn recover(circuit: &MerkleCircuitNoHash4) -> PrivacyAnalysisReport {
    analyze_private_recoverability_with_witness::<Fp, _, _>(
        circuit,
        K,
        &observations(),
        targets(circuit).into_keys(),
        options(),
    )
    .unwrap()
}

#[test]
fn external_merkle_nohash_native_controls() {
    // Minden bemenethez kulon ervenyes alternativat ellenoriz ugyanazon gyok mellett.
    let variants = [
        original(),
        circuit(5, [1, 5, 7], [0, 1, 0]),
        circuit(4, [4, 4, 7], [0, 1, 0]),
        circuit(4, [3, 6, 6], [0, 1, 0]),
        circuit(4, [2, 5, 8], [0, 1, 0]),
        circuit(4, [3, 5, 7], [1, 1, 0]),
        circuit(4, [3, 5, 7], [0, 0, 0]),
        circuit(4, [3, 5, 7], [0, 1, 1]),
    ];
    let expected_targets = targets(&variants[0]);
    for variant in &variants {
        MockProver::run(K, variant, vec![vec![Fp::from(ROOT)]])
            .unwrap()
            .assert_satisfied();
        assert_eq!(targets(variant), expected_targets);
    }
    assert!(
        MockProver::run(K, &original(), vec![vec![Fp::from(ROOT + 1)]])
            .unwrap()
            .verify()
            .is_err()
    );
    assert!(MockProver::run(
        K,
        &circuit(4, [3, 5, 7], [2, 1, 0]),
        vec![vec![Fp::from(ROOT)]]
    )
    .unwrap()
    .verify()
    .is_err());
}

#[test]
fn external_merkle_nohash_standard_recovery() {
    let circuit = original();
    let names = targets(&circuit);
    let layout = Analyzable::<Fp>::config_and_synthesize(&circuit, K).unwrap();
    let problem = extract_ucp_problem(&layout);
    println!("Unmodified external Merkle NoHash4: Standard (combined)");
    println!(
        "{DEPTH} levels; {} private targets; {} equations; {} advice cells; public root={ROOT}",
        names.len(),
        problem.expressions.len(),
        problem.witness_cells.len()
    );
    let report = recover(&circuit);
    println!(
        "{}",
        report.phase_report_with_names(|cell| names.get(cell).cloned())
    );
    assert_ne!(report.status, PrivacyAnalysisStatus::Inconsistent);
    assert_eq!(
        report.satisfiability_evidence,
        Some(SatisfiabilityEvidence::VerifiedWitness)
    );
    assert_eq!(report.satisfiability_checks, 0);
    assert_eq!(report.summary.exact_values, 0);
    assert_eq!(report.summary.non_unique_cells, names.len());
    assert_eq!(report.summary.unresolved_uniqueness, 0);
    let boolean_domain = UcpValueDomain::finite_set([BigInt::from(0), BigInt::from(1)]);
    for cell in &report.cells {
        assert_eq!(cell.uniqueness, PrivateCellUniqueness::NonUnique);
        if names[&cell.cell].starts_with("direction_") {
            assert_eq!(cell.domain, boolean_domain);
            assert!(cell.domain_is_complete);
        } else {
            assert!(cell.domain.is_none());
            assert!(!cell.domain_is_complete);
        }
    }
    let Some(RecoveryPhase::Ucp { counts, .. }) = report.phases.first() else {
        panic!("Expected initial propagation phase");
    };
    assert_eq!(counts.domains, DEPTH);
    assert_eq!(counts.exact_values, 0);
}
