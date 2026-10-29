//! External Halo2 Book fixture and a separately identified publication-leak control.
//! The upstream source is unchanged; the adapter never reads advice values to recover secrets.

use super::{
    cell::CellId,
    privacy::{
        analyze_private_recoverability, PrivacyAnalysisOptions, PrivacyAnalysisStatus,
        PrivateCellUniqueness,
    },
    privacy_validation::{
        validate_private_recovery_report, DomainValidationStatus, RecoveryValidationStatus,
    },
    value::UcpValueDomain,
};
use crate::{
    circuit_analyzer::{analyzable::Analyzable, halo2_proofs_libs::*},
    io::analyzer_io_type::{AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod},
};
use num_bigint::BigInt;
use std::collections::HashMap;

pub(super) mod halo2_book {
    //Import-name adaptation only; the included upstream file is byte-for-byte unchanged.
    use zcash_halo2_proofs as halo2_proofs;
    include!("fixtures/halo2_simple_example.rs");

    type Fr = halo2_proofs::pasta::Fp;

    pub(crate) fn original(a: u64, b: u64) -> impl Circuit<Fr> {
        MyCircuit {
            constant: Fr::from(7),
            a: Value::known(Fr::from(a)),
            b: Value::known(Fr::from(b)),
        }
    }

    //Local positive control: reuse upstream gates, but publish a and ab in addition to c.
    //Only b remains a selected secret; intentionally published a is not counted as leakage.
    struct PublishedIntermediates {
        a: Value<Fr>,
        b: Value<Fr>,
    }

    impl Circuit<Fr> for PublishedIntermediates {
        type Config = FieldConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                a: Value::unknown(),
                b: Value::unknown(),
            }
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            <MyCircuit<Fr> as Circuit<Fr>>::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let chip = FieldChip::<Fr>::construct(config);
            let a = chip.load_private(layouter.namespace(|| "load a"), self.a)?;
            let b = chip.load_private(layouter.namespace(|| "load b"), self.b)?;
            let constant =
                chip.load_constant(layouter.namespace(|| "load constant"), Fr::from(7))?;
            let ab = chip.mul(layouter.namespace(|| "a * b"), a.clone(), b)?;
            let absq = chip.mul(layouter.namespace(|| "ab * ab"), ab.clone(), ab.clone())?;
            let c = chip.mul(layouter.namespace(|| "constant * absq"), constant, absq)?;
            chip.expose_public(layouter.namespace(|| "expose c"), c, 0)?;
            chip.expose_public(layouter.namespace(|| "publish a"), a, 1)?;
            chip.expose_public(layouter.namespace(|| "publish ab"), ab, 2)
        }
    }

    pub(crate) fn published_intermediates(a: u64, b: u64) -> impl Circuit<Fr> {
        PublishedIntermediates {
            a: Value::known(Fr::from(a)),
            b: Value::known(Fr::from(b)),
        }
    }

    pub(crate) fn run_original_mock_example() {
        main();
    }
}

//Select the two real private inputs by their upstream load regions, not every advice copy.
pub(super) fn private_inputs<C: Circuit<Fr>>(circuit: &C) -> Vec<CellId> {
    let analyzable = Analyzable::<Fr>::config_and_synthesize(circuit, 4).unwrap();
    let cells: Vec<_> = analyzable
        .regions
        .iter()
        .filter(|region| region.name == "load private")
        .map(|region| {
            assert_eq!(
                region.cells.len(),
                1,
                "Upstream private-input layout changed"
            );
            let (column, row) = region.cells[0];
            assert_eq!(column.column_type(), &Any::Advice);
            CellId::advice(column.index(), i32::try_from(row).unwrap())
        })
        .collect();
    assert_eq!(
        cells.len(),
        2,
        "Expected exactly the upstream a and b inputs"
    );
    assert_ne!(cells[0], cells[1]);
    cells
}

pub(super) fn observations(publications: &[i64]) -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput {
            instance_cells: publications
                .iter()
                .enumerate()
                .map(|(row, value)| (format!("I-0-{row}"), (*value).into()))
                .collect::<HashMap<_, _>>(),
            iterations: 1,
        },
        lookup_method: LookupMethod::InlineConstraints,
    }
}

fn mock_check<C: Circuit<Fr>>(circuit: &C, publications: &[u64]) {
    zcash_halo2_proofs::dev::MockProver::run(
        4,
        circuit,
        vec![publications.iter().copied().map(Fr::from).collect()],
    )
    .unwrap()
    .assert_satisfied();
}

#[test]
fn external_halo2_book_original_keeps_private_inputs_non_unique() {
    //Upstream main also checks that changing c makes the witness fail MockProver.
    halo2_book::run_original_mock_example();
    let circuit = halo2_book::original(2, 3);
    let alternate = halo2_book::original(1, 6);
    mock_check(&circuit, &[252]);
    mock_check(&alternate, &[252]);
    let targets = private_inputs(&circuit);
    assert_eq!(targets, private_inputs(&alternate));
    let input = observations(&[252]);
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        targets.clone(),
        PrivacyAnalysisOptions::default(),
    )
    .unwrap();
    println!("Unmodified Halo2 Book example, c=252:\n{report}");
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.summary.non_unique_cells, 2);
    assert_eq!(report.summary.exact_values, 0);
    assert!(report.cells.iter().all(|cell| {
        cell.uniqueness == PrivateCellUniqueness::NonUnique && cell.domain.is_none()
    }));
    let alternate_report = analyze_private_recoverability::<Fr, _, _>(
        &alternate,
        4,
        &input,
        targets,
        PrivacyAnalysisOptions::default(),
    )
    .unwrap();
    assert_eq!(report.cells, alternate_report.cells);
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report).unwrap();
    assert_eq!(validation.status, RecoveryValidationStatus::NoDomainClaims);
    //Non-uniqueness is not a cryptographic privacy certificate for this arithmetic relation.
}

#[test]
fn external_halo2_book_published_intermediates_recover_remaining_secret() {
    let circuit = halo2_book::published_intermediates(2, 3);
    mock_check(&circuit, &[252, 2, 6]);
    let b = private_inputs(&circuit)[1].clone();
    let input = observations(&[252, 2, 6]);
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        [b],
        PrivacyAnalysisOptions::default(),
    )
    .unwrap();
    println!("Local publication control, a=2 and ab=6 expose b=3:\n{report}");
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.summary.unique_cells, 1);
    assert_eq!(report.summary.exact_values, 1);
    assert_eq!(
        report.cells[0].domain,
        Some(UcpValueDomain::exact(BigInt::from(3)))
    );
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report).unwrap();
    println!("Independent validation:\n{validation}");
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
    assert_eq!(validation.cells[0].status, DomainValidationStatus::Entailed);
    //A wrong supplied witness fails Halo2, but must not become a recovery premise.
    let invalid_witness = halo2_book::published_intermediates(2, 4);
    let prover = zcash_halo2_proofs::dev::MockProver::run(
        4,
        &invalid_witness,
        vec![vec![Fr::from(252), Fr::from(2), Fr::from(6)]],
    )
    .unwrap();
    assert!(prover.verify().is_err());
    let without_witness_sampling = analyze_private_recoverability::<Fr, _, _>(
        &invalid_witness,
        4,
        &input,
        private_inputs(&invalid_witness).into_iter().skip(1),
        PrivacyAnalysisOptions::default(),
    )
    .unwrap();
    assert_eq!(report.cells, without_witness_sampling.cells);
    //Check against the original constraints, not against an assumed recovered value.
    let mut wrong = report;
    wrong.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(4)));
    let refuted = validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &wrong).unwrap();
    assert_eq!(refuted.status, RecoveryValidationStatus::Refuted);
    assert_eq!(refuted.cells[0].counterexample, Some(BigInt::from(3)));
}

#[test]
fn external_halo2_book_requires_complete_public_observations() {
    let circuit = halo2_book::published_intermediates(2, 3);
    let b = private_inputs(&circuit)[1].clone();
    for row in 0..3 {
        let mut input = observations(&[252, 2, 6]);
        input
            .verification_input
            .instance_cells
            .remove(&format!("I-0-{row}"));
        let error = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input,
            [b.clone()],
            PrivacyAnalysisOptions::default(),
        )
        .unwrap_err();
        assert!(error
            .to_string()
            .contains("Missing concrete public observation"));
    }
}
