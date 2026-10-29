//! A tanúellenőrzés létezési bizonyítékát választja el a visszaállítás premisszáitól.

use super::*;
use crate::{io::analyzer_io_type::VerificationInput, smt_solver::process::invocation_count};

const LINEAR: u8 = 0;
const MASKED: u8 = 1;
const INCONSISTENT: u8 = 2;
const BOOLEAN: u8 = 3;

#[derive(Clone)]
struct WitnessCircuit<const CASE: u8> {
    secret: Option<Fr>,
    nonce: Fr,
}

#[derive(Clone)]
struct Config {
    secret: Column<Advice>,
    nonce: Column<Advice>,
    selector: Selector,
}

impl<const CASE: u8> Circuit<Fr> for WitnessCircuit<CASE> {
    type Config = Config;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            secret: None,
            nonce: Fr::ZERO,
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Config {
        // Az első instance oszlop és az első két sor kihasználatlan marad.
        let public = if CASE == BOOLEAN {
            None
        } else {
            let _unused = meta.instance_column();
            Some(meta.instance_column())
        };
        let secret = meta.advice_column();
        let nonce = meta.advice_column();
        let selector = meta.selector();
        meta.create_gate("witness existence and privacy", |meta| {
            let q = meta.query_selector(selector);
            let s = meta.query_advice(secret, Rotation::cur());
            let n = meta.query_advice(nonce, Rotation::cur());
            let c = |v| Expression::Constant(Fr::from(v));
            let p = public
                .map(|column| meta.query_instance(column, Rotation::cur()))
                .unwrap_or_else(|| c(0));
            let equations = match CASE {
                LINEAR => vec![s + c(5) - p],
                MASKED => vec![s + n - p],
                INCONSISTENT => vec![s.clone(), s - c(1)],
                BOOLEAN => vec![s.clone() * (s - c(1))],
                _ => unreachable!(),
            };
            equations
                .into_iter()
                .map(|e| q.clone() * e)
                .collect::<Vec<_>>()
        });
        Config {
            secret,
            nonce,
            selector,
        }
    }

    fn synthesize(
        &self,
        config: Config,
        mut layouter: impl Layouter<Fr>,
    ) -> std::result::Result<(), Error> {
        layouter.assign_region(
            || "actual witness",
            |mut region| {
                config.selector.enable(&mut region, 2)?;
                region.assign_advice(
                    || "secret",
                    config.secret,
                    2,
                    || self.secret.map(Value::known).unwrap_or(Value::unknown()),
                )?;
                region.assign_advice(|| "nonce", config.nonce, 2, || Value::known(self.nonce))?;
                Ok(())
            },
        )
    }
}

fn input(value: BigInt) -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput::new([("I-1-2".to_owned(), value)], 1),
        lookup_method: LookupMethod::InlineConstraints,
    }
}

fn options() -> PrivacyAnalysisOptions {
    PrivacyAnalysisOptions {
        max_semantic_queries: 0,
        solver_timeout_ms: Some(2_000),
        initial_sat_timeout_ms: Some(2_000),
        ..Default::default()
    }
}

fn analyze<const CASE: u8>(
    circuit: &WitnessCircuit<CASE>,
    public: BigInt,
) -> PrivacyAnalysisReport {
    analyze_private_recoverability_with_witness::<Fr, _, _>(
        circuit,
        4,
        &input(public),
        [CellId::advice(0, 2)],
        options(),
    )
    .unwrap()
}

#[test]
fn witness_guard_accepts_actual_public_values_without_any_solver_call() {
    let circuit = WitnessCircuit::<LINEAR> {
        secret: Some(Fr::from(95)),
        nonce: Fr::ZERO,
    };
    let before = invocation_count();
    let report = analyze(&circuit, 100.into());
    assert_eq!(invocation_count(), before);
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.satisfiability_checks, 0);
    assert_eq!(
        report.satisfiability_evidence,
        Some(SatisfiabilityEvidence::VerifiedWitness)
    );
    assert_eq!(
        report.cells[0].domain,
        Some(UcpValueDomain::exact(95.into()))
    );
    assert_eq!(report.public_values, [(CellId::instance(1, 2), 100.into())]);
    assert!(report
        .to_string()
        .contains("Satisfiability evidence: VerifiedWitness"));
    assert!(report.to_string().contains(PRIVACY_WITNESS_SAT_POLICY));
}

#[test]
fn witness_guard_does_not_turn_a_private_sample_into_a_recovered_value() {
    for (secret, nonce) in [(30, 70), (40, 60)] {
        let circuit = WitnessCircuit::<MASKED> {
            secret: Some(Fr::from(secret)),
            nonce: Fr::from(nonce),
        };
        let before = invocation_count();
        let report = analyze(&circuit, 100.into());
        assert_eq!(invocation_count(), before);
        assert_eq!(
            report.satisfiability_evidence,
            Some(SatisfiabilityEvidence::VerifiedWitness)
        );
        assert_ne!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
        assert_eq!(report.cells[0].domain, None);
        assert!(!report.cells[0].domain_is_complete);
        assert_eq!(report.summary.exact_values, 0);
    }
}

#[test]
fn witness_guard_preserves_the_existing_smt_entry_point() {
    let circuit = WitnessCircuit::<LINEAR> {
        secret: Some(Fr::from(95)),
        nonce: Fr::ZERO,
    };
    let before = invocation_count();
    let original = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input(100.into()),
        [CellId::advice(0, 2)],
        options(),
    )
    .unwrap();
    assert!(invocation_count() > before);
    assert!(original.satisfiability_checks > 0);
    assert_eq!(
        original.satisfiability_evidence,
        Some(SatisfiabilityEvidence::Smt)
    );
    let verified = analyze(&circuit, 100.into());
    assert_eq!(original.cells, verified.cells);
    assert_eq!(original.public_values, verified.public_values);
}

#[test]
fn witness_guard_handles_no_instance_columns_without_narrowing_a_boolean_domain() {
    let input = AnalyzerInput {
        verification_input: VerificationInput::new(Vec::<(String, BigInt)>::new(), 1),
        ..input(0.into())
    };
    for secret in [Fr::ZERO, Fr::ONE] {
        let circuit = WitnessCircuit::<BOOLEAN> {
            secret: Some(secret),
            nonce: Fr::ZERO,
        };
        let before = invocation_count();
        let report = analyze_private_recoverability_with_witness::<Fr, _, _>(
            &circuit,
            4,
            &input,
            [CellId::advice(0, 2)],
            options(),
        )
        .unwrap();
        assert_eq!(invocation_count(), before);
        assert_eq!(
            report.satisfiability_evidence,
            Some(SatisfiabilityEvidence::VerifiedWitness)
        );
        assert_eq!(
            report.cells[0].domain,
            UcpValueDomain::finite_set([0.into(), 1.into()])
        );
        assert!(!report.cells[0].domain_is_complete);
        assert_ne!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
    }
}

#[test]
fn witness_guard_falls_back_for_wrong_missing_and_mismatched_witnesses() {
    // A 96-os tanú 101-es megfigyeléshez helyes, 100-hoz nem; a 7-es tanú is hibás.
    for secret in [Some(Fr::from(7)), Some(Fr::from(96)), None] {
        let circuit = WitnessCircuit::<LINEAR> {
            secret,
            nonce: Fr::ZERO,
        };
        let before = invocation_count();
        let report = analyze(&circuit, 100.into());
        assert!(invocation_count() > before);
        assert!(report.satisfiability_checks > 0);
        assert_eq!(
            report.satisfiability_evidence,
            Some(SatisfiabilityEvidence::Smt)
        );
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(95.into()))
        );
    }
}

#[test]
fn witness_guard_only_reports_inconsistency_after_original_smt_check() {
    let circuit = WitnessCircuit::<INCONSISTENT> {
        secret: Some(Fr::ZERO),
        nonce: Fr::ZERO,
    };
    let before = invocation_count();
    let report = analyze(&circuit, 100.into());
    assert!(invocation_count() > before);
    assert!(report.satisfiability_checks > 0);
    assert_eq!(report.status, PrivacyAnalysisStatus::Inconsistent);
    assert_eq!(report.satisfiability_evidence, None);
    assert_eq!(report.ucp_result, None);
    assert_eq!(report.cells[0].domain, None);
}

#[test]
fn witness_guard_preserves_signed_and_full_width_field_observations() {
    let large = (BigInt::from(1) << 200usize) + BigInt::from(123);
    for public in [BigInt::from(-1), large] {
        let magnitude = Fr::from_str_vartime(&public.magnitude().to_string()).unwrap();
        let field = if public.sign() == num_bigint::Sign::Minus {
            -magnitude
        } else {
            magnitude
        };
        let circuit = WitnessCircuit::<LINEAR> {
            secret: Some(field - Fr::from(5)),
            nonce: Fr::ZERO,
        };
        let before = invocation_count();
        let report = analyze(&circuit, public.clone());
        assert_eq!(invocation_count(), before);
        assert_eq!(
            report.satisfiability_evidence,
            Some(SatisfiabilityEvidence::VerifiedWitness)
        );
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(public - BigInt::from(5)))
        );
    }
}

#[test]
fn witness_guard_rejects_invalid_instance_indices_before_allocating_padding() {
    let circuit = WitnessCircuit::<LINEAR> {
        secret: Some(Fr::from(95)),
        nonce: Fr::ZERO,
    };
    let mut context = prepare_privacy_analysis::<Fr, _, _>(
        &circuit,
        4,
        &input(100.into()),
        [CellId::advice(0, 2)],
    )
    .unwrap();
    for cell in [
        CellId::instance(1, -1),
        CellId::instance(1, i32::MAX),
        CellId::instance(usize::MAX, 2),
        CellId::advice(1, 2),
    ] {
        context.public_values.push((cell, 0.into()));
        assert!(witness_instances(&context, 4).is_none());
        context.public_values.pop();
    }
}

#[test]
fn witness_guard_does_not_replace_fresh_domain_validation() {
    use super::super::privacy_validation::{
        validate_private_recovery_report, RecoveryValidationStatus,
    };
    let circuit = WitnessCircuit::<LINEAR> {
        secret: Some(Fr::from(95)),
        nonce: Fr::ZERO,
    };
    let mut report = analyze(&circuit, 100.into());
    let before = invocation_count();
    let validated =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(100.into()), &report)
            .unwrap();
    assert!(invocation_count() > before);
    assert!(validated.solver_checks > 0);
    assert_eq!(validated.status, RecoveryValidationStatus::VerifiedDomains);
    report.cells[0].domain = Some(UcpValueDomain::exact(94.into()));
    let refuted =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(100.into()), &report)
            .unwrap();
    assert_eq!(refuted.status, RecoveryValidationStatus::Refuted);
}
