//! Full-width private recovery without reading advice assignments as public facts.
use super::{
    cell::CellId,
    privacy::{
        analyze_private_recoverability, PrivacyAnalysisOptions, PrivateCellUniqueness,
        PrivateRecoveryStatus,
    },
    privacy_validation::{validate_private_recovery_report, RecoveryValidationStatus},
    value::UcpValueDomain,
};
use crate::{
    circuit_analyzer::{
        analyzer::{Analyzer, SemanticQueryResult},
        halo2_proofs_libs::*,
    },
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerType, LookupMethod, VerificationInput, VerificationMethod,
    },
};
use num_bigint::BigInt;
use std::collections::HashMap;

// A public multiplier reveals a 254-bit private operand; a second gate propagates it.
// Negation exercises the signed representative used by both UCP and the SMT bridge.
#[derive(Clone)]
struct WideCircuit<const NEGATIVE: bool> {
    wrong_witness: bool,
}

#[derive(Clone, Debug)]
struct WideConfig {
    secret: Column<Advice>,
    derived: Column<Advice>,
    selector: Selector,
}

fn constant<const NEGATIVE: bool>() -> Fr {
    let mut value = Fr::from(1);
    for _ in 0..253 {
        value = value + value;
    }
    if NEGATIVE {
        -value
    } else {
        value
    }
}

fn expected<const NEGATIVE: bool>() -> BigInt {
    let value = BigInt::from(1) << 253usize;
    if NEGATIVE {
        -value
    } else {
        value
    }
}

impl<const NEGATIVE: bool> Circuit<Fr> for WideCircuit<NEGATIVE> {
    type Config = WideConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            wrong_witness: false,
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let public = meta.instance_column();
        let secret = meta.advice_column();
        let derived = meta.advice_column();
        let selector = meta.selector();
        meta.create_gate("public multiplier reveals a full-width operand", |meta| {
            let q = meta.query_selector(selector);
            let public = meta.query_instance(public, Rotation::cur());
            let secret = meta.query_advice(secret, Rotation::cur());
            let derived = meta.query_advice(derived, Rotation::cur());
            vec![
                q.clone()
                    * (secret.clone() - Expression::Constant(constant::<NEGATIVE>()) * public),
                q * (derived - secret - Expression::Constant(Fr::from(7))),
            ]
        });
        WideConfig {
            secret,
            derived,
            selector,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "wide private operand",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                let value = if self.wrong_witness {
                    Fr::from(3)
                } else {
                    constant::<NEGATIVE>()
                };
                region.assign_advice(|| "secret", config.secret, 0, || Value::known(value))?;
                region.assign_advice(
                    || "derived",
                    config.derived,
                    0,
                    || Value::known(value + Fr::from(7)),
                )?;
                Ok(())
            },
        )
    }
}

fn input() -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput {
            instance_cells: HashMap::from([("I-0-0".into(), 1.into())]),
            iterations: 1,
        },
        lookup_method: LookupMethod::InlineConstraints,
    }
}

fn check_recovery<const NEGATIVE: bool>(wrong_witness: bool) {
    let circuit = WideCircuit::<NEGATIVE> { wrong_witness };
    let input = input();
    let secret = CellId::advice(0, 0);
    let derived = CellId::advice(1, 0);
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        [secret.clone(), derived.clone()],
        PrivacyAnalysisOptions {
            max_semantic_queries: 2,
            solver_timeout_ms: Some(2_000),
            ..Default::default()
        },
    )
    .unwrap();

    // Delta stores all 254 bits, not merely the fact that the cell is unique in K.
    assert_eq!(report.summary.exact_values, 2);
    assert_eq!(report.semantic_queries, 0);
    for (cell, value) in [
        (secret, expected::<NEGATIVE>()),
        (derived, expected::<NEGATIVE>() + 7),
    ] {
        let result = report
            .cells
            .iter()
            .find(|entry| entry.cell == cell)
            .unwrap();
        assert_eq!(result.recovery_status(), PrivateRecoveryStatus::Recovered);
        assert_eq!(result.domain, Some(UcpValueDomain::exact(value)));
        assert_eq!(result.recovery_limitation, None);
    }

    // A fresh solver checks the original constraints, without assuming recovered facts.
    let validation =
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report).unwrap();
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
    println!("{report}\n{validation}");
}

#[test]
fn full_width_recovery_propagates_and_passes_fresh_validation() {
    MockProver::run(
        4,
        &WideCircuit::<false> {
            wrong_witness: false,
        },
        vec![vec![Fr::from(1)]],
    )
    .unwrap()
    .assert_satisfied();
    check_recovery::<false>(false);
}

#[test]
fn negative_full_width_representative_roundtrips_through_smt() {
    check_recovery::<true>(false);
}

#[test]
fn supplied_advice_witness_is_not_used_as_a_recovery_oracle() {
    // Reject the supplied witness, yet recover the actual permitted value from C + public data.
    assert!(MockProver::run(
        4,
        &WideCircuit::<false> {
            wrong_witness: true
        },
        vec![vec![Fr::from(1)]]
    )
    .unwrap()
    .verify()
    .is_err());
    check_recovery::<false>(true);
}

#[test]
fn smt_only_query_returns_the_full_width_unique_model_value() {
    let input = input();
    let mut analyzer = Analyzer::<Fr>::new(
        &WideCircuit::<false> {
            wrong_witness: false,
        },
        4,
        AnalyzerType::UnderconstrainedCircuit,
        Some(&input),
    )
    .unwrap();
    analyzer.set_smt_timeout_ms(Some(2_000)).unwrap();
    // No UCP facts are injected; this exercises parsing and model normalization directly.
    let output = analyzer
        .query_ucp_cell_uniqueness_with_value(&input, &CellId::advice(0, 0))
        .unwrap();
    assert_eq!(output.result, SemanticQueryResult::ProvenUnique);
    assert_eq!(output.value, Some(expected::<false>()));
    assert_eq!(output.value_unavailable_reason, None);
}

// Publishing 3*secret+7 leaks the operand; publishing secret+mask alone does not
// determine either operand. Both variants use the same large public observation.
#[derive(Clone)]
struct PublishedAffineCircuit<const MASKED: bool>;

fn affine_secret() -> Fr {
    let mut value = Fr::from(1);
    for _ in 0..200 {
        value = value + value;
    }
    value
}

fn publication() -> BigInt {
    (BigInt::from(1) << 200usize) * 3 + 7
}

impl<const MASKED: bool> Circuit<Fr> for PublishedAffineCircuit<MASKED> {
    type Config = WideConfig;
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        self.clone()
    }
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let public = meta.instance_column();
        let secret = meta.advice_column();
        let derived = meta.advice_column();
        let selector = meta.selector();
        meta.create_gate(
            "published affine value with or without an independent mask",
            |meta| {
                let q = meta.query_selector(selector);
                let public = meta.query_instance(public, Rotation::cur());
                let secret = meta.query_advice(secret, Rotation::cur());
                let derived = meta.query_advice(derived, Rotation::cur());
                if MASKED {
                    vec![q * (public - secret - derived)]
                } else {
                    vec![
                        q.clone()
                            * (public
                                - Expression::Constant(Fr::from(3)) * secret.clone()
                                - Expression::Constant(Fr::from(7))),
                        q * (derived - secret - Expression::Constant(Fr::from(7))),
                    ]
                }
            },
        );
        WideConfig {
            secret,
            derived,
            selector,
        }
    }
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "private operand and second advice cell",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                let secret = affine_secret();
                let derived = if MASKED {
                    secret + secret + Fr::from(7)
                } else {
                    secret + Fr::from(7)
                };
                region.assign_advice(|| "secret", config.secret, 0, || Value::known(secret))?;
                region.assign_advice(
                    || "derived or independent mask",
                    config.derived,
                    0,
                    || Value::known(derived),
                )?;
                Ok(())
            },
        )
    }
}

fn wide_input(value: BigInt) -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput::new([("I-0-0".into(), value)], 1),
        lookup_method: LookupMethod::InlineConstraints,
    }
}

#[test]
fn full_width_public_observation_supports_recovery_validation_and_pipeline() {
    use super::pipeline::analyze_underconstrained_with_ucp_and_value_recovery;
    let circuit = PublishedAffineCircuit::<false>;
    let public = affine_secret() * Fr::from(3) + Fr::from(7);
    MockProver::run(4, &circuit, vec![vec![public]])
        .unwrap()
        .assert_satisfied();
    let modulus = super::extractor::field_modulus::<Fr>();
    // Canonical, wrapped positive and wrapped negative values denote the same field element.
    for observation in [
        publication(),
        publication() + &modulus,
        publication() - &modulus,
    ] {
        let input = wide_input(observation);
        let targets = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input,
            targets.clone(),
            PrivacyAnalysisOptions {
                max_semantic_queries: 2,
                solver_timeout_ms: Some(2_000),
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(
            report.public_values,
            vec![(CellId::instance(0, 0), publication())]
        );
        assert_eq!(report.summary.exact_values, 2);
        assert_eq!(report.semantic_queries, 0);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(1) << 200usize))
        );
        // Validation accepts an equivalent canonical observation, not just identical input bytes.
        let validation = validate_private_recovery_report::<Fr, _>(
            &circuit,
            4,
            &wide_input(publication()),
            &report,
        )
        .unwrap();
        assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
        let pipeline = analyze_underconstrained_with_ucp_and_value_recovery::<Fr, _, _>(
            &circuit,
            4,
            &input,
            targets.clone(),
        )
        .unwrap();
        for target in targets {
            let cell = report
                .cells
                .iter()
                .find(|cell| cell.cell == target)
                .unwrap();
            assert_eq!(
                pipeline.ucp_result.value_facts.domain(&target),
                cell.domain.as_ref()
            );
        }
    }
}

#[test]
fn full_width_publication_is_used_by_smt_only_and_legacy_analyzer() {
    use crate::io::analyzer_io_type::AnalyzerOutputStatus;
    let input = wide_input(publication());
    let circuit = PublishedAffineCircuit::<false>;
    let mut analyzer = Analyzer::<Fr>::new(
        &circuit,
        4,
        AnalyzerType::UnderconstrainedCircuit,
        Some(&input),
    )
    .unwrap();
    analyzer.set_smt_timeout_ms(Some(2_000)).unwrap();
    let output = analyzer
        .query_ucp_cell_uniqueness_with_value(&input, &CellId::advice(0, 0))
        .unwrap();
    assert_eq!(output.result, SemanticQueryResult::ProvenUnique);
    assert_eq!(output.value, Some(BigInt::from(1) << 200usize));
    // Use a fresh encoder: the old whole-witness analyzer must not inherit UCP assertions.
    let wrapped = wide_input(publication() - super::extractor::field_modulus::<Fr>());
    let mut analyzer = Analyzer::<Fr>::new(
        &circuit,
        4,
        AnalyzerType::UnderconstrainedCircuit,
        Some(&wrapped),
    )
    .unwrap();
    assert_eq!(
        analyzer
            .analyze_underconstrained(&wrapped)
            .unwrap()
            .output_status,
        AnalyzerOutputStatus::NotUnderconstrainedLocal
    );
}

#[test]
fn wide_public_sum_still_allows_multiple_private_operands() {
    let circuit = PublishedAffineCircuit::<true>;
    MockProver::run(
        4,
        &circuit,
        vec![vec![affine_secret() * Fr::from(3) + Fr::from(7)]],
    )
    .unwrap()
    .assert_satisfied();
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &wide_input(publication()),
        [CellId::advice(0, 0), CellId::advice(1, 0)],
        PrivacyAnalysisOptions {
            max_semantic_queries: 2,
            solver_timeout_ms: Some(2_000),
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(report.summary.exact_values, 0);
    assert_eq!(report.summary.non_unique_cells, 2);
    assert!(report
        .cells
        .iter()
        .all(|cell| cell.uniqueness == PrivateCellUniqueness::NonUnique && cell.domain.is_none()));
}

#[test]
fn oversized_public_observation_is_an_error_even_if_field_reduction_would_fit() {
    let circuit = PublishedAffineCircuit::<false>;
    let oversized = publication()
        + (super::extractor::field_modulus::<Fr>() << super::value::MAX_VALUE_BITS as usize);
    let input = wide_input(oversized);
    let target = CellId::advice(0, 0);
    assert!(analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input,
        [target.clone()],
        PrivacyAnalysisOptions::default()
    )
    .is_err());
    assert!(
        super::pipeline::analyze_underconstrained_with_ucp::<Fr, _, _>(
            &circuit,
            4,
            &input,
            [target]
        )
        .is_err()
    );
    assert!(Analyzer::<Fr>::new(
        &circuit,
        4,
        AnalyzerType::UnderconstrainedCircuit,
        Some(&input)
    )
    .is_err());
}
