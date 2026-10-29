//! Full upstream Poseidon circuit plus an explicitly local publication control.
//! A solver budget failure is an incomplete result, never evidence of secrecy.
use super::{
    cell::CellId,
    privacy::{analyze_private_recoverability, PrivacyAnalysisOptions, PrivacyAnalysisStatus},
    privacy_validation::{validate_private_recovery_report, RecoveryValidationStatus},
    value::UcpValueDomain,
};
use crate::{
    circuit_analyzer::{analyzable::Analyzable, halo2_proofs_libs::*},
    io::analyzer_io_type::{AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod},
};
use num_bigint::BigInt;

pub(super) const POSEIDON_K: u32 = 7;

pub(super) mod upstream {
    use super::*;
    use ff::Field;
    use halo2_gadgets::poseidon::{
        primitives::{self as poseidon, generate_constants, ConstantLength, Mds, Spec},
        Hash, Pow5Chip, Pow5Config,
    };
    use std::{convert::TryInto, marker::PhantomData};
    use zcash_halo2_proofs::pasta::Fp;

    // Unchanged excerpt from the pinned upstream benchmark; imports live in this adapter.
    include!("fixtures/halo2_poseidon_benchmark_circuit.rs");

    pub(crate) fn original(message: [Fr; 2]) -> impl Circuit<Fr> {
        HashCircuit::<MySpec<3, 2>, 3, 2, 2> {
            message: Value::known(message),
            _spec: PhantomData,
        }
    }

    pub(crate) fn digest(message: [Fr; 2]) -> Fr {
        poseidon::Hash::<_, MySpec<3, 2>, ConstantLength<2>, 3, 2>::init().hash(message)
    }

    #[derive(Clone)]
    pub(crate) struct PublicationControl {
        message: [Fr; 2],
    }

    #[derive(Clone, Debug)]
    pub(crate) struct PublicationConfig {
        core: MyConfig<3, 2, 2>,
        selector: Selector,
        observations: [Column<Advice>; 2],
        public: [Column<Instance>; 2],
    }

    impl Circuit<Fr> for PublicationControl {
        type Config = PublicationConfig;
        type FloorPlanner = SimpleFloorPlanner;
        fn without_witnesses(&self) -> Self {
            Self {
                message: [Fr::from(0); 2],
            }
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let core = <HashCircuit<MySpec<3, 2>, 3, 2, 2> as Circuit<Fr>>::configure(meta);
            let sum = meta.instance_column();
            let weighted = meta.instance_column();
            let observations = [meta.advice_column(), meta.advice_column()];
            for column in observations {
                meta.enable_equality(column);
            }
            meta.enable_equality(sum);
            meta.enable_equality(weighted);
            let selector = meta.selector();
            meta.create_gate("local extra observations of a hashed message", |meta| {
                let q = meta.query_selector(selector);
                let a = meta.query_advice(core.input[0], Rotation::cur());
                let b = meta.query_advice(core.input[1], Rotation::cur());
                vec![
                    q.clone()
                        * (meta.query_advice(observations[0], Rotation::cur())
                            - a.clone()
                            - b.clone()),
                    q * (meta.query_advice(observations[1], Rotation::cur())
                        - a
                        - Expression::Constant(Fr::from(2)) * b),
                ]
            });
            PublicationConfig {
                core,
                selector,
                observations,
                public: [sum, weighted],
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let chip = Pow5Chip::construct(config.core.poseidon_config.clone());
            let (message, public_cells) = layouter.assign_region(
                || "load message",
                |mut region| {
                    // Extra derived observations are published through instance equality bindings.
                    config.selector.enable(&mut region, 0)?;
                    let mut cells = Vec::new();
                    for i in 0..2 {
                        cells.push(region.assign_advice(
                            || format!("load message_{i}"),
                            config.core.input[i],
                            0,
                            || Value::known(self.message[i]),
                        )?);
                    }
                    let values = [
                        self.message[0] + self.message[1],
                        self.message[0] + Fr::from(2) * self.message[1],
                    ];
                    let mut public_cells = Vec::new();
                    for (i, value) in values.into_iter().enumerate() {
                        public_cells.push(region.assign_advice(
                            || "linear publication",
                            config.observations[i],
                            0,
                            || Value::known(value),
                        )?);
                    }
                    Ok((cells.try_into().unwrap(), public_cells))
                },
            )?;
            for (cell, column) in public_cells.iter().zip(config.public) {
                layouter.constrain_instance(cell.cell(), column, 0)?;
            }
            // Same external chip, parameters, 8 full rounds and 56 partial rounds.
            let hasher = Hash::<_, _, MySpec<3, 2>, ConstantLength<2>, 3, 2>::init(
                chip,
                layouter.namespace(|| "init"),
            )?;
            let output = hasher.hash(layouter.namespace(|| "hash"), message)?;
            layouter.constrain_instance(output.cell(), config.core.expected, 0)
        }
    }

    pub(crate) fn publication_control(message: [Fr; 2]) -> PublicationControl {
        PublicationControl { message }
    }
}

// Select only the message-loading region, not round states, copies, or output cells.
pub(super) fn private_message_cells<C: Circuit<Fr>>(circuit: &C) -> Vec<CellId> {
    let analyzable = Analyzable::<Fr>::config_and_synthesize(circuit, POSEIDON_K).unwrap();
    let regions: Vec<_> = analyzable
        .regions
        .iter()
        .filter(|region| region.name == "load message")
        .collect();
    assert_eq!(regions.len(), 1);
    let cells: Vec<_> = regions[0]
        .cells
        .iter()
        // The pinned upstream message occupies state columns 0 and 1; control outputs do not.
        .filter(|(column, _)| column.index() < 2)
        .map(|(column, row)| {
            assert_eq!(column.column_type(), &Any::Advice);
            CellId::advice(column.index(), i32::try_from(*row).unwrap())
        })
        .collect();
    assert_eq!(cells.len(), 2, "Upstream message layout changed");
    cells
}

pub(super) fn observations(message: [Fr; 2], control: bool) -> AnalyzerInput {
    let mut publications = vec![(
        "I-0-0".into(),
        super::plonkish::field_to_bigint(&upstream::digest(message)),
    )];
    if control {
        publications.push((
            "I-1-0".into(),
            super::plonkish::field_to_bigint(&(message[0] + message[1])),
        ));
        publications.push((
            "I-2-0".into(),
            super::plonkish::field_to_bigint(&(message[0] + Fr::from(2) * message[1])),
        ));
    }
    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput::new(publications, 1),
        lookup_method: LookupMethod::InlineConstraints,
    }
}

#[test]
fn external_poseidon_original_checks_real_hash_and_rejects_wrong_message() {
    let message = [Fr::from(2), Fr::from(3)];
    let digest = upstream::digest(message);
    MockProver::run(POSEIDON_K, &upstream::original(message), vec![vec![digest]])
        .unwrap()
        .assert_satisfied();
    assert!(MockProver::run(
        POSEIDON_K,
        &upstream::original([Fr::from(2), Fr::from(4)]),
        vec![vec![digest]]
    )
    .unwrap()
    .verify()
    .is_err());
    let targets = private_message_cells(&upstream::original(message));
    assert_eq!(targets.len(), 2);
    assert_ne!(targets[0], targets[1]);
    // The native digest is a public statement; the message is never passed to recovery as a fact.
    assert!(
        observations(message, false)
            .verification_input
            .instance_cells["I-0-0"]
            .bits()
            > 64
    );
}

#[test]
fn external_poseidon_publication_control_checks_both_added_observations() {
    let message = [Fr::from(2), Fr::from(3)];
    let circuit = upstream::publication_control(message);
    let public = vec![
        vec![upstream::digest(message)],
        vec![Fr::from(5)],
        vec![Fr::from(8)],
    ];
    MockProver::run(POSEIDON_K, &circuit, public.clone())
        .unwrap()
        .assert_satisfied();
    for column in 0..3 {
        let mut wrong = public.clone();
        wrong[column][0] += Fr::from(1);
        assert!(MockProver::run(POSEIDON_K, &circuit, wrong)
            .unwrap()
            .verify()
            .is_err());
    }
    assert_eq!(
        private_message_cells(&circuit),
        private_message_cells(&upstream::original(message))
    );
}

#[test]
fn external_poseidon_publication_control_ucp_derives_message_in_a_satisfied_context() {
    let message = [Fr::from(2), Fr::from(3)];
    let circuit = upstream::publication_control(message);
    let input = observations(message, true);
    MockProver::run(
        POSEIDON_K,
        &circuit,
        vec![
            vec![upstream::digest(message)],
            vec![Fr::from(5)],
            vec![Fr::from(8)],
        ],
    )
    .unwrap()
    .assert_satisfied();
    let analyzable = Analyzable::<Fr>::config_and_synthesize(&circuit, POSEIDON_K).unwrap();
    let problem = super::extractor::extract_ucp_problem(&analyzable);
    let mut values = problem.initial_value_facts.clone();
    for (name, value) in input.verification_input.instance_cells {
        values.mark_known(
            super::value::parse_cell_id(&name).unwrap(),
            super::value::normalize_field_value(value, &problem.field_modulus).unwrap(),
        );
    }
    // Kernel propagation is tested separately from the public API's original-SAT guard.
    // No advice assignment is seeded into Delta; MockProver establishes this fixture is valid.
    let result = problem.analyze_with_values(problem.initial_facts.clone(), values);
    println!("Poseidon kernel: expressions={}, witness_cells={}, domains={}, message={:?}, publication={:?}/{:?}", problem.expressions.len(), problem.witness_cells.len(), result.value_facts.domains().len(), private_message_cells(&circuit), result.value_facts.domain(&CellId::advice(4, 0)), result.value_facts.domain(&CellId::advice(5, 0)));
    for (cell, value) in private_message_cells(&circuit).iter().zip([2, 3]) {
        assert_eq!(
            result.value_facts.domain(cell),
            Some(&UcpValueDomain::exact(BigInt::from(value)))
        );
    }
}

#[test]
#[ignore = "Full hash inversion is resource-relative; run explicitly with --ignored --nocapture --test-threads=1"]
fn external_poseidon_records_bounded_recovery_outcomes() {
    let message = [Fr::from(2), Fr::from(3)];
    println!("case\tstatus\texact\tunresolved\tsat_checks\tcell_queries\telapsed_ms");
    probe(
        "poseidon_original",
        &upstream::original(message),
        &observations(message, false),
        false,
    );
    probe(
        "poseidon_publication_control",
        &upstream::publication_control(message),
        &observations(message, true),
        true,
    );
}

#[test]
fn external_poseidon_publication_control_recovers_private_message() {
    let message = [Fr::from(2), Fr::from(3)];
    let circuit = upstream::publication_control(message);
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        POSEIDON_K,
        &observations(message, true),
        private_message_cells(&circuit),
        PrivacyAnalysisOptions {
            max_semantic_queries: 0,
            solver_timeout_ms: Some(2_000),
            ..Default::default()
        },
    )
    .unwrap();
    println!("{report}");
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(report.summary.exact_values, 2);
    assert_eq!(report.satisfiability_checks, 1);
    assert_eq!(report.semantic_queries, 0);
    for (cell, value) in report.cells.iter().zip([2, 3]) {
        assert_eq!(
            cell.domain,
            Some(UcpValueDomain::exact(BigInt::from(value)))
        );
    }
    let validation = validate_private_recovery_report::<Fr, _>(
        &circuit,
        POSEIDON_K,
        &observations(message, true),
        &report,
    )
    .unwrap();
    println!("{validation}");
    assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
    assert_eq!(validation.domain_queries, 2);
    assert_eq!(validation.subset_checks, 2);
    assert_eq!(validation.solver_checks, 3);
}

fn probe<C: Circuit<Fr>>(id: &str, circuit: &C, input: &AnalyzerInput, expect_recovery: bool) {
    let report = analyze_private_recoverability::<Fr, _, _>(
        circuit,
        POSEIDON_K,
        input,
        private_message_cells(circuit),
        PrivacyAnalysisOptions {
            max_semantic_queries: 2,
            solver_timeout_ms: Some(2_000),
            ..Default::default()
        },
    )
    .unwrap();
    println!(
        "{}\t{:?}\t{}\t{}\t{}\t{}\t{:.3}",
        id,
        report.status,
        report.summary.exact_values,
        report.summary.unresolved_uniqueness,
        report.satisfiability_checks,
        report.semantic_queries,
        report.elapsed.as_secs_f64() * 1000.0
    );
    println!("{report}");
    assert_ne!(report.status, PrivacyAnalysisStatus::Inconsistent);
    if report.ucp_result.is_none() {
        assert_eq!(report.status, PrivacyAnalysisStatus::SolverUnknown);
        assert!(report.cells.iter().all(|cell| cell.domain.is_none()));
    }
    if expect_recovery && report.status == PrivacyAnalysisStatus::Analyzed {
        assert_eq!(report.summary.exact_values, 2);
        for (cell, value) in report.cells.iter().zip([2, 3]) {
            assert_eq!(
                cell.domain,
                Some(UcpValueDomain::exact(BigInt::from(value)))
            );
        }
    }
    if report.cells.iter().any(|cell| cell.domain.is_some()) {
        match validate_private_recovery_report::<Fr, _>(circuit, POSEIDON_K, input, &report) {
            Ok(validation) => {
                assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains)
            }
            Err(error)
                if error
                    .downcast_ref::<crate::smt_solver::smt_parser::UnknownSolverResult>()
                    .is_some() =>
            {
                println!("{id}: validation incomplete: {error:#}");
            }
            Err(error) => panic!("{id}: validation failed: {error:#}"),
        }
    }
}
