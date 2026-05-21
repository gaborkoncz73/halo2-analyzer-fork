use super::{
    cell::CellId,
    pipeline::{analyze_underconstrained_with_ucp, UcpAnalyzerPipelineStatus},
};
use crate::{
    circuit_analyzer::{analyzer::Analyzer, halo2_proofs_libs::*},
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerOutputStatus, AnalyzerType, LookupMethod, VerificationInput,
        VerificationMethod,
    },
};
use std::{collections::HashMap, marker::PhantomData, time::Instant};

#[derive(Clone, Debug)]
struct LinearChainConfig {
    x: Column<Advice>,
    y: Column<Advice>,
    z: Column<Advice>,
    selector: Selector,
}

#[derive(Clone, Debug, Default)]
struct LinearChainCircuit {
    _marker: PhantomData<Fr>,
}

#[derive(Clone, Debug)]
struct SquareZeroConfig {
    x: Column<Advice>,
}

#[derive(Clone, Debug, Default)]
struct SquareZeroCircuit {
    _marker: PhantomData<Fr>,
}

impl Circuit<Fr> for LinearChainCircuit {
    type Config = LinearChainConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let public = meta.instance_column();
        let x = meta.advice_column();
        let y = meta.advice_column();
        let z = meta.advice_column();
        let selector = meta.selector();

        meta.create_gate("linear ucp chain", |meta| {
            let selector = meta.query_selector(selector);
            let public = meta.query_instance(public, Rotation::cur());
            let x = meta.query_advice(x, Rotation::cur());
            let y = meta.query_advice(y, Rotation::cur());
            let z = meta.query_advice(z, Rotation::cur());

            vec![
                selector.clone() * (x.clone() + public - Expression::Constant(Fr::from(5))),
                selector.clone() * (y.clone() - x - Expression::Constant(Fr::from(1))),
                selector * (z - y - Expression::Constant(Fr::from(1))),
            ]
        });

        LinearChainConfig { x, y, z, selector }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> std::result::Result<(), Error> {
        layouter.assign_region(
            || "linear chain row",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                region.assign_advice(|| "x", config.x, 0, || Value::known(Fr::from(3)))?;
                region.assign_advice(|| "y", config.y, 0, || Value::known(Fr::from(4)))?;
                region.assign_advice(|| "z", config.z, 0, || Value::known(Fr::from(5)))?;
                Ok(())
            },
        )
    }
}

impl Circuit<Fr> for SquareZeroCircuit {
    type Config = SquareZeroConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let x = meta.advice_column();

        meta.create_gate("square zero", |meta| {
            let x = meta.query_advice(x, Rotation::cur());

            vec![x.clone() * x]
        });

        SquareZeroConfig { x }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> std::result::Result<(), Error> {
        layouter.assign_region(
            || "square zero row",
            |mut region| {
                region.assign_advice(|| "x", config.x, 0, || Value::known(Fr::zero()))?;
                Ok(())
            },
        )
    }
}

fn specific_input(value: i64) -> AnalyzerInput {
    let mut instance_cells = HashMap::new();
    instance_cells.insert("I-0-0".to_string(), value);

    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput {
            instance_cells,
            iterations: 1,
        },
        lookup_method: LookupMethod::InlineConstraints,
    }
}

fn no_input() -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::None,
        verification_input: VerificationInput {
            instance_cells: HashMap::new(),
            iterations: 1,
        },
        lookup_method: LookupMethod::InlineConstraints,
    }
}

fn run_analyzer_only<CircuitType: Circuit<Fr>>(
    circuit: &CircuitType,
    k: u32,
    analyzer_input: &AnalyzerInput,
) -> (AnalyzerOutputStatus, std::time::Duration) {
    let start = Instant::now();
    let mut analyzer = Analyzer::<Fr>::new(
        circuit,
        k,
        AnalyzerType::UnderconstrainedCircuit,
        Some(analyzer_input),
    )
    .unwrap();
    let output = analyzer.analyze_underconstrained(analyzer_input).unwrap();

    (output.output_status, start.elapsed())
}

#[test]
fn compares_analyzer_only_with_ucp_pipeline_when_ucp_solves_targets() {
    let circuit = LinearChainCircuit::default();
    let analyzer_input = specific_input(2);

    let (analyzer_status, analyzer_duration) = run_analyzer_only(&circuit, 4, &analyzer_input);

    let pipeline_start = Instant::now();
    let pipeline_output = analyze_underconstrained_with_ucp::<Fr, _, _>(
        &circuit,
        4,
        &analyzer_input,
        [CellId::advice(2, 0)],
    )
    .unwrap();
    let pipeline_duration = pipeline_start.elapsed();

    println!(
        "linear_chain analyzer_only={:?} analyzer_time={:?} pipeline_status={:?} pipeline_time={:?} used_smt={} semantic_queries={} smt_learned={:?}",
        analyzer_status,
        analyzer_duration,
        pipeline_output.status,
        pipeline_duration,
        pipeline_output.used_smt,
        pipeline_output.semantic_queries,
        pipeline_output.smt_learned_cells,
    );

    assert_eq!(
        analyzer_status,
        AnalyzerOutputStatus::NotUnderconstrainedLocal
    );
    assert_eq!(
        pipeline_output.status,
        UcpAnalyzerPipelineStatus::VerifiedByUcp
    );
    assert!(!pipeline_output.used_smt);
    assert_eq!(pipeline_output.semantic_queries, 0);
    assert!(pipeline_output.target_check.all_targets_unique());
}

#[test]
fn compares_analyzer_only_with_ucp_pipeline_when_smt_learns_target() {
    let circuit = SquareZeroCircuit::default();
    let analyzer_input = no_input();

    let (analyzer_status, analyzer_duration) = run_analyzer_only(&circuit, 4, &analyzer_input);

    let pipeline_start = Instant::now();
    let pipeline_output = analyze_underconstrained_with_ucp::<Fr, _, _>(
        &circuit,
        4,
        &analyzer_input,
        [CellId::advice(0, 0)],
    )
    .unwrap();
    let pipeline_duration = pipeline_start.elapsed();

    println!(
        "square_zero analyzer_only={:?} analyzer_time={:?} pipeline_status={:?} pipeline_time={:?} used_smt={} semantic_queries={} smt_learned={:?}",
        analyzer_status,
        analyzer_duration,
        pipeline_output.status,
        pipeline_duration,
        pipeline_output.used_smt,
        pipeline_output.semantic_queries,
        pipeline_output.smt_learned_cells,
    );

    assert_eq!(
        analyzer_status,
        AnalyzerOutputStatus::NotUnderconstrainedLocal
    );
    assert_eq!(
        pipeline_output.status,
        UcpAnalyzerPipelineStatus::VerifiedBySmt
    );
    assert!(pipeline_output.used_smt);
    assert_eq!(pipeline_output.semantic_queries, 1);
    assert_eq!(
        pipeline_output.smt_learned_cells,
        vec![CellId::advice(0, 0)]
    );
    assert!(pipeline_output.target_check.all_targets_unique());
}
