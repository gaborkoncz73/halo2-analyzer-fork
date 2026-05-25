//! UCP pipeline demos on real sample circuits from `sample_circuits`.
//!
//! The smaller `demo_tests` module shows the paper rules on hand-written UCP
//! expressions. This file is the next step: it runs the extractor, UCP engine,
//! ChooseVar and SMT feedback loop on actual Halo2 circuits already present in
//! the repository.

use super::{
    cell::CellId,
    extractor::extract_ucp_problem_with_targets,
    pipeline::{analyze_underconstrained_with_ucp, UcpAnalyzerPipelineStatus},
};
use crate::{
    circuit_analyzer::{analyzable::Analyzable, halo2_proofs_libs::*},
    io::analyzer_io_type::{AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod},
    sample_circuits::zcash::{
        bit_decomposition::two_bit_decomp::{
            TwoBitDecompCircuit, TwoBitDecompCircuitUnderConstrained,
        },
        simple::decoder_circuits::{CorrectDecoderCircuit, UnderDecoderCircuit},
    },
};
use std::{collections::HashMap, marker::PhantomData};

fn analyzer_input_with_instance(value: i64) -> AnalyzerInput {
    let mut instance_cells = HashMap::new();
    instance_cells.insert("I-0-0".to_string(), value);

    AnalyzerInput {
        verification_method: VerificationMethod::Specific,
        verification_input: VerificationInput {
            instance_cells,
            iterations: 5,
        },
        lookup_method: LookupMethod::InlineConstraints,
    }
}

fn two_bit_targets() -> [CellId; 3] {
    [
        CellId::advice(0, 0), // b0
        CellId::advice(1, 0), // b1
        CellId::advice(2, 0), // x
    ]
}

fn decoder_targets<const W: usize>() -> Vec<CellId> {
    let mut targets = Vec::new();
    for column in 1..=W {
        targets.push(CellId::advice(column, 0));
    }
    targets.push(CellId::advice(W + 1, 0)); // success
    targets
}

// Real sample demo 1:
// A korrekt two-bit decomposition circuitből a pipeline UCP-vel meg tudja
// bizonyítani, hogy b0, b1 és x unique.
//
// Miért érdekes?
//   - az extractor kiszedi a Halo2 gate-eket és copy constraintet,
//   - a root rule megtanulja b0,b1 boolean domainjét,
//   - a base-conv szabály ebből bizonyítja a digit uniqueness-t.
#[test]
fn sample_two_bit_decomp_verified_by_ucp() {
    let circuit = TwoBitDecompCircuit::<Fr>::default();
    let analyzer_input = analyzer_input_with_instance(3);
    let targets = two_bit_targets();

    let output = analyze_underconstrained_with_ucp::<Fr, _, _>(
        &circuit,
        4,
        &analyzer_input,
        targets.clone(),
    )
    .unwrap();

    println!(
        "sample_two_bit_decomp status={:?} used_smt={} semantic_queries={} unresolved_targets={:?} domains={:?}",
        output.status,
        output.used_smt,
        output.semantic_queries,
        output.target_check.unresolved_targets,
        output.ucp_result.value_facts.domains(),
    );

    assert_eq!(output.status, UcpAnalyzerPipelineStatus::VerifiedByUcp);
    assert!(!output.used_smt);
    assert!(output.target_check.all_targets_unique());
    for target in targets {
        assert!(output.ucp_result.facts.is_unique(&target));
    }
}

// Real sample demo 2:
// Az underconstrained two-bit decomposition circuitben a b1 boolean constraint
// hibásan b0-t ellenőrzi. A pipeline ezt targetként b1-en nem fogja UCP-ből
// bizonyítani, és SMT-vel underconstrained esetként refutálja.
#[test]
fn sample_underconstrained_two_bit_decomp_refuted_by_smt() {
    let circuit = TwoBitDecompCircuitUnderConstrained::<Fr>::default();
    let analyzer_input = analyzer_input_with_instance(3);
    let target = CellId::advice(1, 0); // b1

    let output = analyze_underconstrained_with_ucp::<Fr, _, _>(
        &circuit,
        4,
        &analyzer_input,
        [target.clone()],
    )
    .unwrap();

    println!(
        "sample_under_two_bit status={:?} used_smt={} semantic_queries={} unresolved_targets={:?} smt_learned={:?}",
        output.status,
        output.used_smt,
        output.semantic_queries,
        output.target_check.unresolved_targets,
        output.smt_learned_cells,
    );

    assert_eq!(output.status, UcpAnalyzerPipelineStatus::RefutedBySmt);
    assert!(output.used_smt);
    assert!(output.semantic_queries >= 1);
    assert!(!output.ucp_result.facts.is_unique(&target));
}

// Real sample demo 3:
// A correct decoder nagyobb, több gate-es példa. Itt nem kézzel rakjuk össze az
// equationöket: a teljes Halo2 circuitből megyünk végig extractor -> UCP -> SMT
// pipeline-on. A cél az összes output bit és a success cella constrained volta.
#[test]
fn sample_correct_decoder_targets_are_constrained() {
    const W: usize = 8;
    let circuit = CorrectDecoderCircuit::<Fr, W>(PhantomData);
    let analyzer_input = analyzer_input_with_instance(2);
    let targets = decoder_targets::<W>();

    let output = analyze_underconstrained_with_ucp::<Fr, _, _>(
        &circuit,
        5,
        &analyzer_input,
        targets.clone(),
    )
    .unwrap();

    println!(
        "sample_correct_decoder status={:?} used_smt={} semantic_queries={} unresolved_targets={:?} smt_learned={:?}",
        output.status,
        output.used_smt,
        output.semantic_queries,
        output.target_check.unresolved_targets,
        output.smt_learned_cells,
    );

    assert!(matches!(
        output.status,
        UcpAnalyzerPipelineStatus::VerifiedByUcp | UcpAnalyzerPipelineStatus::VerifiedBySmt
    ));
    assert!(output.target_check.all_targets_unique());
    for target in targets {
        assert!(output.ucp_result.facts.is_unique(&target));
    }
}

// Real sample demo 4:
// Az underconstrained decoder ugyanazt a witness-t kielégíti MockProverrel, de
// nincs elég constraint ahhoz, hogy az összes output egyértelmű legyen. Ez a
// pipeline szempontjából látványosabb, mint egy kézzel írt toy példa.
#[test]
fn sample_underconstrained_decoder_refuted_on_outputs() {
    const W: usize = 8;
    let circuit = UnderDecoderCircuit::<Fr, W>(PhantomData);
    let analyzer_input = analyzer_input_with_instance(2);
    let targets = decoder_targets::<W>();

    let output =
        analyze_underconstrained_with_ucp::<Fr, _, _>(&circuit, 5, &analyzer_input, targets)
            .unwrap();

    println!(
        "sample_under_decoder status={:?} used_smt={} semantic_queries={} unresolved_targets={:?} smt_learned={:?}",
        output.status,
        output.used_smt,
        output.semantic_queries,
        output.target_check.unresolved_targets,
        output.smt_learned_cells,
    );

    assert_eq!(output.status, UcpAnalyzerPipelineStatus::RefutedBySmt);
    assert!(output.used_smt);
    assert!(output.semantic_queries >= 1);
}

// Real sample demo 5:
// Nem pipeline döntés, hanem extractor smoke test: valódi decoderből tényleg sok
// UCP expression és witness cella jön ki. Ez segít látni, hogy már nem csak
// kézzel írt expression-listán dolgozik a rendszer.
#[test]
fn sample_decoder_extractor_builds_nontrivial_ucp_problem() {
    const W: usize = 8;
    let circuit = CorrectDecoderCircuit::<Fr, W>(PhantomData);
    let analyzable = Analyzable::config_and_synthesize(&circuit, 5).unwrap();
    let targets = decoder_targets::<W>();
    let problem = extract_ucp_problem_with_targets(&analyzable, targets.clone());

    println!(
        "sample_decoder_extractor expressions={} initial_k={} witnesses={} targets={}",
        problem.expressions.len(),
        problem.initial_facts.unique_cells().len(),
        problem.witness_cells.len(),
        problem.output_cells.len(),
    );

    assert!(problem.expressions.len() >= W * 3);
    assert!(problem.witness_cells.len() >= W * 2);
    assert_eq!(problem.output_cells, targets);
}
