//! A valtozatlan logikaju tartomanyellenorzott egyenlegkapcsolast futtatja a visszaallitason.
//! A v2-es vegosszeg a kapcsolason kivul, polinom-megnyitassal publikus, ezert itt nincs instance.

use super::upstream::{entry::Entry, univariate_grand_sum::UnivariateGrandSum};
use crate::{
    circuit_analyzer::{
        analyzable::Analyzable,
        halo2_proofs_libs::{Fr, MockProver},
        ucp::{
            cell::CellId,
            extractor::extract_ucp_problem_with_targets,
            privacy::{analyze_private_recoverability, PrivacyAnalysisOptions},
        },
    },
    io::analyzer_io_type::{AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod},
};
use num_bigint::BigUint;
use std::{collections::HashMap, time::Instant};

const K: u32 = 17;
const USERS: usize = 2;
const CURRENCIES: usize = 1;
const BALANCE_COLUMN: usize = 1;

fn circuit(balances: [u64; USERS]) -> UnivariateGrandSum<USERS, CURRENCIES> {
    UnivariateGrandSum::init(
        balances
            .iter()
            .enumerate()
            .map(|(index, balance)| {
                Entry::new(format!("user{index}"), [BigUint::from(*balance)]).unwrap()
            })
            .collect(),
    )
}

fn targets() -> Vec<CellId> {
    (0..USERS)
        .map(|row| CellId::advice(BALANCE_COLUMN, i32::try_from(row).unwrap()))
        .collect()
}

fn input() -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::None,
        verification_input: VerificationInput {
            instance_cells: HashMap::new(),
            iterations: 1,
        },
        lookup_method: LookupMethod::InlineConstraints,
    }
}

#[test]
fn summa_mock_prover_accepts_u64_balances() {
    let started = Instant::now();
    MockProver::run(K, &circuit([11_888, 3_500]), vec![vec![]])
        .unwrap()
        .assert_satisfied();
    println!("Summa MockProver: {:?}", started.elapsed());
}

#[test]
#[ignore = "Teljes elemzes; futtatas: cargo test --release --no-default-features --features use_pse_halo2_proofs --lib external_examples::summa -- --ignored --nocapture --test-threads=1"]
fn summa_ucp_extraction_and_fixpoint() {
    let started = Instant::now();
    let analyzable = Analyzable::<Fr>::config_and_synthesize(&circuit([11_888, 3_500]), K).unwrap();
    println!("Summa synthesis: {:?}", started.elapsed());
    let started = Instant::now();
    let problem = extract_ucp_problem_with_targets(&analyzable, targets());
    println!(
        "Summa extraction: {:?}; {} expressions, {} lookup domains, {} lookup relations",
        started.elapsed(),
        problem.expressions.len(),
        problem.expression_domains.len(),
        problem.lookups.len()
    );
    let started = Instant::now();
    let result = problem.analyze_with_values(
        problem.initial_facts.clone(),
        problem.initial_value_facts.clone(),
    );
    println!("Summa UCP fixpoint: {:?}", started.elapsed());
    for cell in targets() {
        println!(
            "  {cell}: unique={} domain={:?}",
            result.facts.is_unique(&cell),
            result.value_facts.domain(&cell)
        );
    }
}

#[test]
#[ignore = "Teljes elemzes; futtatas: cargo test --release --no-default-features --features use_pse_halo2_proofs --lib external_examples::summa -- --ignored --nocapture --test-threads=1"]
fn summa_recovery_without_public_total() {
    let mut options = PrivacyAnalysisOptions::default();
    options.solver_timeout_ms = Some(3_000);
    options.initial_sat_timeout_ms = Some(60_000);
    options.search.retry_solver_timeout_ms = None;
    let started = Instant::now();
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit([11_888, 3_500]),
        K,
        &input(),
        targets(),
        options,
    )
    .unwrap();
    println!("Summa recovery: {:?}\n{report}", started.elapsed());
}
