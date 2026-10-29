//! Before/after actual solver-invocation measurements. Run serially with --ignored.
use super::{
    cell::CellId,
    privacy::{analyze_private_recoverability, PrivacyAnalysisOptions},
    privacy_discovery::PrivacyDomainDiscoveryOptions,
    privacy_discovery_tests::{
        discovery_demo_input, discovery_demo_targets, UnboundedProjectionCircuit, TWO_ROOTS, UNIQUE,
    },
    privacy_domain::PrivacyDomainRefinementOptions,
    privacy_domain_tests::FiniteProjectionCircuit,
    privacy_validation::{validate_private_recovery_report, RecoveryValidationStatus},
};
use crate::{
    circuit_analyzer::halo2_proofs_libs::*, io::analyzer_io_type::AnalyzerInput,
    smt_solver::process::invocation_count,
};
use std::{fs::File, io::Write};

fn measure<C: Circuit<Fr>>(
    writer: &mut File,
    name: &str,
    circuit: &C,
    k: u32,
    input: &AnalyzerInput,
    targets: &[CellId],
    repeats: usize,
) {
    for profile in ["semantic", "refinement", "discovery", "combined"] {
        let options = PrivacyAnalysisOptions {
            max_semantic_queries: 8,
            solver_timeout_ms: Some(2_000),
            initial_sat_timeout_ms: None,
            search: super::privacy::PrivacySearchOptions {
                retry_solver_timeout_ms: None,
                ..Default::default()
            },
            domain_refinement: PrivacyDomainRefinementOptions {
                max_solver_checks: if matches!(profile, "refinement" | "combined") {
                    32
                } else {
                    0
                },
                max_candidates_per_cell: 16,
            },
            domain_discovery: PrivacyDomainDiscoveryOptions {
                max_solver_checks: if matches!(profile, "discovery" | "combined") {
                    16
                } else {
                    0
                },
                max_values_per_cell: 4,
                ..Default::default()
            },
        };
        for trial in 0..=repeats {
            let before = invocation_count();
            let report = analyze_private_recoverability::<Fr, _, _>(
                circuit,
                k,
                input,
                targets.to_vec(),
                options,
            )
            .unwrap();
            let invocations = invocation_count() - before;
            let validation =
                validate_private_recovery_report::<Fr, _>(circuit, k, input, &report).unwrap();
            assert!(matches!(
                validation.status,
                RecoveryValidationStatus::VerifiedDomains
                    | RecoveryValidationStatus::NoDomainClaims
            ));
            if trial > 0 {
                let domains = report
                    .cells
                    .iter()
                    .map(|cell| format!("{}:{:?}:{:?}", cell.cell, cell.uniqueness, cell.domain))
                    .collect::<Vec<_>>()
                    .join(";");
                writeln!(writer, "{name}\t{profile}\t{trial}\t{invocations}\t{}\t{}\t{}\t{:?}\t{}\t{}\t{}\t{domains}",
                    report.semantic_queries, report.domain_refinement_statistics.solver_checks, report.domain_discovery_statistics.solver_checks,
                    report.status, report.summary.exact_values, report.summary.finite_domains, report.elapsed.as_micros()).unwrap();
            }
        }
    }
}

#[test]
#[ignore = "Before/after solver invocation counts; set PRIVACY_SEARCH_MEASUREMENT_OUTPUT and run serially"]
fn privacy_search_invocation_measurements() {
    let output = std::env::var("PRIVACY_SEARCH_MEASUREMENT_OUTPUT").expect("Set output TSV path");
    let repeats = std::env::var("PRIVACY_SEARCH_MEASUREMENT_REPEATS")
        .ok()
        .map(|value| value.parse().unwrap())
        .unwrap_or(3);
    let mut writer = File::create(output).unwrap();
    writeln!(writer, "case\tprofile\ttrial\tsolver_invocations\tsemantic_queries\trefinement_checks\tdiscovery_checks\tstatus\texact\tfinite\telapsed_us\tdomains").unwrap();
    let input = discovery_demo_input();
    let targets = discovery_demo_targets();
    measure(
        &mut writer,
        "two_roots",
        &UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0)),
        4,
        &input,
        &targets,
        repeats,
    );
    measure(
        &mut writer,
        "singleton",
        &UnboundedProjectionCircuit::<UNIQUE>::new(Fr::from(1), Fr::from(3)),
        4,
        &input,
        &targets,
        repeats,
    );
    measure(
        &mut writer,
        "lookup_two_roots",
        &FiniteProjectionCircuit::<false>::new(3),
        5,
        &input,
        &targets,
        repeats,
    );
    let mut negative = input.clone();
    negative
        .verification_input
        .instance_cells
        .insert("I-0-0".into(), (-11).into());
    measure(
        &mut writer,
        "lookup_singleton",
        &FiniteProjectionCircuit::<false>::new(11),
        5,
        &negative,
        &targets,
        repeats,
    );
    measure(
        &mut writer,
        "lookup_offset",
        &FiniteProjectionCircuit::<false, true>::new(3),
        5,
        &input,
        &targets,
        repeats,
    );
}
