//! Serial, same-target comparisons of private recovery against an SMT-only reference.
//! The full timing suite is opt-in; normal tests check results, never speed ratios.

use super::{
    cell::CellId,
    demo_tests::{
        linear_masking_input, linear_masking_targets, LinearMaskingCircuit, LinearMaskingMode,
        PrivateAmountBitsCircuit, SecretCommitmentCircuit, SmtAnchorChainCircuit,
    },
    external_circuit_tests::{halo2_book, observations, private_inputs},
    external_poseidon_tests::{
        observations as poseidon_observations, private_message_cells,
        upstream as poseidon_upstream, POSEIDON_K,
    },
    external_range_tests::{range_private_inputs, RangeAggregateCircuit, RANGE_K},
    privacy::{
        analyze_private_recoverability, prepare_privacy_analysis, PrivacyAnalysisOptions,
        PrivacyAnalysisReport, PrivacyAnalysisStatus, PrivacySearchOptions, PrivateCellUniqueness,
        PRIVACY_SAT_HINT_POLICY, PRIVACY_SEARCH_POLICY, PRIVACY_SMT_DOMAIN_POLICY,
    },
    privacy_discovery::PRIVACY_DOMAIN_DISCOVERY_POLICY,
    privacy_domain::PRIVACY_DOMAIN_REFINEMENT_POLICY,
    privacy_subset::PRIVACY_TARGETED_SUBSET_POLICY,
    privacy_validation::{
        validate_private_recovery_report, RecoveryValidationStatus, PRIVACY_VALIDATION_POLICY,
    },
    value::UcpValueDomain,
};
use crate::{
    circuit_analyzer::{analyzer::SemanticQueryResult, halo2_proofs_libs::*},
    io::analyzer_io_type::{AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod},
    sample_circuits::zcash::bit_decomposition::{
        two_bit_decomp::{TwoBitDecompCircuit, TwoBitDecompCircuitUnderConstrained},
        two_bit_decomp_lookup::TwoBitDecompCircuit as LookupTwoBitDecompCircuit,
    },
    smt_solver::smt_parser::{Satisfiability, UnknownSolverResult},
};
use anyhow::{ensure, Context, Result};
use num_bigint::BigInt;
use std::{
    collections::{BTreeMap, HashMap},
    fs::File,
    io::{BufWriter, Write},
    path::PathBuf,
    process::Command,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

#[derive(Clone, Copy)]
struct CaseSpec {
    id: &'static str,
    origin: &'static str,
    //Derived cells are a performance control, not a claim about private input protection.
    target_role: &'static str,
    k: u32,
    expected_exact: usize,
    expected_non_unique: usize,
}

struct ReferenceCell {
    uniqueness: PrivateCellUniqueness,
    exact: Option<BigInt>,
}

struct SmtReference {
    cells: BTreeMap<CellId, ReferenceCell>,
    elapsed: Duration,
    queries: usize,
    expressions: usize,
    witness_cells: usize,
}

struct Trial {
    ucp_first: bool,
    ucp_elapsed: Duration,
    smt_elapsed: Duration,
    validation_elapsed: Duration,
    ucp_queries: usize,
    target_queries: usize,
    bridge_queries: usize,
    retry_queries: usize,
    progress_rounds: usize,
    smt_queries: usize,
    exact: usize,
    finite_domains: usize,
    unique: usize,
    non_unique: usize,
    validation_domains: usize,
    validation_solver_checks: usize,
    validation_subset_checks: usize,
    validation_status: RecoveryValidationStatus,
    expressions: usize,
    witness_cells: usize,
}

struct CaseMeasurements {
    spec: CaseSpec,
    selected_cells: usize,
    public_observations: String,
    trials: Vec<Trial>,
}

struct IncompleteCase {
    id: &'static str,
    elapsed: Duration,
    reason: String,
}

//Only a solver unknown is an incomplete measurement. Correctness mismatches still fail.
fn collect_case(
    id: &'static str,
    run: impl FnOnce() -> Result<CaseMeasurements>,
    completed: &mut Vec<CaseMeasurements>,
    incomplete: &mut Vec<IncompleteCase>,
) -> Result<()> {
    println!("Measuring {}...", id);
    let started = Instant::now();
    match run() {
        Ok(case) => completed.push(case),
        Err(error) if error.downcast_ref::<UnknownSolverResult>().is_some() => {
            incomplete.push(IncompleteCase {
                id,
                elapsed: started.elapsed(),
                reason: format!("{:#}", error).replace(['\t', '\r', '\n'], " "),
            });
        }
        Err(error) => return Err(error),
    }
    Ok(())
}

fn input(public: Option<i64>) -> AnalyzerInput {
    AnalyzerInput {
        verification_method: if public.is_some() {
            VerificationMethod::Specific
        } else {
            VerificationMethod::None
        },
        verification_input: VerificationInput {
            instance_cells: public
                .map(|value| HashMap::from([("I-0-0".into(), value.into())]))
                .unwrap_or_default(),
            iterations: 1,
        },
        lookup_method: LookupMethod::InlineConstraints,
    }
}

//The reference gets the same validated interface, but never assumes inferred K/Delta.
//Each selected cell is queried independently against the original constraints.
fn smt_reference<C: Circuit<Fr>>(
    circuit: &C,
    k: u32,
    input: &AnalyzerInput,
    targets: &[CellId],
) -> Result<SmtReference> {
    let started = Instant::now();
    let mut context =
        prepare_privacy_analysis::<Fr, _, _>(circuit, k, input, targets.iter().cloned())?;
    ensure!(
        context
            .analyzer
            .check_ucp_satisfiability(&context.analyzer_input)
            .context("SMT-only initial SAT check failed")?
            == Satisfiability::Satisfiable,
        "Measurement reference requires a satisfiable context"
    );
    let mut cells = BTreeMap::new();
    for cell in &context.private_cells {
        let query = context
            .analyzer
            .query_ucp_cell_uniqueness_with_value(&context.analyzer_input, cell)
            .with_context(|| format!("SMT-only cell query failed at {}", cell))?;
        let uniqueness = match query.result {
            SemanticQueryResult::ProvenUnique => PrivateCellUniqueness::Unique,
            SemanticQueryResult::NotUnique => PrivateCellUniqueness::NonUnique,
            SemanticQueryResult::Unknown => PrivateCellUniqueness::Unknown,
            SemanticQueryResult::Overconstrained => anyhow::bail!("Reference became inconsistent"),
        };
        cells.insert(
            cell.clone(),
            ReferenceCell {
                uniqueness,
                exact: query.value,
            },
        );
    }
    Ok(SmtReference {
        queries: cells.len(),
        cells,
        elapsed: started.elapsed(),
        expressions: context.problem.expressions.len(),
        witness_cells: context.problem.witness_cells.len(),
    })
}

fn compare_results(
    report: &PrivacyAnalysisReport,
    reference: &SmtReference,
    spec: CaseSpec,
) -> Result<()> {
    ensure!(
        report.status == PrivacyAnalysisStatus::Analyzed,
        "{}: incomplete recovery",
        spec.id
    );
    ensure!(
        report.cells.len() == reference.cells.len(),
        "Different selected cells"
    );
    for cell in &report.cells {
        let reference = reference
            .cells
            .get(&cell.cell)
            .context("Missing reference cell")?;
        ensure!(
            cell.uniqueness == reference.uniqueness,
            "{}: uniqueness mismatch at {}",
            spec.id,
            cell.cell
        );
        let exact = match &cell.domain {
            Some(UcpValueDomain::Exact(value)) => Some(value),
            _ => None,
        };
        ensure!(
            exact == reference.exact.as_ref(),
            "{}: exact value mismatch at {}",
            spec.id,
            cell.cell
        );
    }
    ensure!(
        report.summary.exact_values == spec.expected_exact,
        "{}: unexpected exact count",
        spec.id
    );
    ensure!(
        report.summary.non_unique_cells == spec.expected_non_unique,
        "{}: unexpected ambiguity count",
        spec.id
    );
    ensure!(
        report.summary.unresolved_uniqueness == 0,
        "{}: unresolved cells",
        spec.id
    );
    Ok(())
}

fn run_trial<C: Circuit<Fr>>(
    spec: CaseSpec,
    circuit: &C,
    input: &AnalyzerInput,
    targets: &[CellId],
    ucp_first: bool,
) -> Result<Trial> {
    let recover = || {
        let report = analyze_private_recoverability::<Fr, _, _>(
            circuit,
            spec.k,
            input,
            targets.iter().cloned(),
            measurement_options(),
        )
        .context("UCP recovery failed")?;
        //The public API now preserves unknown as a report, not a failed proof or a safe secret.
        if matches!(
            report.status,
            PrivacyAnalysisStatus::SolverUnknown | PrivacyAnalysisStatus::QueryLimitReached
        ) {
            return Err(anyhow::Error::new(UnknownSolverResult)
                .context(format!("Incomplete UCP recovery: {}", report)));
        }
        Ok(report)
    };
    //Alternate the order; do not always give one method a warmer process/filesystem cache.
    let (report, reference) = if ucp_first {
        let report = recover()?;
        (report, smt_reference(circuit, spec.k, input, targets)?)
    } else {
        let reference = smt_reference(circuit, spec.k, input, targets)?;
        (recover()?, reference)
    };
    compare_results(&report, &reference, spec)?;
    ensure!(
        report.domain_discovery_statistics.solver_checks == 0
            && report.domain_refinement_statistics.solver_checks == 0,
        "This measurement reference does not perform domain enumeration/refinement"
    );
    //Validation is measured separately, never hidden in the UCP recovery timing.
    let validation = validate_private_recovery_report::<Fr, _>(circuit, spec.k, input, &report)
        .context("Independent domain validation failed")?;
    let expected = if report.summary.exact_values + report.summary.finite_domains == 0 {
        RecoveryValidationStatus::NoDomainClaims
    } else {
        RecoveryValidationStatus::VerifiedDomains
    };
    ensure!(
        validation.status == expected,
        "{}: independent validation failed",
        spec.id
    );
    Ok(Trial {
        ucp_first,
        ucp_elapsed: report.elapsed,
        smt_elapsed: reference.elapsed,
        validation_elapsed: validation.elapsed,
        ucp_queries: report.semantic_queries,
        target_queries: report.search_statistics.target_queries,
        bridge_queries: report.search_statistics.bridge_queries,
        retry_queries: report.search_statistics.retry_queries,
        progress_rounds: report.search_statistics.progress_rounds,
        smt_queries: reference.queries,
        exact: report.summary.exact_values,
        finite_domains: report.summary.finite_domains,
        unique: report.summary.unique_cells,
        non_unique: report.summary.non_unique_cells,
        validation_domains: validation.domain_queries,
        validation_solver_checks: validation.solver_checks,
        validation_subset_checks: validation.subset_checks,
        validation_status: validation.status,
        expressions: reference.expressions,
        witness_cells: reference.witness_cells,
    })
}

fn measure<C: Circuit<Fr>>(
    spec: CaseSpec,
    circuit: &C,
    input: &AnalyzerInput,
    targets: Vec<CellId>,
    repetitions: usize,
) -> Result<CaseMeasurements> {
    ensure!(repetitions > 0, "At least one measurement is required");
    ensure!(
        targets.len() <= PrivacyAnalysisOptions::default().max_semantic_queries,
        "Too many selected cells for the query budget"
    );
    //A complete discarded run warms recovery, the reference and the validation path.
    run_trial(spec, circuit, input, &targets, false)?;
    let trials = (0..repetitions)
        .map(|index| run_trial(spec, circuit, input, &targets, index % 2 == 0))
        .collect::<Result<Vec<_>>>()?;
    let public_observations = input
        .verification_input
        .instance_cells
        .iter()
        .collect::<BTreeMap<_, _>>()
        .into_iter()
        .map(|(cell, value)| format!("{}={}", cell, value))
        .collect::<Vec<_>>()
        .join(";");
    Ok(CaseMeasurements {
        spec,
        selected_cells: targets.len(),
        public_observations,
        trials,
    })
}

fn repository_case(id: &'static str, repetitions: usize) -> Result<CaseMeasurements> {
    let targets = vec![CellId::advice(0, 0), CellId::advice(1, 0)];
    let spec = CaseSpec {
        id,
        origin: "repository_sample",
        target_role: "private_input",
        k: 4,
        expected_exact: 2,
        expected_non_unique: 0,
    };
    match id {
        "two_bit_gates" => measure(
            spec,
            &TwoBitDecompCircuit::<Fr>::default(),
            &input(Some(3)),
            targets.clone(),
            repetitions,
        ),
        "two_bit_lookup" => measure(
            spec,
            &LookupTwoBitDecompCircuit::<Fr>::default(),
            &input(Some(3)),
            targets.clone(),
            repetitions,
        ),
        //Missing range constraints are a bug control, not a privacy-preserving design.
        "two_bit_missing_range" => measure(
            CaseSpec {
                expected_exact: 0,
                expected_non_unique: 2,
                ..spec
            },
            &TwoBitDecompCircuitUnderConstrained::<Fr>::default(),
            &input(Some(3)),
            targets,
            repetitions,
        ),
        _ => anyhow::bail!("Unknown repository measurement case"),
    }
}

fn repository_cases(repetitions: usize) -> Result<Vec<CaseMeasurements>> {
    ["two_bit_gates", "two_bit_lookup", "two_bit_missing_range"]
        .into_iter()
        .map(|id| repository_case(id, repetitions))
        .collect()
}

fn packed_case<const N: usize>(repetitions: usize) -> Result<CaseMeasurements> {
    let amount = 0xa5a5a5a5_u64 & ((1_u64 << N) - 1);
    let id = match N {
        4 => "packed_bits_4",
        8 => "packed_bits_8",
        16 => "packed_bits_16",
        32 => "packed_bits_32",
        _ => unreachable!(),
    };
    measure(
        CaseSpec {
            id,
            origin: "synthetic_demo",
            target_role: "private_input",
            k: 5,
            expected_exact: N,
            expected_non_unique: 0,
        },
        &PrivateAmountBitsCircuit::<N>::new(amount),
        &input(Some(amount as i64)),
        (0..N).map(|column| CellId::advice(column, 0)).collect(),
        repetitions,
    )
}

fn masked_case(repetitions: usize) -> Result<CaseMeasurements> {
    //An algebraic ambiguity control; this sum is not a cryptographic commitment.
    measure(
        CaseSpec {
            id: "masked_sum",
            origin: "synthetic_demo",
            target_role: "private_input",
            k: 4,
            expected_exact: 0,
            expected_non_unique: 2,
        },
        &SecretCommitmentCircuit::new(42, 58),
        &input(Some(100)),
        vec![CellId::advice(0, 0), CellId::advice(1, 0)],
        repetitions,
    )
}

fn linear_masking_case(mode: LinearMaskingMode, repetitions: usize) -> Result<CaseMeasurements> {
    let targets = linear_masking_targets(mode);
    let input = linear_masking_input(mode);
    let id = match mode {
        LinearMaskingMode::FirstOnly => "mask_single_publication",
        LinearMaskingMode::SecondOnly => "mask_second_publication",
        LinearMaskingMode::ReusedMask => "mask_reused_composition",
        LinearMaskingMode::IndependentMasks => "mask_independent_publications",
    };
    let leaked = mode == LinearMaskingMode::ReusedMask;
    let spec = CaseSpec {
        id,
        origin: "synthetic_demo",
        target_role: "private_input",
        k: 4,
        expected_exact: if leaked { targets.len() } else { 0 },
        expected_non_unique: if leaked { 0 } else { targets.len() },
    };
    //Reuse the exact demo gates and observations, not a separate benchmark circuit.
    match mode {
        LinearMaskingMode::FirstOnly => measure(
            spec,
            &LinearMaskingCircuit::<{ LinearMaskingMode::FirstOnly as u8 }>::new(42, 58, 0),
            &input,
            targets,
            repetitions,
        ),
        LinearMaskingMode::SecondOnly => measure(
            spec,
            &LinearMaskingCircuit::<{ LinearMaskingMode::SecondOnly as u8 }>::new(42, 58, 0),
            &input,
            targets,
            repetitions,
        ),
        LinearMaskingMode::ReusedMask => measure(
            spec,
            &LinearMaskingCircuit::<{ LinearMaskingMode::ReusedMask as u8 }>::new(42, 58, 0),
            &input,
            targets,
            repetitions,
        ),
        LinearMaskingMode::IndependentMasks => measure(
            spec,
            &LinearMaskingCircuit::<{ LinearMaskingMode::IndependentMasks as u8 }>::new(41, 59, 60),
            &input,
            targets,
            repetitions,
        ),
    }
}

fn halo2_book_case(publish_intermediates: bool, repetitions: usize) -> Result<CaseMeasurements> {
    if publish_intermediates {
        let circuit = halo2_book::published_intermediates(2, 3);
        let targets = vec![private_inputs(&circuit)[1].clone()];
        measure(
            CaseSpec {
                id: "halo2_book_publication_control",
                origin: "external_derived_control",
                target_role: "private_input",
                k: 4,
                expected_exact: 1,
                expected_non_unique: 0,
            },
            &circuit,
            &observations(&[252, 2, 6]),
            targets,
            repetitions,
        )
    } else {
        let circuit = halo2_book::original(2, 3);
        let targets = private_inputs(&circuit);
        measure(
            CaseSpec {
                id: "halo2_book_original",
                origin: "external_upstream",
                target_role: "private_input",
                k: 4,
                expected_exact: 0,
                expected_non_unique: 2,
            },
            &circuit,
            &observations(&[252]),
            targets,
            repetitions,
        )
    }
}

fn poseidon_publication_case(repetitions: usize) -> Result<CaseMeasurements> {
    let message = [Fr::from(2), Fr::from(3)];
    let circuit = poseidon_upstream::publication_control(message);
    measure(
        CaseSpec {
            id: "poseidon_publication_control",
            origin: "external_derived_control",
            target_role: "private_message_word",
            k: POSEIDON_K,
            expected_exact: 2,
            expected_non_unique: 0,
        },
        &circuit,
        &poseidon_observations(message, true),
        private_message_cells(&circuit),
        repetitions,
    )
}

fn range_gadget_case<const LOOKUP: bool>(
    boundary: bool,
    repetitions: usize,
) -> Result<CaseMeasurements> {
    let id = match (LOOKUP, boundary) {
        (false, false) => "gadget_polynomial_interior",
        (false, true) => "gadget_polynomial_boundary",
        (true, false) => "gadget_lookup_interior",
        (true, true) => "gadget_lookup_boundary",
    };
    let circuit = if boundary {
        RangeAggregateCircuit::<LOOKUP>::new(15, 15)
    } else {
        RangeAggregateCircuit::<LOOKUP>::new(3, 12)
    };
    let targets = range_private_inputs(&circuit);
    measure(
        CaseSpec {
            id,
            origin: "external_gadget_harness",
            target_role: "private_input",
            k: RANGE_K,
            expected_exact: if boundary { 2 } else { 0 },
            expected_non_unique: if boundary { 0 } else { 2 },
        },
        &circuit,
        &observations(&[if boundary { 30 } else { 15 }]),
        targets,
        repetitions,
    )
}

fn hybrid_case(repetitions: usize) -> Result<CaseMeasurements> {
    //Derived witness cells exercise SMT -> Delta -> UCP; they are not secret inputs.
    measure(
        CaseSpec {
            id: "hybrid_chain_12",
            origin: "synthetic_demo",
            target_role: "derived_witness",
            k: 5,
            expected_exact: 12,
            expected_non_unique: 0,
        },
        &SmtAnchorChainCircuit::<12>::default(),
        &input(None),
        (1..=12).map(|column| CellId::advice(column, 0)).collect(),
        repetitions,
    )
}

pub(super) fn median_ms(values: impl IntoIterator<Item = Duration>) -> f64 {
    let mut values: Vec<_> = values.into_iter().collect();
    values.sort_unstable();
    let middle = values.len() / 2;
    if values.len() % 2 == 0 {
        (values[middle - 1].as_secs_f64() + values[middle].as_secs_f64()) * 500.0
    } else {
        values[middle].as_secs_f64() * 1000.0
    }
}

fn write_samples(writer: &mut impl Write, cases: &[CaseMeasurements]) -> Result<()> {
    writeln!(writer, "case\torigin\ttarget_role\tk\tpublic_observations\ttrial\tfirst_method\tselected_cells\texpressions\twitness_cells\texact\tfinite_domains\tunique\tnon_unique\tucp_queries\ttarget_queries\tbridge_queries\tretry_queries\tprogress_rounds\tsmt_queries\tucp_ms\tsmt_ms\tvalidation_domains\tvalidation_solver_checks\tvalidation_subset_checks\tvalidation_ms\tvalidation_status")?;
    for case in cases {
        for (index, trial) in case.trials.iter().enumerate() {
            writeln!(writer, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.6}\t{:.6}\t{}\t{}\t{}\t{:.6}\t{:?}",
                case.spec.id, case.spec.origin, case.spec.target_role, case.spec.k, case.public_observations,
                index + 1, if trial.ucp_first { "ucp" } else { "smt" }, case.selected_cells,
                trial.expressions, trial.witness_cells, trial.exact, trial.finite_domains, trial.unique,
                trial.non_unique, trial.ucp_queries, trial.target_queries, trial.bridge_queries,
                trial.retry_queries, trial.progress_rounds, trial.smt_queries,
                trial.ucp_elapsed.as_secs_f64() * 1000.0, trial.smt_elapsed.as_secs_f64() * 1000.0,
                trial.validation_domains, trial.validation_solver_checks, trial.validation_subset_checks,
                trial.validation_elapsed.as_secs_f64() * 1000.0, trial.validation_status)?;
        }
    }
    Ok(())
}

fn write_summary(writer: &mut impl Write, cases: &[CaseMeasurements]) -> Result<()> {
    writeln!(writer, "case\torigin\ttarget_role\trepetitions\tselected_cells\texact\tfinite_domains\tucp_median_ms\tsmt_median_ms\tvalidation_median_ms\tucp_speedup\tvalidated_ucp_median_ms")?;
    for case in cases {
        let ucp = median_ms(case.trials.iter().map(|trial| trial.ucp_elapsed));
        let smt = median_ms(case.trials.iter().map(|trial| trial.smt_elapsed));
        let validation = median_ms(case.trials.iter().map(|trial| trial.validation_elapsed));
        let validated = median_ms(
            case.trials
                .iter()
                .map(|trial| trial.ucp_elapsed + trial.validation_elapsed),
        );
        let counts = &case.trials[0];
        writeln!(
            writer,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.6}\t{:.6}\t{:.6}\t{:.6}\t{:.6}",
            case.spec.id,
            case.spec.origin,
            case.spec.target_role,
            case.trials.len(),
            case.selected_cells,
            counts.exact,
            counts.finite_domains,
            ucp,
            smt,
            validation,
            smt / ucp.max(f64::MIN_POSITIVE),
            validated
        )?;
    }
    Ok(())
}

pub(super) fn command_line(program: &str, args: &[&str]) -> String {
    Command::new(program)
        .args(args)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| {
            String::from_utf8_lossy(&output.stdout)
                .lines()
                .next()
                .unwrap_or("")
                .replace(['\t', '\r'], " ")
        })
        .unwrap_or_else(|| "unavailable".into())
}

fn metadata() -> String {
    let dirty = Command::new("git")
        .args(["status", "--porcelain"])
        .output()
        .ok()
        .map(|output| !output.stdout.is_empty());
    format!("# schema: private-recovery-measurements-v3\n# unix_time: {}\n# profile: {}\n# platform: {}-{}\n# rust: {}\n# cvc5: {}\n# git_revision: {}\n# working_tree_dirty: {:?}\n# field_modulus: {}\n# solver_query_budget_ms: {}\n# solver_process_policy: supervised-wallclock-per-invocation\n# stored_value_bits_limit: {}\n# finite_domain_size_limit: {}\n# privacy_smt_domain_policy: {}\n# privacy_satisfiability_policy: {PRIVACY_SAT_HINT_POLICY}\n# validation_policy: {PRIVACY_VALIDATION_POLICY}\n# privacy_search_policy: {PRIVACY_SEARCH_POLICY}\n# recovery_total_query_limit: {}\n# recovery_search_options: {:?}\n# finite_domain_refinement_policy: {PRIVACY_DOMAIN_REFINEMENT_POLICY}\n# finite_domain_refinement_options: {:?}\n# finite_domain_discovery_policy: {PRIVACY_DOMAIN_DISCOVERY_POLICY}\n# finite_domain_discovery_options: {:?}\n# targeted_subset_policy: {PRIVACY_TARGETED_SUBSET_POLICY}\n# warmups_per_case: 1\n# serial: true\n",
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_secs(),
        if cfg!(debug_assertions) { "debug" } else { "release" }, std::env::consts::OS,
        std::env::consts::ARCH, command_line("rustc", &["--version"]), command_line("cvc5", &["--version"]),
        command_line("git", &["rev-parse", "HEAD"]), dirty, super::extractor::field_modulus::<Fr>(),
        std::env::var("HALO2_ANALYZER_SMT_TIMEOUT_MS").unwrap_or_else(|_| "unlimited".into()),
        super::value::MAX_VALUE_BITS, super::value::MAX_FINITE_DOMAIN_SIZE,
        PRIVACY_SMT_DOMAIN_POLICY, measurement_options().max_semantic_queries,
        measurement_options().search, measurement_options().domain_refinement, measurement_options().domain_discovery)
}

fn measurement_options() -> PrivacyAnalysisOptions {
    PrivacyAnalysisOptions {
        search: PrivacySearchOptions {
            // Keep the same per-process budget as the SMT-only reference.
            retry_solver_timeout_ms: None,
            ..Default::default()
        },
        ..Default::default()
    }
}

#[test]
fn measurement_metadata_identifies_representation_and_process_policy() {
    let metadata = metadata();
    assert!(metadata.contains("# schema: private-recovery-measurements-v3\n"));
    assert!(metadata.contains(&format!(
        "# privacy_search_policy: {PRIVACY_SEARCH_POLICY}\n"
    )));
    assert!(metadata.contains("# recovery_total_query_limit: 256\n"));
    assert!(metadata.contains("# finite_domain_refinement_options: PrivacyDomainRefinementOptions { max_solver_checks: 0, max_candidates_per_cell: 16 }\n"));
    assert!(metadata.contains("# finite_domain_discovery_options: PrivacyDomainDiscoveryOptions { max_solver_checks: 0, max_values_per_cell: 16, max_checks_per_round: 1, max_retries_per_cell: 1, retry_solver_timeout_ms: None, use_targeted_subsets: false }\n"));
    assert!(metadata.contains(&format!(
        "# targeted_subset_policy: {PRIVACY_TARGETED_SUBSET_POLICY}\n"
    )));
    assert!(metadata.contains(&format!(
        "# validation_policy: {PRIVACY_VALIDATION_POLICY}\n"
    )));
    assert!(metadata.contains(&format!(
        "# privacy_satisfiability_policy: {PRIVACY_SAT_HINT_POLICY}\n"
    )));
    assert!(metadata.contains("# solver_process_policy: supervised-wallclock-per-invocation\n"));
    assert!(metadata.contains(&format!(
        "# stored_value_bits_limit: {}\n",
        super::value::MAX_VALUE_BITS
    )));
    assert!(metadata.contains(&format!(
        "# finite_domain_size_limit: {}\n",
        super::value::MAX_FINITE_DOMAIN_SIZE
    )));
}

fn write_incomplete(writer: &mut impl Write, incomplete: &[IncompleteCase]) -> Result<()> {
    writeln!(writer, "case\tstatus\tattempt_elapsed_ms\treason")?;
    for case in incomplete {
        writeln!(
            writer,
            "{}\tsolver_unknown\t{:.6}\t{}",
            case.id,
            case.elapsed.as_secs_f64() * 1000.0,
            case.reason
        )?;
    }
    Ok(())
}

#[test]
fn privacy_measurement_smoke_matches_smt_on_repository_cases() {
    let cases = repository_cases(1).unwrap();
    assert_eq!(cases.len(), 3);
    assert_eq!(cases[0].trials[0].ucp_queries, 0);
    assert_eq!(cases[1].trials[0].ucp_queries, 0);
    let mut samples = Vec::new();
    write_samples(&mut samples, &cases).unwrap();
    let samples = String::from_utf8(samples).unwrap();
    let columns = samples.lines().next().unwrap().split('\t').count();
    assert!(samples
        .lines()
        .skip(1)
        .all(|line| line.split('\t').count() == columns));
}

#[test]
fn privacy_measurement_smoke_covers_masking_and_hybrid_feedback() {
    let masked = masked_case(1).unwrap();
    assert_eq!(
        masked.trials[0].validation_status,
        RecoveryValidationStatus::NoDomainClaims
    );
    let hybrid = hybrid_case(1).unwrap();
    assert_eq!(hybrid.trials[0].ucp_queries, 1);
    assert_eq!(hybrid.trials[0].smt_queries, 12);
    let bits = packed_case::<8>(1).unwrap();
    assert_eq!(bits.trials[0].exact, 8);
    assert_eq!(bits.trials[0].ucp_queries, 0);
}

#[test]
fn privacy_measurement_smoke_covers_compositional_masking() {
    for mode in [
        LinearMaskingMode::FirstOnly,
        LinearMaskingMode::ReusedMask,
        LinearMaskingMode::IndependentMasks,
    ] {
        let case = linear_masking_case(mode, 1).unwrap();
        let trial = &case.trials[0];
        if mode == LinearMaskingMode::ReusedMask {
            assert_eq!(trial.ucp_queries, 0);
            assert_eq!(trial.exact, 2);
            assert_eq!(
                trial.validation_status,
                RecoveryValidationStatus::VerifiedDomains
            );
        } else {
            assert_eq!(trial.exact, 0);
            assert_eq!(trial.non_unique, case.selected_cells);
            assert_eq!(
                trial.validation_status,
                RecoveryValidationStatus::NoDomainClaims
            );
        }
    }
}

#[test]
fn privacy_measurement_smoke_matches_smt_on_external_halo2_book() {
    let original = halo2_book_case(false, 1).unwrap();
    assert_eq!(original.spec.origin, "external_upstream");
    assert_eq!(original.trials[0].non_unique, 2);
    assert_eq!(original.trials[0].exact, 0);
    let control = halo2_book_case(true, 1).unwrap();
    assert_eq!(control.spec.origin, "external_derived_control");
    assert_eq!(control.selected_cells, 1);
    assert_eq!(control.trials[0].exact, 1);
    assert_eq!(control.trials[0].validation_domains, 1);
    assert_eq!(
        control.trials[0].validation_status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

#[test]
fn privacy_measurement_smoke_matches_smt_on_imported_range_gadgets() {
    for boundary in [false, true] {
        for case in [
            range_gadget_case::<false>(boundary, 1).unwrap(),
            range_gadget_case::<true>(boundary, 1).unwrap(),
        ] {
            assert_eq!(case.spec.origin, "external_gadget_harness");
            assert_eq!(case.selected_cells, 2);
            let trial = &case.trials[0];
            if boundary {
                assert_eq!(trial.exact, 2);
                assert_eq!(
                    trial.validation_status,
                    RecoveryValidationStatus::VerifiedDomains
                );
            } else {
                assert_eq!(trial.non_unique, 2);
                assert_eq!(trial.exact, 0);
            }
        }
    }
}

#[test]
fn privacy_measurement_smoke_reports_explicit_api_budget() {
    let amount = 0xAD;
    let options = PrivacyAnalysisOptions {
        max_semantic_queries: 32,
        solver_timeout_ms: Some(2_000),
        ..Default::default()
    };
    let report = analyze_private_recoverability::<Fr, _, _>(
        &PrivateAmountBitsCircuit::<8>::new(amount),
        4,
        &input(Some(amount as i64)),
        (0..8).map(|column| CellId::advice(column, 0)),
        options,
    )
    .unwrap();
    println!("Explicit 2000 ms/check recovery policy:\n{report}");
    assert_eq!(report.options, options);
    assert_eq!(report.summary.non_unique_cells, 0);
    //Do not require a machine-specific timeout: a genuinely completed proof is also valid.
    match report.status {
        PrivacyAnalysisStatus::Analyzed => assert_eq!(report.summary.exact_values, 8),
        PrivacyAnalysisStatus::SolverUnknown => {
            assert!(report
                .cells
                .iter()
                .any(|cell| cell.recovery_limitation.is_some()));
            if report.ucp_result.is_none() {
                assert_eq!(report.summary.exact_values, 0);
                assert!(report.cells.iter().all(|cell| cell.domain.is_none()));
            }
        }
        other => panic!("Unexpected large-case outcome: {other:?}"),
    }
}

#[test]
fn privacy_measurement_statistics_use_medians_not_speed_assertions() {
    assert_eq!(
        median_ms([
            Duration::from_millis(9),
            Duration::from_millis(1),
            Duration::from_millis(3)
        ]),
        3.0
    );
    assert_eq!(
        median_ms([Duration::from_millis(8), Duration::from_millis(2)]),
        5.0
    );
}

#[test]
fn privacy_measurement_unknown_is_excluded_but_correctness_errors_are_fatal() {
    let mut completed = Vec::new();
    let mut incomplete = Vec::new();
    collect_case(
        "unknown",
        || Err(anyhow::Error::new(UnknownSolverResult)),
        &mut completed,
        &mut incomplete,
    )
    .unwrap();
    assert!(completed.is_empty());
    assert_eq!(incomplete.len(), 1);
    assert!(collect_case(
        "mismatch",
        || anyhow::bail!("exact value mismatch"),
        &mut completed,
        &mut incomplete
    )
    .is_err());
    assert_eq!(incomplete.len(), 1);
}

#[test]
#[ignore = "Repeated serial measurements; run explicitly with --ignored --nocapture --test-threads=1"]
fn privacy_measurement_suite() {
    let repetitions = std::env::var("PRIVACY_MEASUREMENTS_REPETITIONS")
        .unwrap_or_else(|_| "5".into())
        .parse::<usize>()
        .expect("Invalid repetition count");
    assert!((1..=100).contains(&repetitions), "Use 1..=100 repetitions");
    let budget = std::env::var("HALO2_ANALYZER_SMT_TIMEOUT_MS")
        .expect("Set HALO2_ANALYZER_SMT_TIMEOUT_MS to bound the explicit measurement suite")
        .parse::<u64>()
        .expect("Invalid solver budget");
    assert!(budget > 0, "Solver budget must be positive");
    let mut cases = Vec::new();
    let mut incomplete = Vec::new();
    for id in ["two_bit_gates", "two_bit_lookup", "two_bit_missing_range"] {
        collect_case(
            id,
            || repository_case(id, repetitions),
            &mut cases,
            &mut incomplete,
        )
        .unwrap();
    }
    for (id, publish_intermediates) in [
        ("halo2_book_original", false),
        ("halo2_book_publication_control", true),
    ] {
        collect_case(
            id,
            || halo2_book_case(publish_intermediates, repetitions),
            &mut cases,
            &mut incomplete,
        )
        .unwrap();
    }
    for boundary in [false, true] {
        let polynomial_id = if boundary {
            "gadget_polynomial_boundary"
        } else {
            "gadget_polynomial_interior"
        };
        let lookup_id = if boundary {
            "gadget_lookup_boundary"
        } else {
            "gadget_lookup_interior"
        };
        collect_case(
            polynomial_id,
            || range_gadget_case::<false>(boundary, repetitions),
            &mut cases,
            &mut incomplete,
        )
        .unwrap();
        collect_case(
            lookup_id,
            || range_gadget_case::<true>(boundary, repetitions),
            &mut cases,
            &mut incomplete,
        )
        .unwrap();
    }
    // Full cryptographic checks can time out even for an algebraically leaking context.
    collect_case(
        "poseidon_publication_control",
        || poseidon_publication_case(repetitions),
        &mut cases,
        &mut incomplete,
    )
    .unwrap();
    collect_case(
        "masked_sum",
        || masked_case(repetitions),
        &mut cases,
        &mut incomplete,
    )
    .unwrap();
    for (id, mode) in [
        ("mask_single_publication", LinearMaskingMode::FirstOnly),
        ("mask_reused_composition", LinearMaskingMode::ReusedMask),
        (
            "mask_independent_publications",
            LinearMaskingMode::IndependentMasks,
        ),
    ] {
        collect_case(
            id,
            || linear_masking_case(mode, repetitions),
            &mut cases,
            &mut incomplete,
        )
        .unwrap();
    }
    collect_case(
        "packed_bits_4",
        || packed_case::<4>(repetitions),
        &mut cases,
        &mut incomplete,
    )
    .unwrap();
    collect_case(
        "packed_bits_8",
        || packed_case::<8>(repetitions),
        &mut cases,
        &mut incomplete,
    )
    .unwrap();
    collect_case(
        "packed_bits_16",
        || packed_case::<16>(repetitions),
        &mut cases,
        &mut incomplete,
    )
    .unwrap();
    collect_case(
        "packed_bits_32",
        || packed_case::<32>(repetitions),
        &mut cases,
        &mut incomplete,
    )
    .unwrap();
    collect_case(
        "hybrid_chain_12",
        || hybrid_case(repetitions),
        &mut cases,
        &mut incomplete,
    )
    .unwrap();
    let metadata = format!(
        "{}# requested_repetitions: {}\n# completed_cases: {}\n# incomplete_cases: {}\n",
        metadata(),
        repetitions,
        cases.len(),
        incomplete.len()
    );
    let mut summary = Vec::new();
    write_summary(&mut summary, &cases).unwrap();
    println!("{}{}", metadata, String::from_utf8(summary).unwrap());
    let mut skipped = Vec::new();
    write_incomplete(&mut skipped, &incomplete).unwrap();
    println!(
        "Incomplete cases (excluded from speedup summaries):\n{}",
        String::from_utf8(skipped).unwrap()
    );
    if let Some(path) = std::env::var_os("PRIVACY_MEASUREMENTS_OUTPUT") {
        let path = PathBuf::from(path);
        let mut samples = BufWriter::new(File::create(&path).expect("Cannot create sample output"));
        samples.write_all(metadata.as_bytes()).unwrap();
        write_samples(&mut samples, &cases).unwrap();
        samples.flush().unwrap();
        let summary_path = path.with_extension("summary.tsv");
        let mut summary =
            BufWriter::new(File::create(&summary_path).expect("Cannot create summary output"));
        summary.write_all(metadata.as_bytes()).unwrap();
        write_summary(&mut summary, &cases).unwrap();
        summary.flush().unwrap();
        let incomplete_path = path.with_extension("incomplete.tsv");
        let mut skipped = BufWriter::new(
            File::create(&incomplete_path).expect("Cannot create incomplete-case output"),
        );
        skipped.write_all(metadata.as_bytes()).unwrap();
        write_incomplete(&mut skipped, &incomplete).unwrap();
        skipped.flush().unwrap();
        println!(
            "Measurements: {}\nSummary: {}\nIncomplete cases: {}",
            path.display(),
            summary_path.display(),
            incomplete_path.display()
        );
    }
}
