//! Serial ablations of optional recovery paths, with separate original-SMT observation control.
//! Keep incomplete attempts and cell evidence; timing ratios are never correctness assertions.

use super::{
    cell::CellId,
    demo_tests::{
        linear_masking_input, LinearMaskingCircuit, LinearMaskingMode, SecretCommitmentCircuit,
    },
    external_circuit_tests::observations,
    external_range_tests::{range_private_inputs, RangeAggregateCircuit, RANGE_K},
    privacy::{
        analyze_private_recoverability, PrivacyAnalysisOptions, PrivacyAnalysisReport,
        PrivacyAnalysisStatus, PrivacySearchOptions, PrivateCellUniqueness,
        PRIVACY_SAT_HINT_POLICY, PRIVACY_SEARCH_POLICY, PRIVACY_SMT_DOMAIN_POLICY,
    },
    privacy_discovery::{
        PrivacyDomainDiscoveryOptions, PrivateDomainDiscoveryStatus,
        PRIVACY_DOMAIN_DISCOVERY_POLICY,
    },
    privacy_discovery_tests::{
        discovery_demo_input, discovery_demo_targets, LocalizedRecoveryCircuit,
        UnboundedProjectionCircuit, TWO_ROOTS, UNIQUE,
    },
    privacy_domain::{
        PrivacyDomainRefinementOptions, PrivateDomainRefinementStatus,
        PRIVACY_DOMAIN_REFINEMENT_POLICY,
    },
    privacy_domain_tests::FiniteProjectionCircuit,
    privacy_measurement_tests::{command_line, median_ms},
    privacy_observation::{
        analyze_public_observation_effect, PrivateDomainObservationEffect,
        PublicObservationEffectOptions, PublicObservationEffectReport,
        PublicObservationEffectStatus, PRIVACY_OBSERVATION_POLICY,
    },
    privacy_subset::PRIVACY_TARGETED_SUBSET_POLICY,
    privacy_validation::{
        validate_private_recovery_report, PrivateRecoveryValidationReport,
        RecoveryValidationStatus, PRIVACY_VALIDATION_POLICY,
    },
    value::{normalize_field_value, UcpValueDomain, MAX_FINITE_DOMAIN_SIZE, MAX_VALUE_BITS},
};
use crate::{
    circuit_analyzer::halo2_proofs_libs::*, io::analyzer_io_type::AnalyzerInput,
    smt_solver::smt_parser::UnknownSolverResult,
};
use anyhow::{ensure, Context, Result};
use num_bigint::BigInt;
use std::{
    collections::BTreeSet,
    fs::File,
    io::{BufWriter, Write},
    path::Path,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Profile {
    Baseline,
    Refinement,
    Discovery,
    TargetedDiscovery,
}

const PROFILES: [Profile; 4] = [
    Profile::Baseline,
    Profile::Refinement,
    Profile::Discovery,
    Profile::TargetedDiscovery,
];

impl Profile {
    fn options(self, timeout_ms: u64) -> PrivacyAnalysisOptions {
        PrivacyAnalysisOptions {
            max_semantic_queries: 32,
            solver_timeout_ms: Some(timeout_ms),
            initial_sat_timeout_ms: None,
            search: PrivacySearchOptions {
                // No profile silently buys a longer solver timeout on retry.
                retry_solver_timeout_ms: None,
                ..Default::default()
            },
            domain_refinement: PrivacyDomainRefinementOptions {
                max_solver_checks: if self == Self::Refinement { 64 } else { 0 },
                max_candidates_per_cell: 16,
            },
            domain_discovery: PrivacyDomainDiscoveryOptions {
                max_solver_checks: if matches!(self, Self::Discovery | Self::TargetedDiscovery) {
                    32
                } else {
                    0
                },
                max_values_per_cell: 16,
                use_targeted_subsets: self == Self::TargetedDiscovery,
                ..Default::default()
            },
        }
    }
}

#[derive(Clone)]
struct ExpectedProjection {
    role: &'static str,
    // None denotes the whole field in the free-sum control, not an unknown oracle.
    values: Option<BTreeSet<BigInt>>,
    complete_effect: PrivateDomainObservationEffect,
}

impl ExpectedProjection {
    fn finite(values: &[i64], effect: PrivateDomainObservationEffect) -> Self {
        Self {
            role: "private_input",
            values: Some(values.iter().copied().map(BigInt::from).collect()),
            complete_effect: effect,
        }
    }
}

struct CaseSpec {
    id: &'static str,
    origin: &'static str,
    k: u32,
    expected: Vec<ExpectedProjection>,
}

struct Trial {
    profile: Profile,
    repetition: usize, // Zero is a recorded warm-up, excluded from medians.
    order: usize,
    recovery: PrivacyAnalysisReport,
    validation: Option<PrivateRecoveryValidationReport>,
    validation_unknown: Option<String>,
    validation_elapsed: Duration,
    control: PublicObservationEffectReport,
    expected_projections_recovered: usize,
}

impl Trial {
    fn optional_search_incomplete(&self) -> bool {
        self.recovery.domain_discovery_statistics.budget_exhausted
            || self.recovery.domain_refinement_statistics.budget_exhausted
            || self.recovery.cells.iter().any(|cell| {
                cell.domain_discovery.as_ref().is_some_and(|evidence| {
                    evidence.status != PrivateDomainDiscoveryStatus::Complete
                }) || cell.domain_refinement.as_ref().is_some_and(|evidence| {
                    evidence.status != PrivateDomainRefinementStatus::Complete
                })
            })
    }

    fn recovery_complete(&self) -> bool {
        self.recovery.status == PrivacyAnalysisStatus::Analyzed
    }

    fn validation_complete(&self) -> bool {
        self.validation.as_ref().is_some_and(|report| {
            matches!(
                report.status,
                RecoveryValidationStatus::VerifiedDomains
                    | RecoveryValidationStatus::NoDomainClaims
            )
        })
    }

    fn control_complete(&self) -> bool {
        matches!(
            self.control.status,
            PublicObservationEffectStatus::Analyzed | PublicObservationEffectStatus::NoDomainClaims
        )
    }

    fn workflow_complete(&self) -> bool {
        self.recovery_complete() && self.validation_complete() && self.control_complete()
    }

    fn workflow_elapsed(&self) -> Duration {
        self.recovery.elapsed + self.validation_elapsed + self.control.elapsed
    }
}

struct Measurements {
    spec: CaseSpec,
    trials: Vec<Trial>,
}

fn domain_values(domain: &UcpValueDomain) -> Result<BTreeSet<BigInt>> {
    let modulus = super::extractor::field_modulus::<Fr>();
    let values: Vec<_> = match domain {
        UcpValueDomain::Exact(value) => vec![value.clone()],
        UcpValueDomain::FiniteSet(values) => values.iter().cloned().collect(),
    };
    values
        .into_iter()
        .map(|value| {
            normalize_field_value(value, &modulus).context("Unsupported measurement-domain value")
        })
        .collect()
}

// Analytical fixture projections catch false claims independently of the solver being benchmarked.
// Missing/broad claims and unknowns remain measurable outcomes, not silently discarded cases.
fn check_recovery(report: &PrivacyAnalysisReport, spec: &CaseSpec) -> Result<usize> {
    ensure!(
        report.status != PrivacyAnalysisStatus::Inconsistent,
        "{}: valid fixture became inconsistent",
        spec.id
    );
    ensure!(
        report.cells.len() == spec.expected.len(),
        "Wrong target count"
    );
    let mut recovered = 0;
    for (cell, expected) in report.cells.iter().zip(&spec.expected) {
        let expected_unique = expected
            .values
            .as_ref()
            .is_some_and(|values| values.len() == 1);
        match cell.uniqueness {
            PrivateCellUniqueness::Unique => {
                ensure!(expected_unique, "False uniqueness at {}", cell.cell)
            }
            PrivateCellUniqueness::NonUnique => {
                ensure!(!expected_unique, "False ambiguity at {}", cell.cell)
            }
            PrivateCellUniqueness::Unknown => {}
        }
        if let Some(domain) = &cell.domain {
            let actual = domain_values(domain)?;
            let truth = expected
                .values
                .as_ref()
                .context("A finite claim cannot cover the full-field control")?;
            ensure!(
                truth.is_subset(&actual),
                "{}: domain excludes feasible fixture values at {}",
                spec.id,
                cell.cell
            );
            recovered += usize::from(&actual == truth);
        }
    }
    Ok(recovered)
}

fn check_control(
    report: &PrivacyAnalysisReport,
    control: &PublicObservationEffectReport,
    spec: &CaseSpec,
) -> Result<()> {
    ensure!(
        !matches!(
            control.status,
            PublicObservationEffectStatus::Refuted | PublicObservationEffectStatus::Inconsistent
        ),
        "{}: original-SMT control rejected recovery",
        spec.id
    );
    ensure!(
        control.cells.len() == report.cells.len(),
        "Wrong control target count"
    );
    ensure!(
        control.solver_checks
            == control.satisfiability_checks
                + control.observed_domain_checks
                + control.unobserved_domain_checks,
        "Control checks do not partition"
    );
    for ((cell, evidence), expected) in report.cells.iter().zip(&control.cells).zip(&spec.expected)
    {
        ensure!(
            cell.cell == evidence.cell && cell.domain == evidence.domain,
            "Control claim changed"
        );
        if matches!(
            evidence.effect,
            PrivateDomainObservationEffect::ObservationDependent
                | PrivateDomainObservationEffect::AlreadyImplied
        ) {
            ensure!(
                evidence.observed_domain_verified,
                "Unverified observation classification"
            );
            if let (Some(domain), Some(truth)) = (&cell.domain, &expected.values) {
                if domain_values(domain)? == *truth {
                    ensure!(
                        evidence.effect == expected.complete_effect,
                        "{}: wrong observation effect at {}",
                        spec.id,
                        cell.cell
                    );
                }
            }
        }
    }
    Ok(())
}

fn run_trial<C: Circuit<Fr>>(
    spec: &CaseSpec,
    circuit: &C,
    input: &AnalyzerInput,
    targets: &[CellId],
    profile: Profile,
    options: PrivacyAnalysisOptions,
    repetition: usize,
    order: usize,
) -> Result<Trial> {
    let recovery = analyze_private_recoverability::<Fr, _, _>(
        circuit,
        spec.k,
        input,
        targets.iter().cloned(),
        options,
    )?;
    let expected_projections_recovered = check_recovery(&recovery, spec)?;
    ensure!(
        recovery
            .cells
            .iter()
            .map(|cell| &cell.cell)
            .eq(targets.iter()),
        "Measured target order changed"
    );
    let validation_started = Instant::now();
    let (validation, validation_unknown) =
        match validate_private_recovery_report::<Fr, _>(circuit, spec.k, input, &recovery) {
            Ok(report) => {
                ensure!(
                    matches!(
                        report.status,
                        RecoveryValidationStatus::VerifiedDomains
                            | RecoveryValidationStatus::NoDomainClaims
                    ),
                    "Independent validation rejected recovery"
                );
                (Some(report), None)
            }
            Err(error) if error.downcast_ref::<UnknownSolverResult>().is_some() => {
                (None, Some(format!("{error:#}")))
            }
            Err(error) => return Err(error),
        };
    let validation_elapsed = validation
        .as_ref()
        .map_or_else(|| validation_started.elapsed(), |report| report.elapsed);
    let control = analyze_public_observation_effect::<Fr, _>(
        circuit,
        spec.k,
        input,
        &recovery,
        PublicObservationEffectOptions {
            max_solver_checks: 64,
            solver_timeout_ms: options.solver_timeout_ms,
        },
    )?;
    check_control(&recovery, &control, spec)?;
    ensure!(
        recovery.semantic_queries <= options.max_semantic_queries,
        "Semantic budget exceeded"
    );
    ensure!(
        recovery.semantic_queries
            == recovery.search_statistics.target_queries
                + recovery.search_statistics.bridge_queries,
        "Semantic query counters do not partition"
    );
    ensure!(
        recovery.domain_refinement_statistics.solver_checks
            <= options.domain_refinement.max_solver_checks,
        "Refinement budget exceeded"
    );
    let discovery = &recovery.domain_discovery_statistics;
    ensure!(
        discovery.solver_checks <= options.domain_discovery.max_solver_checks
            && discovery.solver_checks
                == discovery.full_solver_checks + discovery.subset_solver_checks,
        "Discovery checks/budget mismatch"
    );
    Ok(Trial {
        profile,
        repetition,
        order,
        recovery,
        validation,
        validation_unknown,
        validation_elapsed,
        control,
        expected_projections_recovered,
    })
}

fn measure<C: Circuit<Fr>>(
    spec: CaseSpec,
    circuit: &C,
    input: &AnalyzerInput,
    targets: Vec<CellId>,
    repetitions: usize,
    timeout_ms: u64,
) -> Result<Measurements> {
    ensure!(
        (1..=100).contains(&repetitions) && timeout_ms > 0,
        "Use 1..=100 repetitions and a positive timeout"
    );
    ensure!(
        targets.len() == spec.expected.len(),
        "Wrong fixture targets"
    );
    let mut trials = Vec::new();
    // Rotate each profile's position; even warm-up evidence is retained.
    for repetition in 0..=repetitions {
        for order in 0..PROFILES.len() {
            let profile = PROFILES[(order + repetition) % PROFILES.len()];
            trials.push(run_trial(
                &spec,
                circuit,
                input,
                &targets,
                profile,
                profile.options(timeout_ms),
                repetition,
                order,
            )?);
        }
    }
    Ok(Measurements { spec, trials })
}

fn measure_case(id: &'static str, repetitions: usize, timeout_ms: u64) -> Result<Measurements> {
    use PrivateDomainObservationEffect::{AlreadyImplied, ObservationDependent};
    let pair = |left: &[i64], right: &[i64], effect| {
        let mut derived = ExpectedProjection::finite(right, effect);
        derived.role = "derived_witness";
        vec![ExpectedProjection::finite(left, effect), derived]
    };
    let spec = |origin, expected| CaseSpec {
        id,
        origin,
        k: 4,
        expected,
    };
    let targets = discovery_demo_targets().to_vec();
    let input = discovery_demo_input();
    match id {
        "expanded_two_roots" => measure(
            spec("synthetic_demo", pair(&[3, 7], &[0], ObservationDependent)),
            &UnboundedProjectionCircuit::<TWO_ROOTS>::new(Fr::from(3), Fr::from(0)),
            &input,
            targets,
            repetitions,
            timeout_ms,
        ),
        "lookup_seeded_two_roots" => measure(
            CaseSpec {
                k: 5,
                ..spec("synthetic_demo", pair(&[3, 7], &[0], ObservationDependent))
            },
            &FiniteProjectionCircuit::<false>::new(3),
            &input,
            targets,
            repetitions,
            timeout_ms,
        ),
        "localized_expanded_singleton" => measure(
            spec("synthetic_demo", pair(&[21], &[23], ObservationDependent)),
            &LocalizedRecoveryCircuit::<6> { amount: 21 },
            &input,
            targets,
            repetitions,
            timeout_ms,
        ),
        "intrinsic_singleton" => measure(
            spec("synthetic_demo", pair(&[1], &[3], AlreadyImplied)),
            &UnboundedProjectionCircuit::<UNIQUE>::new(Fr::from(1), Fr::from(3)),
            &input,
            targets,
            repetitions,
            timeout_ms,
        ),
        "mask_reused_composition" => measure(
            spec(
                "synthetic_demo",
                vec![
                    ExpectedProjection::finite(&[42], ObservationDependent),
                    ExpectedProjection::finite(&[58], ObservationDependent),
                ],
            ),
            &LinearMaskingCircuit::<{ LinearMaskingMode::ReusedMask as u8 }>::new(42, 58, 0),
            &linear_masking_input(LinearMaskingMode::ReusedMask),
            targets,
            repetitions,
            timeout_ms,
        ),
        "masked_sum" => measure(
            spec(
                "synthetic_demo",
                vec![
                    ExpectedProjection {
                        role: "private_input",
                        values: None,
                        complete_effect: PrivateDomainObservationEffect::NoDomainClaim
                    };
                    2
                ],
            ),
            &SecretCommitmentCircuit::new(42, 58),
            &observations(&[100]),
            targets,
            repetitions,
            timeout_ms,
        ),
        "imported_lookup_projection" => {
            let circuit = RangeAggregateCircuit::<true>::new(3, 13);
            let values: Vec<_> = (1..=15).collect();
            measure(
                CaseSpec {
                    k: RANGE_K,
                    ..spec(
                        "external_gadget_harness",
                        vec![ExpectedProjection::finite(&values, ObservationDependent); 2],
                    )
                },
                &circuit,
                &observations(&[16]),
                range_private_inputs(&circuit),
                repetitions,
                timeout_ms,
            )
        }
        _ => anyhow::bail!("Unknown recovery-profile fixture"),
    }
}

const CASES: [&str; 7] = [
    "expanded_two_roots",
    "lookup_seeded_two_roots",
    "localized_expanded_singleton",
    "intrinsic_singleton",
    "mask_reused_composition",
    "masked_sum",
    "imported_lookup_projection",
];

// Small text fields are escaped uniformly; TSV column alignment never depends on Debug contents.
fn row(writer: &mut impl Write, fields: impl IntoIterator<Item = String>) -> Result<()> {
    let fields: Vec<_> = fields
        .into_iter()
        .map(|value| value.replace(['\t', '\r', '\n'], " "))
        .collect();
    writeln!(writer, "{}", fields.join("\t"))?;
    Ok(())
}

fn optional(value: Option<usize>) -> String {
    value.map_or_else(|| "NA".into(), |value| value.to_string())
}

fn ms(value: Duration) -> String {
    format!("{:.6}", value.as_secs_f64() * 1000.0)
}

fn median(values: impl IntoIterator<Item = Duration>) -> String {
    let values: Vec<_> = values.into_iter().collect();
    if values.is_empty() {
        "NA".into()
    } else {
        format!("{:.6}", median_ms(values))
    }
}

fn effect_count(trial: &Trial, effect: PrivateDomainObservationEffect) -> usize {
    trial
        .control
        .cells
        .iter()
        .filter(|cell| cell.effect == effect)
        .count()
}

fn write_samples(writer: &mut impl Write, cases: &[Measurements]) -> Result<()> {
    row(
        writer,
        [
            "case",
            "origin",
            "profile",
            "repetition",
            "warmup",
            "order",
            "recovery_options",
            "control_options",
            "public_values",
            "targets",
            "recovery_status",
            "exact",
            "finite",
            "unique",
            "non_unique",
            "unresolved",
            "expected_small_projections_recovered",
            "expected_small_projections",
            "semantic_cell_queries",
            "target_queries",
            "bridge_queries",
            "retry_queries",
            "progress_rounds",
            "sat_checks",
            "refinement_checks",
            "discovery_checks",
            "discovery_full_checks",
            "discovery_subset_checks",
            "subset_fallbacks",
            "subset_unsat_proofs",
            "discovery_complete_domains",
            "discovery_models_found",
            "discovery_partial_cells",
            "discovery_budget_exhausted",
            "refinement_partial_cells",
            "refinement_budget_exhausted",
            "optional_search_incomplete",
            "validation_status",
            "validation_checks",
            "validation_subset_checks",
            "validation_unknown",
            "control_status",
            "control_checks",
            "control_sat_checks",
            "control_observed_checks",
            "control_unobserved_checks",
            "observation_dependent",
            "already_implied",
            "control_unresolved",
            "workflow_checks_completed",
            "recovery_ms",
            "validation_ms",
            "control_ms",
            "workflow_ms",
        ]
        .map(str::to_owned),
    )?;
    for case in cases {
        for trial in &case.trials {
            let report = &trial.recovery;
            let discovery = &report.domain_discovery_statistics;
            row(
                writer,
                vec![
                    case.spec.id.into(),
                    case.spec.origin.into(),
                    format!("{:?}", trial.profile),
                    trial.repetition.to_string(),
                    (trial.repetition == 0).to_string(),
                    trial.order.to_string(),
                    format!("{:?}", report.options),
                    format!("{:?}", trial.control.options),
                    format!("{:?}", report.public_values),
                    report.cells.len().to_string(),
                    format!("{:?}", report.status),
                    report.summary.exact_values.to_string(),
                    report.summary.finite_domains.to_string(),
                    report.summary.unique_cells.to_string(),
                    report.summary.non_unique_cells.to_string(),
                    report.summary.unresolved_uniqueness.to_string(),
                    trial.expected_projections_recovered.to_string(),
                    case.spec
                        .expected
                        .iter()
                        .filter(|projection| projection.values.is_some())
                        .count()
                        .to_string(),
                    report.semantic_queries.to_string(),
                    report.search_statistics.target_queries.to_string(),
                    report.search_statistics.bridge_queries.to_string(),
                    report.search_statistics.retry_queries.to_string(),
                    report.search_statistics.progress_rounds.to_string(),
                    report.satisfiability_checks.to_string(),
                    report
                        .domain_refinement_statistics
                        .solver_checks
                        .to_string(),
                    discovery.solver_checks.to_string(),
                    discovery.full_solver_checks.to_string(),
                    discovery.subset_solver_checks.to_string(),
                    discovery.subset_fallbacks.to_string(),
                    discovery.subset_unsat_proofs.to_string(),
                    discovery.complete_domains.to_string(),
                    discovery.models_found.to_string(),
                    report
                        .cells
                        .iter()
                        .filter(|cell| {
                            cell.domain_discovery.as_ref().is_some_and(|evidence| {
                                evidence.status != PrivateDomainDiscoveryStatus::Complete
                            })
                        })
                        .count()
                        .to_string(),
                    discovery.budget_exhausted.to_string(),
                    report
                        .cells
                        .iter()
                        .filter(|cell| {
                            cell.domain_refinement.as_ref().is_some_and(|evidence| {
                                evidence.status != PrivateDomainRefinementStatus::Complete
                            })
                        })
                        .count()
                        .to_string(),
                    report
                        .domain_refinement_statistics
                        .budget_exhausted
                        .to_string(),
                    trial.optional_search_incomplete().to_string(),
                    trial.validation.as_ref().map_or_else(
                        || "SolverUnknown".into(),
                        |report| format!("{:?}", report.status),
                    ),
                    optional(trial.validation.as_ref().map(|report| report.solver_checks)),
                    optional(trial.validation.as_ref().map(|report| report.subset_checks)),
                    trial.validation_unknown.clone().unwrap_or_default(),
                    format!("{:?}", trial.control.status),
                    trial.control.solver_checks.to_string(),
                    trial.control.satisfiability_checks.to_string(),
                    trial.control.observed_domain_checks.to_string(),
                    trial.control.unobserved_domain_checks.to_string(),
                    effect_count(trial, PrivateDomainObservationEffect::ObservationDependent)
                        .to_string(),
                    effect_count(trial, PrivateDomainObservationEffect::AlreadyImplied).to_string(),
                    effect_count(trial, PrivateDomainObservationEffect::Unresolved).to_string(),
                    trial.workflow_complete().to_string(),
                    ms(report.elapsed),
                    ms(trial.validation_elapsed),
                    ms(trial.control.elapsed),
                    ms(trial.workflow_elapsed()),
                ],
            )?;
        }
    }
    Ok(())
}

fn write_cells(writer: &mut impl Write, cases: &[Measurements]) -> Result<()> {
    row(
        writer,
        [
            "case",
            "profile",
            "repetition",
            "warmup",
            "cell",
            "target_role",
            "uniqueness",
            "domain",
            "domain_is_complete",
            "expected_projection",
            "baseline",
            "ucp_baseline_refined",
            "refinement_evidence",
            "discovery_evidence",
            "recovery_limitation",
            "observation_effect",
            "observed_coverage",
            "unobserved_alternative",
            "control_limitation",
        ]
        .map(str::to_owned),
    )?;
    for case in cases {
        for trial in &case.trials {
            for ((cell, effect), expected) in trial
                .recovery
                .cells
                .iter()
                .zip(&trial.control.cells)
                .zip(&case.spec.expected)
            {
                row(
                    writer,
                    vec![
                        case.spec.id.into(),
                        format!("{:?}", trial.profile),
                        trial.repetition.to_string(),
                        (trial.repetition == 0).to_string(),
                        cell.cell.to_string(),
                        expected.role.into(),
                        format!("{:?}", cell.uniqueness),
                        format!("{:?}", cell.domain),
                        cell.domain_is_complete.to_string(),
                        expected
                            .values
                            .as_ref()
                            .map_or_else(|| "FullField".into(), |values| format!("{values:?}")),
                        format!("{:?}", cell.baseline_domain),
                        cell.domain_refined_from_baseline.to_string(),
                        format!("{:?}", cell.domain_refinement),
                        format!("{:?}", cell.domain_discovery),
                        format!("{:?}", cell.recovery_limitation),
                        format!("{:?}", effect.effect),
                        effect.observed_domain_verified.to_string(),
                        format!("{:?}", effect.unobserved_counterexample),
                        format!("{:?}", effect.limitation),
                    ],
                )?;
            }
        }
    }
    Ok(())
}

fn write_summary(writer: &mut impl Write, cases: &[Measurements]) -> Result<()> {
    row(
        writer,
        [
            "case",
            "profile",
            "measured_attempts",
            "recovery_analyzed",
            "validation_completed",
            "control_completed",
            "workflow_checks_completed",
            "expected_projection_matches_min",
            "expected_projection_matches_max",
            "recovery_analyzed_median_ms",
            "validation_completed_median_ms",
            "control_completed_median_ms",
            "workflow_completed_median_ms",
            "optional_search_incomplete_attempts",
        ]
        .map(str::to_owned),
    )?;
    for case in cases {
        for profile in PROFILES {
            let trials: Vec<_> = case
                .trials
                .iter()
                .filter(|trial| trial.profile == profile && trial.repetition > 0)
                .collect();
            row(
                writer,
                vec![
                    case.spec.id.into(),
                    format!("{profile:?}"),
                    trials.len().to_string(),
                    trials
                        .iter()
                        .filter(|trial| trial.recovery_complete())
                        .count()
                        .to_string(),
                    trials
                        .iter()
                        .filter(|trial| trial.validation_complete())
                        .count()
                        .to_string(),
                    trials
                        .iter()
                        .filter(|trial| trial.control_complete())
                        .count()
                        .to_string(),
                    trials
                        .iter()
                        .filter(|trial| trial.workflow_complete())
                        .count()
                        .to_string(),
                    optional(
                        trials
                            .iter()
                            .map(|trial| trial.expected_projections_recovered)
                            .min(),
                    ),
                    optional(
                        trials
                            .iter()
                            .map(|trial| trial.expected_projections_recovered)
                            .max(),
                    ),
                    median(
                        trials
                            .iter()
                            .filter(|trial| trial.recovery_complete())
                            .map(|trial| trial.recovery.elapsed),
                    ),
                    median(
                        trials
                            .iter()
                            .filter(|trial| trial.validation_complete())
                            .map(|trial| trial.validation_elapsed),
                    ),
                    median(
                        trials
                            .iter()
                            .filter(|trial| trial.control_complete())
                            .map(|trial| trial.control.elapsed),
                    ),
                    median(
                        trials
                            .iter()
                            .filter(|trial| trial.workflow_complete())
                            .map(|trial| trial.workflow_elapsed()),
                    ),
                    trials
                        .iter()
                        .filter(|trial| trial.optional_search_incomplete())
                        .count()
                        .to_string(),
                ],
            )?;
        }
    }
    Ok(())
}

fn metadata(timeout_ms: u64, repetitions: usize) -> String {
    let git_status = command_line("git", &["status", "--porcelain"]);
    let mut value = format!("# schema: private-recovery-profiles-v1\n# unix_time: {}\n# profile: {}\n# platform: {}-{}\n# rust: {}\n# cvc5: {}\n# git_revision: {}\n# git_status: {}\n# field_modulus: {}\n# stored_value_bits_limit: {MAX_VALUE_BITS}\n# finite_domain_size_limit: {MAX_FINITE_DOMAIN_SIZE}\n# solver_timeout_ms: {timeout_ms}\n# solver_process_policy: supervised-wallclock-per-invocation\n# repetitions: {repetitions}\n# recorded_warmups_per_profile: 1\n# schedule: cyclic-profile-order-per-case\n# serial: true\n# semantic_unit: cell-queries-not-solver-invocations\n# incomplete_attempts: retained-no-timeout-speedups\n# recovery_policy: {PRIVACY_SEARCH_POLICY}\n# export_policy: {PRIVACY_SMT_DOMAIN_POLICY}\n# sat_policy: {PRIVACY_SAT_HINT_POLICY}\n# refinement_policy: {PRIVACY_DOMAIN_REFINEMENT_POLICY}\n# discovery_policy: {PRIVACY_DOMAIN_DISCOVERY_POLICY}\n# subset_policy: {PRIVACY_TARGETED_SUBSET_POLICY}\n# validation_policy: {PRIVACY_VALIDATION_POLICY}\n# observation_policy: {PRIVACY_OBSERVATION_POLICY}\n",
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_secs(), if cfg!(debug_assertions) { "debug" } else { "release" }, std::env::consts::OS, std::env::consts::ARCH, command_line("rustc", &["--version"]), command_line("cvc5", &["--version"]), command_line("git", &["rev-parse", "HEAD"]), command_line("git", &["status", "--porcelain"]), super::extractor::field_modulus::<Fr>());
    for profile in PROFILES {
        value.push_str(&format!(
            "# {profile:?}_options: {:?}\n",
            profile.options(timeout_ms)
        ));
    }
    value.push_str(&format!(
        "# working_tree_dirty: {}\n",
        if git_status == "unavailable" {
            "unavailable"
        } else if git_status.is_empty() {
            "false"
        } else {
            "true"
        }
    ));
    value
}

fn export(path: &Path, metadata: &str, cases: &[Measurements]) -> Result<()> {
    for (path, write) in [
        (
            path.to_path_buf(),
            write_samples as fn(&mut BufWriter<File>, &[Measurements]) -> Result<()>,
        ),
        (path.with_extension("cells.tsv"), write_cells),
        (path.with_extension("summary.tsv"), write_summary),
    ] {
        let mut writer = BufWriter::new(
            File::create(&path).with_context(|| format!("Cannot create {}", path.display()))?,
        );
        writer.write_all(metadata.as_bytes())?;
        write(&mut writer, cases)?;
        writer.flush()?;
    }
    Ok(())
}

#[test]
fn privacy_profile_options_isolate_paths_and_keep_solver_timeouts_equal() {
    for profile in PROFILES {
        let options = profile.options(2_000);
        assert_eq!(options.solver_timeout_ms, Some(2_000));
        assert_eq!(options.max_semantic_queries, 32);
        assert_eq!(options.search.retry_solver_timeout_ms, None);
        assert_eq!(options.domain_discovery.retry_solver_timeout_ms, None);
        assert_eq!(
            options.domain_refinement.max_solver_checks > 0,
            profile == Profile::Refinement
        );
        assert_eq!(
            options.domain_discovery.use_targeted_subsets,
            profile == Profile::TargetedDiscovery
        );
    }
    let metadata = metadata(2_000, 3);
    assert!(metadata
        .contains("# observation_policy: original-observed-coverage-unobserved-exclusion-v1\n"));
    assert!(metadata.contains("# recorded_warmups_per_profile: 1\n"));
    assert_eq!(median([]), "NA");
}

#[test]
fn privacy_profile_smoke_compares_unseeded_and_seeded_projections() {
    for id in ["expanded_two_roots", "lookup_seeded_two_roots"] {
        let measured = measure_case(id, 1, 2_000).unwrap();
        assert_eq!(measured.trials.len(), 8);
        let baseline = measured
            .trials
            .iter()
            .find(|trial| trial.repetition == 1 && trial.profile == Profile::Baseline)
            .unwrap();
        assert_eq!(baseline.expected_projections_recovered, 1);
        let stronger = if id == "expanded_two_roots" {
            Profile::Discovery
        } else {
            Profile::Refinement
        };
        let refined = measured
            .trials
            .iter()
            .find(|trial| trial.repetition == 1 && trial.profile == stronger)
            .unwrap();
        assert_eq!(refined.expected_projections_recovered, 2);
        assert!(refined.workflow_complete());
        if stronger == Profile::Discovery {
            let targeted = measured
                .trials
                .iter()
                .find(|trial| trial.repetition == 1 && trial.profile == Profile::TargetedDiscovery)
                .unwrap();
            assert_eq!(targeted.expected_projections_recovered, 2);
            assert!(
                targeted
                    .recovery
                    .domain_discovery_statistics
                    .subset_solver_checks
                    > 0
            );
        }
    }
}

#[test]
fn privacy_profile_smoke_distinguishes_intrinsic_and_public_recovery() {
    for (id, effect) in [
        (
            "intrinsic_singleton",
            PrivateDomainObservationEffect::AlreadyImplied,
        ),
        (
            "mask_reused_composition",
            PrivateDomainObservationEffect::ObservationDependent,
        ),
    ] {
        let measured = measure_case(id, 1, 2_000).unwrap();
        for trial in &measured.trials {
            assert_eq!(trial.expected_projections_recovered, 2);
            assert_eq!(effect_count(trial, effect), 2);
            assert_eq!(trial.control.solver_checks, 5);
            assert!(trial.workflow_complete());
        }
    }
}

#[test]
fn privacy_profile_partial_attempts_are_retained_but_not_completed_medians() {
    let spec = CaseSpec {
        id: "partial",
        origin: "synthetic_demo",
        k: 4,
        expected: vec![
            ExpectedProjection::finite(&[1], PrivateDomainObservationEffect::AlreadyImplied),
            ExpectedProjection::finite(&[3], PrivateDomainObservationEffect::AlreadyImplied),
        ],
    };
    let circuit = UnboundedProjectionCircuit::<UNIQUE>::new(Fr::from(1), Fr::from(3));
    let mut options = Profile::Discovery.options(2_000);
    options.max_semantic_queries = 0;
    options.domain_discovery.max_solver_checks = 1;
    let trial = run_trial(
        &spec,
        &circuit,
        &discovery_demo_input(),
        &discovery_demo_targets(),
        Profile::Discovery,
        options,
        1,
        0,
    )
    .unwrap();
    assert_eq!(
        trial.recovery.status,
        PrivacyAnalysisStatus::QueryLimitReached
    );
    assert_eq!(trial.recovery.domain_discovery_statistics.solver_checks, 1);
    assert_eq!(trial.expected_projections_recovered, 0);
    assert!(!trial.workflow_complete());
    let measured = Measurements {
        spec,
        trials: vec![trial],
    };
    let mut summary = Vec::new();
    write_summary(&mut summary, std::slice::from_ref(&measured)).unwrap();
    let summary = String::from_utf8(summary).unwrap();
    let row = summary
        .lines()
        .find(|line| line.starts_with("partial\tDiscovery\t"))
        .unwrap()
        .split('\t')
        .collect::<Vec<_>>();
    assert_eq!(row[2], "1");
    assert_eq!(row[3], "0");
    assert_eq!(row[9], "NA");
    assert_eq!(row[12], "NA");
    let mut samples = Vec::new();
    write_samples(&mut samples, &[measured]).unwrap();
    assert!(String::from_utf8(samples)
        .unwrap()
        .contains("QueryLimitReached"));
}

#[test]
fn privacy_profile_exports_are_aligned_and_preserve_cell_evidence() {
    let mut measured = measure_case("intrinsic_singleton", 1, 2_000).unwrap();
    for write in [
        write_samples as fn(&mut Vec<u8>, &[Measurements]) -> Result<()>,
        write_cells,
        write_summary,
    ] {
        let mut bytes = Vec::new();
        write(&mut bytes, std::slice::from_ref(&measured)).unwrap();
        let text = String::from_utf8(bytes).unwrap();
        let columns = text.lines().next().unwrap().split('\t').count();
        assert!(text
            .lines()
            .skip(1)
            .all(|line| line.split('\t').count() == columns));
    }
    let mut cells = Vec::new();
    write_cells(&mut cells, std::slice::from_ref(&measured)).unwrap();
    let cells = String::from_utf8(cells).unwrap();
    assert!(cells.contains("AlreadyImplied"));
    assert!(cells.contains("Exact(1)"));
    assert!(cells.contains("derived_witness"));
    let measured_time = measured
        .trials
        .iter()
        .find(|trial| trial.profile == Profile::Baseline && trial.repetition == 1)
        .unwrap()
        .recovery
        .elapsed;
    for trial in measured
        .trials
        .iter_mut()
        .filter(|trial| trial.repetition == 0)
    {
        trial.recovery.elapsed = Duration::from_secs(999);
    }
    let mut summary = Vec::new();
    write_summary(&mut summary, std::slice::from_ref(&measured)).unwrap();
    let summary = String::from_utf8(summary).unwrap();
    let baseline = summary
        .lines()
        .find(|line| line.starts_with("intrinsic_singleton\tBaseline\t"))
        .unwrap()
        .split('\t')
        .collect::<Vec<_>>();
    assert_eq!(baseline[2], "1");
    assert_eq!(baseline[9], ms(measured_time)); // Recorded warm-ups never enter a median.
    let mut escaped = Vec::new();
    row(
        &mut escaped,
        ["timeout\nreason\tmore".into(), "next".into()],
    )
    .unwrap();
    assert_eq!(
        String::from_utf8(escaped).unwrap(),
        "timeout reason more\tnext\n"
    );
}

#[test]
fn privacy_profile_solver_unknown_is_recorded_without_fabricating_check_counts() {
    let mut measured = measure_case("intrinsic_singleton", 1, 2_000).unwrap();
    let index = measured
        .trials
        .iter()
        .position(|trial| trial.profile == Profile::Baseline && trial.repetition == 1)
        .unwrap();
    let mut trial = measured.trials.remove(index);
    // Inject only the reporting outcome; classification itself has separate original-SMT regressions.
    trial.validation = None;
    trial.validation_unknown = Some("solver unknown: TIMEOUT".into());
    trial.control.status = PublicObservationEffectStatus::SolverUnknown;
    trial.control.cells[0].effect = PrivateDomainObservationEffect::Unresolved;
    trial.control.cells[0].observed_domain_verified = false;
    measured.trials = vec![trial];
    let mut samples = Vec::new();
    write_samples(&mut samples, std::slice::from_ref(&measured)).unwrap();
    let samples = String::from_utf8(samples).unwrap();
    let mut lines = samples.lines();
    let header: Vec<_> = lines.next().unwrap().split('\t').collect();
    let values: Vec<_> = lines.next().unwrap().split('\t').collect();
    let column = |name| values[header.iter().position(|column| *column == name).unwrap()];
    assert_eq!(column("validation_checks"), "NA");
    assert_eq!(column("control_status"), "SolverUnknown");
    assert_eq!(column("workflow_checks_completed"), "false");
    assert!(column("validation_unknown").contains("TIMEOUT"));
    let mut summary = Vec::new();
    write_summary(&mut summary, &[measured]).unwrap();
    let summary = String::from_utf8(summary).unwrap();
    let row: Vec<_> = summary
        .lines()
        .find(|line| line.starts_with("intrinsic_singleton\tBaseline\t"))
        .unwrap()
        .split('\t')
        .collect();
    assert_eq!(row[2], "1");
    assert_eq!(row[3], "1");
    assert_eq!(&row[4..7], &["0", "0", "0"]);
    assert_eq!(&row[10..13], &["NA", "NA", "NA"]);
}

#[test]
fn privacy_profile_correctness_mismatches_remain_fatal() {
    let mut measured = measure_case("intrinsic_singleton", 1, 2_000).unwrap();
    let report = &mut measured.trials[0].recovery;
    report.cells[0].domain = Some(UcpValueDomain::exact(2.into()));
    assert!(check_recovery(report, &measured.spec).is_err());
    report.cells[0].domain = Some(UcpValueDomain::exact(1.into()));
    report.cells[0].uniqueness = PrivateCellUniqueness::NonUnique;
    assert!(check_recovery(report, &measured.spec).is_err());
    report.cells[0].uniqueness = PrivateCellUniqueness::Unique;
    report.status = PrivacyAnalysisStatus::Inconsistent;
    assert!(check_recovery(report, &measured.spec).is_err());
}

#[test]
fn privacy_profile_analyzed_ambiguity_does_not_hide_partial_enumeration() {
    let spec = CaseSpec {
        id: "partial_full_field",
        origin: "synthetic_demo",
        k: 4,
        expected: vec![
            ExpectedProjection {
                role: "private_input",
                values: None,
                complete_effect: PrivateDomainObservationEffect::NoDomainClaim
            };
            2
        ],
    };
    let mut options = Profile::Discovery.options(2_000);
    options.domain_discovery.max_solver_checks = 2;
    let trial = run_trial(
        &spec,
        &SecretCommitmentCircuit::new(42, 58),
        &observations(&[100]),
        &discovery_demo_targets(),
        Profile::Discovery,
        options,
        1,
        0,
    )
    .unwrap();
    assert_eq!(trial.recovery.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(trial.recovery.summary.non_unique_cells, 2);
    assert!(trial
        .recovery
        .cells
        .iter()
        .all(|cell| cell.domain.is_none()));
    assert!(trial.optional_search_incomplete());
    assert!(trial.workflow_complete()); // Checks completed, but enumeration did not.
    let measured = Measurements {
        spec,
        trials: vec![trial],
    };
    let mut summary = Vec::new();
    write_summary(&mut summary, &[measured]).unwrap();
    let summary = String::from_utf8(summary).unwrap();
    let values: Vec<_> = summary
        .lines()
        .find(|line| line.starts_with("partial_full_field\tDiscovery\t"))
        .unwrap()
        .split('\t')
        .collect();
    assert_eq!(values[3], "1");
    assert_eq!(values[6], "1");
    assert_eq!(values.last().copied(), Some("1"));
}

#[test]
#[ignore = "Repeated serial recovery profiles; set PRIVACY_PROFILE_TIMEOUT_MS and run explicitly"]
fn privacy_profile_measurement_suite() {
    let repetitions = std::env::var("PRIVACY_PROFILE_REPETITIONS")
        .unwrap_or_else(|_| "3".into())
        .parse::<usize>()
        .expect("Invalid repetition count");
    let timeout_ms = std::env::var("PRIVACY_PROFILE_TIMEOUT_MS")
        .expect("Set an explicit PRIVACY_PROFILE_TIMEOUT_MS")
        .parse::<u64>()
        .expect("Invalid solver timeout");
    assert!((1..=100).contains(&repetitions) && timeout_ms > 0);
    let cases: Vec<_> = CASES
        .into_iter()
        .map(|id| {
            println!("Measuring profiles for {id}...");
            measure_case(id, repetitions, timeout_ms).unwrap()
        })
        .collect();
    let metadata = metadata(timeout_ms, repetitions);
    let mut summary = Vec::new();
    write_summary(&mut summary, &cases).unwrap();
    println!("{metadata}{}", String::from_utf8(summary).unwrap());
    if let Some(path) = std::env::var_os("PRIVACY_PROFILE_OUTPUT") {
        export(Path::new(&path), &metadata, &cases).unwrap();
    }
}
