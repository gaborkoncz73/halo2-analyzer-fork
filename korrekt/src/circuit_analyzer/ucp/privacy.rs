#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

//! Recoverability of explicitly selected private inputs under fixed public observations.
//! Advice assignments are never used as recovered values. Finite domains are sound
//! candidate supersets; optional original-model searches can certify complete projections.
//! Neither domain sizes nor cell counts measure cryptographic security.
//! Results concern the supplied public observations, not all statements or protocol ZK.

use super::{
    cell::{CellId, CellKind},
    choose_var::choose_query_cell,
    engine::UcpResult,
    extractor::{extract_ucp_problem, UcpProblem},
    facts::UcpFacts,
    privacy_discovery::{
        full_discovery_response, DiscoveryProbe, DiscoveryResponse, DomainDiscoveryState,
        PrivacyDomainDiscoveryOptions, PrivacyDomainDiscoveryStatistics, PrivateDomainDiscovery,
        PrivateDomainDiscoveryStatus, PRIVACY_DOMAIN_DISCOVERY_POLICY,
    },
    privacy_domain::{
        DomainRefinementState, PrivacyDomainRefinementOptions, PrivacyDomainRefinementStatistics,
        PrivateDomainRefinement, PRIVACY_DOMAIN_REFINEMENT_POLICY,
    },
    privacy_subset::PRIVACY_TARGETED_SUBSET_POLICY,
    value::{normalize_field_value, parse_cell_id, UcpValueDomain, UcpValueFacts},
};
use crate::{
    circuit_analyzer::{
        analyzable::{Analyzable, AnalyzableField},
        analyzer::{Analyzer, SemanticQueryOutput, SemanticQueryResult, ValueRecoveryFailure},
        halo2_proofs_libs::*,
    },
    io::analyzer_io_type::{AnalyzerInput, AnalyzerType, LookupMethod, VerificationMethod},
    smt_solver::smt_parser::{Satisfiability, SolverUnknownDetails, UnknownSolverResult},
};
use anyhow::{ensure, Context, Result};
use num_bigint::BigInt;
use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    fmt,
    time::{Duration, Instant},
};

pub(crate) const PRIVACY_SMT_DOMAIN_POLICY: &str = "exact-and-new-or-refined-domains";
pub(crate) const PRIVACY_SAT_HINT_POLICY: &str =
    "target-exact-ucp-hints-positive-only-original-fallback";
pub(crate) const PRIVACY_SEARCH_POLICY: &str = "reserved-targets-progress-bounded-retries-v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrivacyAnalysisStatus {
    /// All selected cells have a value or have been attempted; recovery may be incomplete.
    Analyzed,
    QueryLimitReached,
    SolverUnknown,
    Inconsistent,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrivateCellUniqueness {
    Unique,
    /// SMT found two satisfying assignments differing at this cell under the same observations.
    NonUnique,
    /// No uniqueness or non-uniqueness conclusion was obtained; not evidence of secrecy.
    Unknown,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrivacyAnalysisOptions {
    /// Hard total limit, including bridges and retries. Never resets on progress.
    pub max_semantic_queries: usize,
    /// CVC5 check limit and supervised wall-clock budget per solver invocation.
    /// None inherits HALO2_ANALYZER_SMT_TIMEOUT_MS.
    /// This is not a hard deadline for synthesis, UCP, or the whole analysis.
    pub solver_timeout_ms: Option<u64>,
    pub search: PrivacySearchOptions,
    /// Optional finite-set checking, with a separate hard solver-invocation budget.
    pub domain_refinement: PrivacyDomainRefinementOptions,
    /// Optional original-model enumeration for cells without any inferred value domain.
    pub domain_discovery: PrivacyDomainDiscoveryOptions,
}

impl Default for PrivacyAnalysisOptions {
    fn default() -> Self {
        Self {
            max_semantic_queries: 256,
            solver_timeout_ms: None,
            search: PrivacySearchOptions::default(),
            domain_refinement: PrivacyDomainRefinementOptions::default(),
            domain_discovery: PrivacyDomainDiscoveryOptions::default(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrivacySearchOptions {
    /// Total allowance for non-target cells; first target attempts are reserved separately.
    pub max_bridge_queries: usize,
    /// Stops optional bridge/retry work, never an unattempted target's first query.
    pub max_queries_without_progress: usize,
    /// Only inconclusive target queries can be retried, after progress or a larger budget.
    pub max_retries_per_target: usize,
    /// Retry budget floor. Never reduces the initial budget, including unlimited mode.
    pub retry_solver_timeout_ms: Option<u64>,
}

impl Default for PrivacySearchOptions {
    fn default() -> Self {
        Self {
            max_bridge_queries: 32,
            max_queries_without_progress: 32,
            max_retries_per_target: 1,
            retry_solver_timeout_ms: Some(10_000),
        }
    }
}

impl PrivacyAnalysisOptions {
    fn retry_timeout_ms(&self) -> Option<u64> {
        self.solver_timeout_ms
            .map(|initial| initial.max(self.search.retry_solver_timeout_ms.unwrap_or(initial)))
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PrivacySearchStatistics {
    pub target_queries: usize,
    pub bridge_queries: usize,
    /// A subset of target_queries, not an additional query count.
    pub retry_queries: usize,
    /// Recovery fixpoint runs, excluding the structural baseline and initial SAT hints.
    pub propagation_runs: usize,
    pub progress_rounds: usize,
    pub queries_without_progress: usize,
    /// No exact value and no uniqueness/domain SMT attempt; not evidence of secrecy.
    pub unqueried_targets: usize,
    pub stop_reason: Option<PrivacySearchStopReason>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrivacySearchStopReason {
    TotalQueryLimit,
    NoProgressLimit,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrivateRecoveryStatus {
    Recovered,
    UniqueWithoutValue,
    NonUnique,
    Unresolved,
    UnsupportedValueRepresentation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RecoveryLimitation {
    QueryLimit,
    SolverTimeout,
    SolverUnknown { reason: Option<String> },
    ValueRepresentationLimit,
    DomainSizeLimit,
    NoConcreteValue,
    InconsistentContext,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnsupportedPrivacyFeature {
    InlineLookupsRequired,
    FixedUnrotatedTablesRequired,
}

impl fmt::Display for UnsupportedPrivacyFeature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InlineLookupsRequired => {
                "Privacy analysis requires inline lookup constraints for validated witnesses"
            }
            Self::FixedUnrotatedTablesRequired => {
                "Privacy analysis requires concrete, unrotated fixed lookup tables"
            }
        })
    }
}

impl std::error::Error for UnsupportedPrivacyFeature {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrivateCellReport {
    pub cell: CellId,
    /// Uniqueness query attempts only; finite-domain checks are accounted for separately.
    pub query_attempts: usize,
    pub uniqueness: PrivateCellUniqueness,
    pub domain: Option<UcpValueDomain>,
    /// Inferred without fixing concrete public observations, including structural ranges.
    pub baseline_domain: Option<UcpValueDomain>,
    /// Improvement over the UCP baseline; SMT reasoning can also cause this refinement.
    /// This is not a measured entropy loss or proof of causation by public data alone.
    /// Use analyze_public_observation_effect for an original-SMT control of a reported domain.
    pub domain_refined_from_baseline: bool,
    pub recovery_limitation: Option<RecoveryLimitation>,
    /// None means no finite-domain SMT refinement was attempted, not that the set is complete.
    pub domain_refinement: Option<PrivateDomainRefinement>,
    /// Partial observed values are model samples, not a covering Delta domain.
    pub domain_discovery: Option<PrivateDomainDiscovery>,
}

impl PrivateCellReport {
    /// Derive the category from evidence instead of storing a second, potentially stale label.
    pub fn recovery_status(&self) -> PrivateRecoveryStatus {
        if matches!(self.domain, Some(UcpValueDomain::Exact(_))) {
            PrivateRecoveryStatus::Recovered
        } else if self.recovery_limitation == Some(RecoveryLimitation::ValueRepresentationLimit) {
            PrivateRecoveryStatus::UnsupportedValueRepresentation
        } else {
            match self.uniqueness {
                PrivateCellUniqueness::Unique => PrivateRecoveryStatus::UniqueWithoutValue,
                PrivateCellUniqueness::NonUnique => PrivateRecoveryStatus::NonUnique,
                PrivateCellUniqueness::Unknown => PrivateRecoveryStatus::Unresolved,
            }
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PrivacyAnalysisSummary {
    pub private_cells: usize,
    pub exact_values: usize,
    pub finite_domains: usize,
    pub unique_cells: usize,
    pub non_unique_cells: usize,
    pub unresolved_uniqueness: usize,
    pub refined_domains: usize,
}

#[derive(Debug)]
pub struct PrivacyAnalysisReport {
    pub status: PrivacyAnalysisStatus,
    pub cells: Vec<PrivateCellReport>,
    pub summary: PrivacyAnalysisSummary,
    pub public_values: Vec<(CellId, BigInt)>,
    pub semantic_queries: usize,
    pub search_statistics: PrivacySearchStatistics,
    pub domain_refinement_statistics: PrivacyDomainRefinementStatistics,
    pub domain_discovery_statistics: PrivacyDomainDiscoveryStatistics,
    pub satisfiability_checks: usize,
    pub elapsed: Duration,
    /// Effective options, including the resolved solver budget, for reproducible measurements.
    pub options: PrivacyAnalysisOptions,
    /// No inferred facts are reported for an inconsistent constraint system.
    pub ucp_result: Option<UcpResult>,
}

pub(crate) struct PrivacyAnalysisContext<F: AnalyzableField> {
    pub problem: UcpProblem,
    pub analyzer: Analyzer<F>,
    pub analyzer_input: AnalyzerInput,
    pub public_values: Vec<(CellId, BigInt)>,
    pub private_cells: Vec<CellId>,
}

#[derive(Default)]
struct CellQueryState {
    attempts: usize,
    generation: usize,
    timeout_ms: Option<u64>,
    retryable: bool,
}

struct RecoverySearchState {
    statistics: PrivacySearchStatistics,
    cells: BTreeMap<CellId, CellQueryState>,
    previous_facts: UcpFacts,
    previous_values: UcpValueFacts,
    generation: usize,
}

impl RecoverySearchState {
    fn new(facts: &UcpFacts, values: &UcpValueFacts) -> Self {
        Self {
            statistics: PrivacySearchStatistics::default(),
            cells: BTreeMap::new(),
            previous_facts: facts.clone(),
            previous_values: values.clone(),
            generation: 0,
        }
    }

    fn observe_progress(&mut self, result: &UcpResult, modulus: &BigInt) {
        let changed = result
            .facts
            .unique_cells()
            .difference(self.previous_facts.unique_cells())
            .next()
            .is_some()
            || result.value_facts.domains().iter().any(|(cell, domain)| {
                domain_refined(self.previous_values.domain(cell), Some(domain), modulus)
            });
        if changed {
            self.generation += 1;
            self.statistics.progress_rounds += 1;
            self.statistics.queries_without_progress = 0;
        }
        self.previous_facts = result.facts.clone();
        self.previous_values = result.value_facts.clone();
    }

    fn total_queries(&self) -> usize {
        self.statistics.target_queries + self.statistics.bridge_queries
    }

    fn record_query(&mut self, cell: &CellId, is_target: bool, timeout_ms: Option<u64>) {
        let state = self.cells.entry(cell.clone()).or_default();
        if is_target {
            self.statistics.target_queries += 1;
            self.statistics.retry_queries += usize::from(state.attempts > 0);
        } else {
            self.statistics.bridge_queries += 1;
        }
        state.attempts += 1;
        state.generation = self.generation;
        state.timeout_ms = timeout_ms;
        state.retryable = false;
        self.statistics.queries_without_progress += 1;
    }

    fn retry_candidate(
        &self,
        pending: &[CellId],
        options: &PrivacyAnalysisOptions,
    ) -> Option<CellId> {
        pending
            .iter()
            .find(|cell| {
                let Some(state) = self.cells.get(*cell) else {
                    return false;
                };
                let increased_budget = match (state.timeout_ms, options.retry_timeout_ms()) {
                    (Some(previous), Some(next)) => next > previous,
                    _ => false,
                };
                state.retryable
                    && state.attempts <= options.search.max_retries_per_target
                    && (state.generation < self.generation || increased_budget)
            })
            .cloned()
    }
}

// Positive-only SAT acceleration: candidates guide existence checking, never recovery premises.
pub(crate) fn check_privacy_satisfiability<F: AnalyzableField>(
    context: &mut PrivacyAnalysisContext<F>,
) -> (Result<Satisfiability>, usize) {
    let mut values = context.problem.initial_value_facts.clone();
    for (cell, value) in &context.public_values {
        values.mark_known(cell.clone(), value.clone());
    }
    let candidates = context
        .problem
        .analyze_with_values(context.problem.initial_facts.clone(), values);
    let hinted = if context
        .private_cells
        .iter()
        .any(|cell| candidates.value_facts.known_value(cell).is_some())
    {
        context
            .analyzer
            .check_ucp_satisfiability_with_hints(&context.analyzer_input, &candidates.value_facts)
    } else {
        // Intrinsic constants alone rarely help inversion; do not spend another solver budget.
        Ok(None)
    };
    let hint_checks = usize::from(!matches!(&hinted, Ok(None)));
    match accept_sat_hint(hinted) {
        Ok(true) => (Ok(Satisfiability::Satisfiable), hint_checks),
        Ok(false) => (
            context
                .analyzer
                .check_ucp_satisfiability(&context.analyzer_input),
            hint_checks + 1,
        ),
        Err(error) => (Err(error), hint_checks),
    }
}

fn accept_sat_hint(result: Result<Option<Satisfiability>>) -> Result<bool> {
    match result {
        Ok(Some(Satisfiability::Satisfiable)) => Ok(true),
        Ok(None | Some(Satisfiability::Unsatisfiable)) => Ok(false),
        Err(error) if error.downcast_ref::<UnknownSolverResult>().is_some() => Ok(false),
        Err(error) => Err(error),
    }
}

//Recovery and independent validation must use the same supported circuit/public interface.
pub(crate) fn prepare_privacy_analysis<F, ConcreteCircuit, I>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    private_cells: I,
) -> Result<PrivacyAnalysisContext<F>>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
    I: IntoIterator<Item = CellId>,
{
    prepare_privacy_analysis_with_capture(circuit, k, analyzer_input, private_cells, false)
}

pub(crate) fn prepare_privacy_analysis_with_capture<F, ConcreteCircuit, I>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    private_cells: I,
    capture_original: bool,
) -> Result<PrivacyAnalysisContext<F>>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
    I: IntoIterator<Item = CellId>,
{
    analyzer_input.verification_input.validate_public_values()?;
    let private_cells: Vec<_> = private_cells
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    ensure!(
        !private_cells.is_empty(),
        "Select at least one private advice cell"
    );
    let analyzable = Analyzable::config_and_synthesize(circuit, k)
        .context("Failed to synthesize circuit for privacy analysis")?;
    if !analyzable.cs.lookups.is_empty()
        && analyzer_input.lookup_method != LookupMethod::InlineConstraints
    {
        return Err(UnsupportedPrivacyFeature::InlineLookupsRequired.into());
    }
    //The analyzer's inline encoder supports concrete, unrotated table columns only.
    if !analyzable.cs.lookups.iter().all(|lookup| {
        lookup
            .table_expressions
            .iter()
            .all(|expr| matches!(expr, Expression::Fixed(query) if query.rotation.0 == 0))
    }) {
        return Err(UnsupportedPrivacyFeature::FixedUnrotatedTablesRequired.into());
    }
    let problem = extract_ucp_problem(&analyzable);
    let witnesses: HashSet<_> = problem.witness_cells.iter().collect();
    for cell in &private_cells {
        ensure!(
            cell.kind == CellKind::Advice && witnesses.contains(cell),
            "Private cell {} is not an assigned or referenced advice cell",
            cell
        );
    }

    let mut public_values = BTreeMap::new();
    for (name, value) in &analyzer_input.verification_input.instance_cells {
        let cell =
            parse_cell_id(name).with_context(|| format!("Invalid public cell name: {}", name))?;
        ensure!(
            cell.kind == CellKind::Instance && cell.to_string() == *name,
            "Public observations must name instance cells, not private witnesses: {}",
            name
        );
        let value = normalize_field_value(value.clone(), &problem.field_modulus)
            .context("Public observation is outside the supported value range")?;
        public_values.insert(cell, value);
    }
    ensure!(
        public_values.is_empty()
            || analyzer_input.verification_method == VerificationMethod::Specific,
        "Concrete public observations require Specific verification"
    );
    //Validate before Analyzer::new, which can prompt interactively for missing public values.
    for cell in problem.initial_facts.unique_cells() {
        if cell.kind == CellKind::Instance {
            ensure!(
                public_values.contains_key(cell),
                "Missing concrete public observation for {}",
                cell
            );
        }
    }
    //An empty Specific map must not open the analyzer's interactive input prompt.
    let mut effective_input = analyzer_input.clone();
    if effective_input.verification_input.instance_cells.is_empty() {
        effective_input.verification_method = VerificationMethod::None;
    }
    let analyzer_input = &effective_input;
    let analyzer = Analyzer::<F>::new_with_original_subset_capture(
        circuit,
        k,
        AnalyzerType::UnderconstrainedCircuit,
        Some(analyzer_input),
        capture_original,
    )
    .context("Failed to initialize privacy SMT analyzer")?;
    //Lookups can introduce public queries that are absent from the UCP gate expressions.
    for name in &analyzer.all_variables {
        if name.starts_with("I-") {
            ensure!(
                analyzer_input
                    .verification_input
                    .instance_cells
                    .contains_key(name),
                "Missing concrete public observation for {}",
                name
            );
        }
    }
    let public_values: Vec<_> = public_values.into_iter().collect();
    Ok(PrivacyAnalysisContext {
        problem,
        analyzer,
        analyzer_input: effective_input,
        public_values,
        private_cells,
    })
}

/// Uses the existing instance_cells mapping for public observations, including
/// published outputs exposed through instance columns. Select genuine secret
/// advice cells explicitly; multiple witnesses do not imply an underconstrained output.
pub fn analyze_private_recoverability<F, ConcreteCircuit, I>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    private_cells: I,
    options: PrivacyAnalysisOptions,
) -> Result<PrivacyAnalysisReport>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
    I: IntoIterator<Item = CellId>,
{
    let started = Instant::now();
    //Validate before synthesis; explicit options override the legacy environment fallback.
    let effective_timeout = Analyzer::<F>::resolve_smt_timeout_ms(options.solver_timeout_ms)?;
    let options = PrivacyAnalysisOptions {
        solver_timeout_ms: effective_timeout,
        ..options
    };
    ensure!(
        options.search.retry_solver_timeout_ms != Some(0),
        "Retry solver timeout must be greater than zero"
    );
    options.domain_refinement.validate()?;
    options.domain_discovery.validate()?;
    let mut context = prepare_privacy_analysis_with_capture::<F, _, _>(
        circuit,
        k,
        analyzer_input,
        private_cells,
        options.domain_discovery.max_solver_checks > 0
            && options.domain_discovery.use_targeted_subsets,
    )?;
    context
        .analyzer
        .set_smt_timeout_ms(options.solver_timeout_ms)?;
    let (initial_check, satisfiability_checks) = check_privacy_satisfiability(&mut context);
    let mut report = analyze_prepared(
        context,
        options,
        started,
        initial_check,
        |analyzer, input, cell| analyzer.query_ucp_cell_uniqueness_with_value(input, cell),
    )?;
    report.satisfiability_checks = satisfiability_checks;
    Ok(report)
}

//A single driver keeps real and deterministic unknown-result tests on the same state machine.
fn analyze_prepared<F: AnalyzableField>(
    context: PrivacyAnalysisContext<F>,
    options: PrivacyAnalysisOptions,
    started: Instant,
    initial_check: Result<Satisfiability>,
    mut query: impl FnMut(&mut Analyzer<F>, &AnalyzerInput, &CellId) -> Result<SemanticQueryOutput>,
) -> Result<PrivacyAnalysisReport> {
    let PrivacyAnalysisContext {
        problem,
        mut analyzer,
        analyzer_input,
        public_values,
        private_cells,
    } = context;
    let analyzer_input = &analyzer_input;
    let initial_failure = match initial_check {
        Ok(Satisfiability::Satisfiable) => None,
        Ok(Satisfiability::Unsatisfiable) => Some((
            PrivacyAnalysisStatus::Inconsistent,
            RecoveryLimitation::InconsistentContext,
        )),
        Err(error) => Some((
            PrivacyAnalysisStatus::SolverUnknown,
            limitation_from_solver_error(error)?,
        )),
    };
    if let Some((status, limitation)) = initial_failure {
        let cells = private_cells
            .into_iter()
            .map(|cell| PrivateCellReport {
                cell,
                query_attempts: 0,
                uniqueness: PrivateCellUniqueness::Unknown,
                domain: None,
                baseline_domain: None,
                domain_refined_from_baseline: false,
                recovery_limitation: Some(limitation.clone()),
                domain_refinement: None,
                domain_discovery: None,
            })
            .collect();
        return Ok(finish_report(
            status,
            cells,
            public_values,
            PrivacySearchStatistics::default(),
            started.elapsed(),
            None,
            options,
        ));
    }

    // Preserve original premises; search-only exact assertions never modify this snapshot.
    let original_context = if options.domain_refinement.max_solver_checks > 0
        || options.domain_discovery.max_solver_checks > 0
    {
        Some(analyzer.original_private_query_context(analyzer_input, &private_cells)?)
    } else {
        None
    };
    let mut domain_search = DomainRefinementState::new(options.domain_refinement);
    let mut discovery = DomainDiscoveryState::new(options.domain_discovery);

    // Structural UCP baseline only; the separate SMT observation control distinguishes public effects.
    let baseline = problem.analyze_with_values(
        problem.initial_facts.clone(),
        problem.initial_value_facts.clone(),
    );
    let facts = baseline.facts.clone();
    let mut values = baseline.value_facts.clone();
    for (cell, value) in &public_values {
        values.mark_known(cell.clone(), value.clone());
    }
    let private_set: HashSet<_> = private_cells.iter().cloned().collect();
    let mut non_unique = HashSet::new();
    let mut limitations = BTreeMap::new();
    let mut search = RecoverySearchState::new(&facts, &values);
    let mut result = problem.analyze_with_values(facts, values);
    search.statistics.propagation_runs += 1;
    search.observe_progress(&result, &problem.field_modulus);
    let mut exact_search_facts = original_context
        .as_ref()
        .map(|original| original.search_exact_facts(&analyzer, &result.value_facts))
        .transpose()?
        .unwrap_or_default();
    let mut propagation_needed = false;
    let (status, result) = loop {
        // Search evidence alone does not invalidate the existing propagation fixpoint.
        if propagation_needed {
            result = problem.analyze_with_values(result.facts, result.value_facts);
            search.statistics.propagation_runs += 1;
            search.observe_progress(&result, &problem.field_modulus);
            if let Some(original) = &original_context {
                exact_search_facts = original.search_exact_facts(&analyzer, &result.value_facts)?;
            }
            propagation_needed = false;
        }
        if let Some(original) = &original_context {
            // Complete original-model enumeration already established coverage and feasibility.
            let refinement_targets: Vec<_> = private_cells
                .iter()
                .filter(|cell| {
                    discovery.cells.get(*cell).is_none_or(|evidence| {
                        evidence.status != PrivateDomainDiscoveryStatus::Complete
                    })
                })
                .cloned()
                .collect();
            if let Some((cell, domain, proven_non_unique)) = domain_search.refine_next(
                &refinement_targets,
                &problem,
                &result,
                |cell, domain, exclude| {
                    if exclude {
                        // Coverage is checked independently of all recovered assertions.
                        original.check_membership::<F>(
                            cell,
                            domain,
                            true,
                            options.solver_timeout_ms,
                        )
                    } else {
                        original.check_candidate_with_exact_facts::<F>(
                            cell,
                            domain,
                            options.solver_timeout_ms,
                            &exact_search_facts,
                        )
                    }
                },
            )? {
                propagation_needed |= result.value_facts.mark_domain(cell.clone(), domain);
                if proven_non_unique {
                    non_unique.insert(cell);
                }
                // A smaller Delta can activate other UCP rules and make new finite targets eligible.
                continue;
            }
            if let Some((cell, domain, proven_non_unique)) = discovery.discover_next_with_subsets(
                &private_cells,
                &problem.expressions,
                &result,
                &problem.field_modulus,
                options.solver_timeout_ms,
                |cell, blocked, timeout, probe| {
                    if probe == DiscoveryProbe::SubsetExclusion
                        && original.has_targeted_subset(cell)
                    {
                        match original.check_unseen_subset::<F>(cell, blocked, timeout) {
                            Ok(Satisfiability::Unsatisfiable) => Ok(DiscoveryResponse::SubsetUnsat),
                            Ok(Satisfiability::Satisfiable) => {
                                Ok(DiscoveryResponse::SubsetFallback { unknown: false })
                            }
                            Err(error) if error.downcast_ref::<UnknownSolverResult>().is_some() => {
                                Ok(DiscoveryResponse::SubsetFallback { unknown: true })
                            }
                            Err(error) => Err(error),
                        }
                    } else {
                        full_discovery_response(original.query_unseen_value_with_exact_facts::<F>(
                            cell,
                            blocked,
                            timeout,
                            &exact_search_facts,
                        ))
                    }
                },
            )? {
                // Samples stay private to discovery; original or subset UNSAT must establish coverage.
                if let Some(domain) = domain {
                    propagation_needed |= result.value_facts.mark_domain(cell.clone(), domain);
                }
                if proven_non_unique {
                    non_unique.insert(cell);
                }
                continue;
            }
        }
        let pending: Vec<_> = private_cells
            .iter()
            .filter(|cell| {
                result.value_facts.known_value(cell).is_none()
                    && !non_unique.contains(*cell)
                    && search.cells.get(*cell).is_none_or(|state| state.retryable)
            })
            .cloned()
            .collect();
        if pending.is_empty() {
            break (PrivacyAnalysisStatus::Analyzed, result);
        }
        let first_targets: Vec<_> = pending
            .iter()
            .filter(|cell| !search.cells.contains_key(*cell))
            .cloned()
            .collect();
        let retry = search.retry_candidate(&pending, &options);
        if first_targets.is_empty() && retry.is_none() {
            break (PrivacyAnalysisStatus::SolverUnknown, result);
        }
        if search.total_queries() >= options.max_semantic_queries {
            search.statistics.stop_reason = Some(PrivacySearchStopReason::TotalQueryLimit);
            for cell in &pending {
                limitations
                    .entry(cell.clone())
                    .or_insert(RecoveryLimitation::QueryLimit);
            }
            break (PrivacyAnalysisStatus::QueryLimitReached, result);
        }

        let optional_work = search.statistics.queries_without_progress
            < options.search.max_queries_without_progress;
        // Reserve one attempt for every remaining target before allowing a bridge query.
        let bridge_allowed = optional_work
            && search.statistics.bridge_queries < options.search.max_bridge_queries
            && options.max_semantic_queries - search.total_queries() > first_targets.len();
        let queried = search.cells.keys().cloned().collect();
        let query_cell = if first_targets.is_empty() {
            if !optional_work && retry.is_some() {
                search.statistics.stop_reason = Some(PrivacySearchStopReason::NoProgressLimit);
                break (PrivacyAnalysisStatus::QueryLimitReached, result);
            }
            retry
        } else {
            first_targets
                .iter()
                .find(|cell| result.facts.is_unique(cell))
                .cloned()
                .or_else(|| {
                    choose_query_cell(
                        &problem.expressions,
                        &result.facts,
                        &result.value_facts,
                        &problem.field_modulus,
                        &first_targets,
                        if bridge_allowed {
                            &problem.witness_cells
                        } else {
                            &[]
                        },
                        &queried,
                    )
                })
        };
        let Some(query_cell) = query_cell else {
            break (PrivacyAnalysisStatus::SolverUnknown, result);
        };
        let timeout_ms = if search.cells.contains_key(&query_cell) {
            options.retry_timeout_ms()
        } else {
            options.solver_timeout_ms
        };
        analyzer.set_smt_timeout_ms(timeout_ms)?;
        analyzer.set_ucp_unique_cells(result.facts.unique_cells().iter().cloned());
        //Unchanged structural finite sets already follow from C; retain them in Delta, not as SMT ORs.
        analyzer.set_ucp_value_facts(&smt_query_value_facts(
            &result.value_facts,
            &baseline.value_facts,
        ));
        search.record_query(&query_cell, private_set.contains(&query_cell), timeout_ms);
        let answer = query(&mut analyzer, analyzer_input, &query_cell);
        let answer = match answer {
            Ok(answer) => answer,
            Err(error) => {
                let limitation = limitation_from_solver_error(error)?;
                search.cells.get_mut(&query_cell).unwrap().retryable = true;
                limitations.insert(query_cell, limitation);
                continue;
            }
        };
        match answer.result {
            SemanticQueryResult::ProvenUnique => {
                propagation_needed |= result.facts.mark_unique(query_cell.clone());
                if let Some(value) = answer.value {
                    propagation_needed |= result.value_facts.mark_known(query_cell, value);
                } else {
                    let limitation = match answer.value_unavailable_reason {
                        Some(ValueRecoveryFailure::RepresentationLimit) => {
                            RecoveryLimitation::ValueRepresentationLimit
                        }
                        _ => RecoveryLimitation::NoConcreteValue,
                    };
                    limitations.insert(query_cell, limitation);
                }
            }
            SemanticQueryResult::NotUnique => {
                if private_set.contains(&query_cell) {
                    non_unique.insert(query_cell);
                }
            }
            SemanticQueryResult::Unknown => {
                search.cells.get_mut(&query_cell).unwrap().retryable = true;
                limitations.insert(
                    query_cell,
                    RecoveryLimitation::SolverUnknown { reason: None },
                );
            }
            SemanticQueryResult::Overconstrained => {
                anyhow::bail!("Inferred facts conflict with the initially satisfiable circuit");
            }
        }
    };

    ensure!(
        non_unique
            .iter()
            .all(|cell| result.value_facts.known_value(cell).is_none()
                && !result.facts.is_unique(cell)),
        "Recovered facts contradict original non-uniqueness witnesses"
    );

    let cells = private_cells
        .into_iter()
        .map(|cell| {
            let domain = result.value_facts.domain(&cell).cloned();
            let baseline_domain = baseline.value_facts.domain(&cell).cloned();
            let uniqueness = if result.facts.is_unique(&cell) {
                PrivateCellUniqueness::Unique
            } else if non_unique.contains(&cell) {
                PrivateCellUniqueness::NonUnique
            } else {
                PrivateCellUniqueness::Unknown
            };
            let refined = domain_refined(
                baseline_domain.as_ref(),
                domain.as_ref(),
                &problem.field_modulus,
            );
            let recovery_limitation = if matches!(domain, Some(UcpValueDomain::Exact(_)))
                || uniqueness == PrivateCellUniqueness::NonUnique
            {
                None
            } else {
                limitations.remove(&cell)
            };
            PrivateCellReport {
                query_attempts: search.cells.get(&cell).map_or(0, |state| state.attempts),
                domain_refinement: domain_search.cells.remove(&cell),
                domain_discovery: discovery.cells.remove(&cell),
                cell,
                uniqueness,
                domain,
                baseline_domain,
                domain_refined_from_baseline: refined,
                recovery_limitation,
            }
        })
        .collect();
    let mut report = finish_report(
        status,
        cells,
        public_values,
        search.statistics,
        started.elapsed(),
        Some(result),
        options,
    );
    report.domain_refinement_statistics = domain_search.statistics;
    report.domain_discovery_statistics = discovery.statistics;
    Ok(report)
}

fn smt_query_value_facts(current: &UcpValueFacts, baseline: &UcpValueFacts) -> UcpValueFacts {
    let mut exported = UcpValueFacts::new();
    for (cell, domain) in current.domains() {
        if domain.is_singleton() || baseline.domain(cell) != Some(domain) {
            exported.mark_domain(cell.clone(), domain.clone());
        }
    }
    exported
}

pub(crate) fn limitation_from_solver_error(error: anyhow::Error) -> Result<RecoveryLimitation> {
    if error.downcast_ref::<UnknownSolverResult>().is_none() {
        return Err(error);
    }
    let reason = error
        .downcast_ref::<SolverUnknownDetails>()
        .and_then(|detail| detail.reason.clone());
    Ok(
        if matches!(
            reason.as_deref(),
            Some("TIMEOUT" | crate::smt_solver::process::WALLCLOCK_TIMEOUT_REASON)
        ) {
            RecoveryLimitation::SolverTimeout
        } else {
            RecoveryLimitation::SolverUnknown { reason }
        },
    )
}

pub(crate) fn domain_refined(
    baseline: Option<&UcpValueDomain>,
    current: Option<&UcpValueDomain>,
    modulus: &BigInt,
) -> bool {
    fn field_values(domain: &UcpValueDomain, modulus: &BigInt) -> BTreeSet<BigInt> {
        let values = match domain {
            UcpValueDomain::Exact(value) => vec![value.clone()],
            UcpValueDomain::FiniteSet(values) => values.iter().cloned().collect(),
        };
        values
            .into_iter()
            .map(|value| ((value % modulus) + modulus) % modulus)
            .collect()
    }
    let Some(current) = current else {
        return false;
    };
    let current = field_values(current, modulus);
    match baseline {
        Some(baseline) => {
            let baseline = field_values(baseline, modulus);
            current.len() < baseline.len() && current.is_subset(&baseline)
        }
        None => BigInt::from(current.len()) < *modulus,
    }
}

fn finish_report(
    status: PrivacyAnalysisStatus,
    cells: Vec<PrivateCellReport>,
    public_values: Vec<(CellId, BigInt)>,
    mut search_statistics: PrivacySearchStatistics,
    elapsed: Duration,
    ucp_result: Option<UcpResult>,
    options: PrivacyAnalysisOptions,
) -> PrivacyAnalysisReport {
    let mut summary = PrivacyAnalysisSummary {
        private_cells: cells.len(),
        ..Default::default()
    };
    //Recovery and uniqueness are independent axes; their counts must not be added together.
    for cell in &cells {
        search_statistics.unqueried_targets += usize::from(
            cell.query_attempts == 0
                && cell.domain_refinement.is_none()
                && cell.domain_discovery.is_none()
                && !matches!(cell.domain, Some(UcpValueDomain::Exact(_))),
        );
        match &cell.domain {
            Some(UcpValueDomain::Exact(_)) => summary.exact_values += 1,
            Some(UcpValueDomain::FiniteSet(_)) => summary.finite_domains += 1,
            None => {}
        }
        match cell.uniqueness {
            PrivateCellUniqueness::Unique => summary.unique_cells += 1,
            PrivateCellUniqueness::NonUnique => summary.non_unique_cells += 1,
            PrivateCellUniqueness::Unknown => summary.unresolved_uniqueness += 1,
        }
        summary.refined_domains += usize::from(cell.domain_refined_from_baseline);
    }
    PrivacyAnalysisReport {
        status,
        cells,
        summary,
        public_values,
        semantic_queries: search_statistics.target_queries + search_statistics.bridge_queries,
        search_statistics,
        domain_refinement_statistics: PrivacyDomainRefinementStatistics::default(),
        domain_discovery_statistics: PrivacyDomainDiscoveryStatistics::default(),
        satisfiability_checks: 1,
        elapsed,
        ucp_result,
        options,
    }
}

impl fmt::Display for PrivacyAnalysisReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Privacy analysis: {:?}", self.status)?;
        writeln!(f, "SMT domain export: {}", PRIVACY_SMT_DOMAIN_POLICY)?;
        writeln!(f, "Initial SAT policy: {}", PRIVACY_SAT_HINT_POLICY)?;
        writeln!(f, "Search policy: {}", PRIVACY_SEARCH_POLICY)?;
        writeln!(
            f,
            "Limits: {} semantic queries; solver ms/check and process: {:?}",
            self.options.max_semantic_queries, self.options.solver_timeout_ms
        )?;
        writeln!(f, "Search limits: {:?}", self.options.search)?;
        writeln!(
            f,
            "Finite-domain refinement: {}; limits: {:?}; statistics: {:?}",
            PRIVACY_DOMAIN_REFINEMENT_POLICY,
            self.options.domain_refinement,
            self.domain_refinement_statistics
        )?;
        writeln!(
            f,
            "Domain discovery: {}; limits: {:?}; statistics: {:?}",
            PRIVACY_DOMAIN_DISCOVERY_POLICY,
            self.options.domain_discovery,
            self.domain_discovery_statistics
        )?;
        writeln!(
            f,
            "Targeted exclusion policy: {}",
            PRIVACY_TARGETED_SUBSET_POLICY
        )?;
        writeln!(f, "Search: targets={}; bridges={}; retries={}; propagation runs={}; progress rounds={}; queries since progress={}; unqueried targets={}; stop={:?}",
            self.search_statistics.target_queries, self.search_statistics.bridge_queries,
            self.search_statistics.retry_queries, self.search_statistics.propagation_runs,
            self.search_statistics.progress_rounds,
            self.search_statistics.queries_without_progress, self.search_statistics.unqueried_targets,
            self.search_statistics.stop_reason)?;
        writeln!(f, "Private cells: {}; exact: {}; finite domains: {}; unique: {}; non-unique: {}; unresolved: {}; refined domains: {}",
            self.summary.private_cells, self.summary.exact_values, self.summary.finite_domains,
            self.summary.unique_cells, self.summary.non_unique_cells, self.summary.unresolved_uniqueness,
            self.summary.refined_domains)?;
        writeln!(
            f,
            "Initial SAT checks: {}; SMT uniqueness queries: {}; refinement solver checks: {}; discovery solver checks: {}; elapsed: {:?}",
            self.satisfiability_checks, self.semantic_queries,
            self.domain_refinement_statistics.solver_checks, self.domain_discovery_statistics.solver_checks, self.elapsed
        )?;
        for cell in &self.cells {
            write!(
                f,
                "{}: {:?}; {:?}; attempts: {}; limitation: {:?}; ",
                cell.cell,
                cell.uniqueness,
                cell.recovery_status(),
                cell.query_attempts,
                cell.recovery_limitation
            )?;
            match &cell.domain {
                Some(UcpValueDomain::Exact(value)) => write!(f, "Exact({})", value)?,
                Some(UcpValueDomain::FiniteSet(values)) => write!(f, "Candidates({:?})", values)?,
                None => write!(f, "No recovered domain")?,
            }
            writeln!(
                f,
                "; inferred domain refinement: {}; finite-domain SMT evidence: {:?}; discovery evidence: {:?}",
                cell.domain_refined_from_baseline, cell.domain_refinement, cell.domain_discovery
            )?;
        }
        Ok(())
    }
}

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod tests {
    use super::super::privacy_validation::{
        validate_private_recovery_report, DomainValidationStatus, RecoveryValidationStatus,
    };
    use super::*;
    use crate::io::analyzer_io_type::VerificationInput;
    use std::collections::HashMap;

    const LINEAR: u8 = 0;
    const MASKED: u8 = 1;
    const CANDIDATES: u8 = 2;
    const BOOLEAN: u8 = 3;
    const EXPANDED: u8 = 4;
    const HUGE: u8 = 5;
    const INCONSISTENT: u8 = 6;
    const MIXED: u8 = 7;
    const PUBLISHED: u8 = 8;
    const COPIED_CONSTANT: u8 = 9;
    const NONLINEAR_WITH_AFFINE: u8 = 10;
    const NONLINEAR_INCONSISTENT: u8 = 11;
    const TWO_EXPANDED: u8 = 12;
    const SQUARED_DERIVED: u8 = 13;
    const MANY_EXPANDED: u8 = 14;
    const TWO_BOOLEANS: u8 = 15;

    //Two advice cells suffice to separate recovery, ambiguity and structural ranges.
    #[derive(Clone, Default)]
    struct ExampleCircuit<const CASE: u8> {
        secret: u64,
        nonce: u64,
    }

    #[derive(Clone)]
    struct ExampleConfig {
        secret: Column<Advice>,
        nonce: Column<Advice>,
        selector: Selector,
        published: Option<Column<Instance>>,
    }

    impl<const CASE: u8> Circuit<Fr> for ExampleCircuit<CASE> {
        type Config = ExampleConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let secret = meta.advice_column();
            let nonce = meta.advice_column();
            let selector = meta.selector();
            let public = if matches!(CASE, LINEAR | MASKED | CANDIDATES | MIXED | PUBLISHED) {
                Some(meta.instance_column())
            } else {
                None
            };
            if CASE == PUBLISHED {
                meta.enable_equality(secret);
                meta.enable_equality(public.unwrap());
            }
            if CASE == COPIED_CONSTANT {
                let fixed = meta.fixed_column();
                meta.enable_constant(fixed);
                meta.enable_equality(secret);
            }
            meta.create_gate("private recovery example", |meta| {
                let s = meta.query_advice(secret, Rotation::cur());
                let n = meta.query_advice(nonce, Rotation::cur());
                let q = meta.query_selector(selector);
                let one = Expression::Constant(Fr::from(1));
                let boolean = |value: Expression<Fr>| value.clone() * (value - one.clone());
                let public = public.map(|column| meta.query_instance(column, Rotation::cur()));
                let equations = match CASE {
                    LINEAR => vec![s + Expression::Constant(Fr::from(5)) - public.unwrap()],
                    MASKED => vec![s + n - public.unwrap()],
                    CANDIDATES => vec![
                        //Before observing public=2: secret in {0,1,2}; nonce in {0,1}.
                        s.clone()
                            * (s.clone() - one.clone())
                            * (s.clone() - Expression::Constant(Fr::from(2))),
                        boolean(n.clone()),
                        s + n - public.unwrap(),
                    ],
                    BOOLEAN => vec![boolean(s)],
                    TWO_BOOLEANS => vec![boolean(s), boolean(n)],
                    EXPANDED | MANY_EXPANDED => {
                        vec![s.clone() * s.clone() - Expression::Constant(Fr::from(2)) * s + one]
                    }
                    NONLINEAR_WITH_AFFINE => vec![
                        s.clone() * s.clone() - Expression::Constant(Fr::from(2)) * s + one,
                        n - Expression::Constant(Fr::from(7)),
                    ],
                    NONLINEAR_INCONSISTENT => vec![s.clone() * s.clone(), s - one],
                    TWO_EXPANDED => vec![
                        s.clone() * s.clone() - Expression::Constant(Fr::from(2)) * s + one,
                        n.clone() * n.clone() - Expression::Constant(Fr::from(4)) * n
                            + Expression::Constant(Fr::from(4)),
                    ],
                    SQUARED_DERIVED => vec![
                        s.clone() * s.clone() - Expression::Constant(Fr::from(2)) * s.clone() + one,
                        n - s.clone() * s,
                    ],
                    HUGE => vec![s - Expression::Constant(Fr::from(1_u64 << 63))],
                    INCONSISTENT => vec![s.clone(), s - one],
                    MIXED => vec![
                        s + Expression::Constant(Fr::from(5)) - public.unwrap(),
                        boolean(n),
                    ],
                    PUBLISHED => vec![s - n - Expression::Constant(Fr::from(5))],
                    COPIED_CONSTANT => vec![s - n - Expression::Constant(Fr::from(5))],
                    _ => unreachable!(),
                };
                equations
                    .into_iter()
                    .map(|expr| q.clone() * expr)
                    .collect::<Vec<_>>()
            });
            ExampleConfig {
                secret,
                nonce,
                selector,
                published: if CASE == PUBLISHED { public } else { None },
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> std::result::Result<(), Error> {
            if CASE == MANY_EXPANDED {
                return layouter.assign_region(
                    || "forty independent recoverable private inputs",
                    |mut region| {
                        for row in 0..40 {
                            config.selector.enable(&mut region, row)?;
                            region.assign_advice(
                                || "private input",
                                config.secret,
                                row,
                                || Value::known(Fr::from(1)),
                            )?;
                            region.assign_advice(
                                || "unused queried nonce",
                                config.nonce,
                                row,
                                || Value::known(Fr::from(0)),
                            )?;
                        }
                        Ok(())
                    },
                );
            }
            let published = layouter.assign_region(
                || "private inputs",
                |mut region| {
                    config.selector.enable(&mut region, 0)?;
                    let secret = region.assign_advice(
                        || "secret",
                        config.secret,
                        0,
                        || Value::known(Fr::from(self.secret)),
                    )?;
                    if CASE == COPIED_CONSTANT {
                        region.constrain_constant(secret.cell(), Fr::from(7))?;
                    }
                    region.assign_advice(
                        || "nonce",
                        config.nonce,
                        0,
                        || Value::known(Fr::from(self.nonce)),
                    )?;
                    Ok(secret.cell())
                },
            )?;
            if let Some(column) = config.published {
                layouter.constrain_instance(published, column, 0)?;
            }
            Ok(())
        }
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

    #[test]
    fn temporary_sat_candidate_never_becomes_a_uniqueness_premise() {
        let secret = CellId::advice(0, 0);
        let mut context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<BOOLEAN>::default(),
            4,
            &input(None),
            [secret.clone()],
        )
        .unwrap();
        for (value, expected) in [
            (2, Satisfiability::Unsatisfiable),
            (0, Satisfiability::Satisfiable),
        ] {
            let mut hints = UcpValueFacts::new();
            hints.mark_known(secret.clone(), BigInt::from(value));
            assert_eq!(
                context
                    .analyzer
                    .check_ucp_satisfiability_with_hints(&context.analyzer_input, &hints,)
                    .unwrap(),
                Some(expected)
            );
            assert!(context.analyzer.ucp_value_domains().is_empty());
            assert!(context.analyzer.ucp_unique_variables().is_empty());
            assert_eq!(
                context
                    .analyzer
                    .query_ucp_cell_uniqueness(&context.analyzer_input, &secret,)
                    .unwrap(),
                SemanticQueryResult::NotUnique
            );
        }
    }

    #[test]
    fn rejected_sat_hint_falls_back_to_original_context() {
        let secret = CellId::advice(0, 0);
        let mut context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<BOOLEAN>::default(),
            4,
            &input(None),
            [secret.clone()],
        )
        .unwrap();
        // Deliberately bad candidate: it must not classify the satisfiable boolean circuit as UNSAT.
        context
            .problem
            .initial_value_facts
            .mark_known(secret, BigInt::from(2));
        let (result, checks) = check_privacy_satisfiability(&mut context);
        assert_eq!(result.unwrap(), Satisfiability::Satisfiable);
        assert_eq!(checks, 2);
        assert!(context.analyzer.ucp_value_domains().is_empty());
    }

    #[test]
    fn sat_hint_unknown_allows_fallback_but_execution_errors_remain_errors() {
        assert!(
            !accept_sat_hint(Err(anyhow::anyhow!(UnknownSolverResult).context(
                SolverUnknownDetails {
                    reason: Some("TIMEOUT".into())
                }
            )))
            .unwrap()
        );
        assert!(!accept_sat_hint(Ok(None)).unwrap());
        assert!(!accept_sat_hint(Ok(Some(Satisfiability::Unsatisfiable))).unwrap());
        assert!(accept_sat_hint(Ok(Some(Satisfiability::Satisfiable))).unwrap());
        assert!(accept_sat_hint(Err(anyhow::anyhow!("malformed solver output"))).is_err());
    }

    fn analyze<const CASE: u8>(
        public: Option<i64>,
        targets: Vec<CellId>,
        budget: usize,
    ) -> PrivacyAnalysisReport {
        analyze_private_recoverability::<Fr, _, _>(
            &ExampleCircuit::<CASE>::default(),
            4,
            &input(public),
            targets,
            PrivacyAnalysisOptions {
                max_semantic_queries: budget,
                ..PrivacyAnalysisOptions::default()
            },
        )
        .unwrap()
    }

    #[test]
    fn smt_export_keeps_exact_and_changed_domains_without_mutating_delta() {
        let cells: Vec<_> = (0..4).map(|column| CellId::advice(column, 0)).collect();
        let range = UcpValueDomain::finite_set((0..4).map(BigInt::from)).unwrap();
        let narrowed = UcpValueDomain::finite_set([1, 2].into_iter().map(BigInt::from)).unwrap();
        let new_domain = UcpValueDomain::finite_set([-1, 0].into_iter().map(BigInt::from)).unwrap();
        let mut baseline = UcpValueFacts::new();
        baseline.mark_domain(cells[0].clone(), range.clone());
        baseline.mark_domain(cells[1].clone(), range);
        baseline.mark_known(cells[2].clone(), BigInt::from(7));
        let mut current = baseline.clone();
        current.mark_domain(cells[1].clone(), narrowed.clone());
        current.mark_domain(cells[3].clone(), new_domain.clone());
        let original = current.clone();
        let exported = smt_query_value_facts(&current, &baseline);
        assert!(exported.domain(&cells[0]).is_none());
        assert_eq!(exported.domain(&cells[1]), Some(&narrowed));
        assert_eq!(exported.known_value(&cells[2]), Some(&BigInt::from(7)));
        assert_eq!(exported.domain(&cells[3]), Some(&new_domain));
        assert_eq!(current, original);
        assert_eq!(exported.domains().len(), 3);
    }

    #[test]
    fn skipped_structural_domain_remains_in_the_report_and_is_validated() {
        let secret = CellId::advice(0, 0);
        let circuit = ExampleCircuit::<BOOLEAN>::default();
        let input = input(None);
        let mut context =
            prepare_privacy_analysis::<Fr, _, _>(&circuit, 4, &input, [secret.clone()]).unwrap();
        let initial_check = context
            .analyzer
            .check_ucp_satisfiability(&context.analyzer_input);
        let mut calls = 0;
        let report = analyze_prepared(
            context,
            PrivacyAnalysisOptions::default(),
            Instant::now(),
            initial_check,
            |analyzer, input, cell| {
                calls += 1;
                assert!(analyzer
                    .ucp_value_domains()
                    .iter()
                    .all(|(_, domain)| domain.is_singleton()));
                analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
            },
        )
        .unwrap();
        assert_eq!(calls, 1);
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
        let boolean = UcpValueDomain::finite_set([0, 1].into_iter().map(BigInt::from));
        assert_eq!(report.cells[0].domain, boolean);
        assert_eq!(report.cells[0].baseline_domain, boolean);
        assert!(!report.cells[0].domain_refined_from_baseline);
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
    }

    //Use the real state machine and solver; only the test control overrides the export policy.
    fn range_export_report<const LOOKUP: bool>(
        total: i64,
        full_export: bool,
    ) -> PrivacyAnalysisReport {
        use super::super::{
            external_circuit_tests::observations,
            external_range_tests::{range_private_inputs, RangeAggregateCircuit, RANGE_K},
        };
        let circuit = if total == 15 {
            RangeAggregateCircuit::<LOOKUP>::new(3, 12)
        } else {
            RangeAggregateCircuit::<LOOKUP>::new(7, 9)
        };
        let input = observations(&[total]);
        let mut context = prepare_privacy_analysis::<Fr, _, _>(
            &circuit,
            RANGE_K,
            &input,
            range_private_inputs(&circuit),
        )
        .unwrap();
        let options = PrivacyAnalysisOptions {
            solver_timeout_ms: Some(2_000),
            ..Default::default()
        };
        context
            .analyzer
            .set_smt_timeout_ms(options.solver_timeout_ms)
            .unwrap();
        let mut values = context.problem.initial_value_facts.clone();
        for (cell, value) in &context.public_values {
            values.mark_known(cell.clone(), value.clone());
        }
        let full_values = context
            .problem
            .analyze_with_values(context.problem.initial_facts.clone(), values)
            .value_facts;
        let initial_check = context.analyzer.check_ucp_satisfiability(&input);
        let mut calls = 0;
        let report = analyze_prepared(
            context,
            options,
            Instant::now(),
            initial_check,
            |analyzer, input, cell| {
                calls += 1;
                if full_export {
                    analyzer.set_ucp_value_facts(&full_values);
                } else if total == 15 {
                    assert!(analyzer
                        .ucp_value_domains()
                        .iter()
                        .all(|(_, domain)| domain.is_singleton()));
                } else {
                    let narrowed = UcpValueDomain::finite_set((1..16).map(BigInt::from)).unwrap();
                    assert!(analyzer
                        .ucp_value_domains()
                        .iter()
                        .any(|(_, domain)| domain == &narrowed));
                }
                analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
            },
        )
        .unwrap();
        assert!(calls > 0);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.non_unique_cells, 2);
        assert_eq!(report.summary.finite_domains, 2);
        let expected =
            UcpValueDomain::finite_set((if total == 15 { 0 } else { 1 }..16).map(BigInt::from));
        for cell in &report.cells {
            assert_eq!(cell.domain, expected);
        }
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, RANGE_K, &input, &report)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        report
    }

    #[test]
    fn selective_domain_export_matches_full_export_on_imported_lookup() {
        //Removing redundant ORs may change the solver model, never the reported domains or verdicts.
        let selective = range_export_report::<true>(15, false);
        let full = range_export_report::<true>(15, true);
        assert_eq!(selective.cells, full.cells);
        assert_eq!(selective.summary, full.summary);
        assert_eq!(selective.ucp_result, full.ucp_result);
    }

    #[test]
    fn refined_finite_domains_are_still_exported_to_real_smt_queries() {
        let selective = range_export_report::<true>(16, false);
        let full = range_export_report::<true>(16, true);
        assert_eq!(selective.cells, full.cells);
        assert_eq!(selective.summary.refined_domains, 2);
    }

    #[test]
    fn recovers_selected_secret_and_deduplicates_targets() {
        let secret = CellId::advice(0, 0);
        let report = analyze::<LINEAR>(Some(100), vec![secret.clone(), secret], 32);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.private_cells, 1);
        assert_eq!(report.summary.exact_values, 1);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(95)))
        );
        assert!(report.cells[0].baseline_domain.is_none());
        assert!(report.cells[0].domain_refined_from_baseline);
        assert_eq!(report.semantic_queries, 0);
        assert_eq!(report.satisfiability_checks, 1);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::Recovered
        );
    }

    #[test]
    fn never_copies_secret_assignments_from_the_witness() {
        let circuit = ExampleCircuit::<MASKED> {
            secret: 42,
            nonce: 58,
        };
        let targets = vec![CellId::advice(0, 0), CellId::advice(1, 0)];
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(100)),
            targets.clone(),
            PrivacyAnalysisOptions::default(),
        )
        .unwrap();
        assert_eq!(report.summary.non_unique_cells, 2);
        assert_eq!(report.summary.exact_values, 0);
        assert!(report.cells.iter().all(|cell| cell.domain.is_none()));
        //Even changing the synthesis witness cannot change inferred secret facts.
        let other = analyze_private_recoverability::<Fr, _, _>(
            &ExampleCircuit::<MASKED> {
                secret: 17,
                nonce: 83,
            },
            4,
            &input(Some(100)),
            targets,
            PrivacyAnalysisOptions::default(),
        )
        .unwrap();
        assert_eq!(report.cells, other.cells);
    }

    #[test]
    fn distinguishes_candidate_narrowing_from_exact_recovery() {
        let report = analyze::<CANDIDATES>(Some(2), vec![CellId::advice(0, 0)], 32);
        let cell = &report.cells[0];
        assert_eq!(cell.uniqueness, PrivateCellUniqueness::NonUnique);
        assert_eq!(
            cell.baseline_domain,
            UcpValueDomain::finite_set([0, 1, 2].map(BigInt::from))
        );
        assert_eq!(
            cell.domain,
            UcpValueDomain::finite_set([1, 2].map(BigInt::from))
        );
        assert!(cell.domain_refined_from_baseline);
        assert_eq!(report.summary.exact_values, 0);
        assert_eq!(report.summary.finite_domains, 1);
    }

    #[test]
    fn intrinsic_boolean_range_is_not_reported_as_new_refinement() {
        let report = analyze::<BOOLEAN>(None, vec![CellId::advice(0, 0)], 32);
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
        assert_eq!(report.cells[0].domain, report.cells[0].baseline_domain);
        assert!(!report.cells[0].domain_refined_from_baseline);
    }

    #[test]
    fn smt_proves_exact_value_instead_of_returning_an_arbitrary_model() {
        let report = analyze::<EXPANDED>(None, vec![CellId::advice(0, 0)], 32);
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(1)))
        );
        assert_eq!(report.semantic_queries, 1);
    }

    #[test]
    fn query_budget_exhaustion_is_unknown_not_evidence_of_secrecy() {
        let report = analyze::<EXPANDED>(None, vec![CellId::advice(0, 0)], 0);
        assert_eq!(report.status, PrivacyAnalysisStatus::QueryLimitReached);
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unknown);
        assert!(report.cells[0].domain.is_none());
        assert_eq!(report.semantic_queries, 0);
        assert_eq!(report.satisfiability_checks, 1);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::Unresolved
        );
        assert_eq!(
            report.cells[0].recovery_limitation,
            Some(RecoveryLimitation::QueryLimit)
        );
    }

    #[test]
    fn rejects_vacuous_recovery_from_inconsistent_constraints() {
        let report = analyze::<INCONSISTENT>(None, vec![CellId::advice(0, 0)], 32);
        assert_eq!(report.status, PrivacyAnalysisStatus::Inconsistent);
        assert!(report.ucp_result.is_none());
        assert!(report.cells[0].domain.is_none());
        assert_eq!(report.summary.unique_cells, 0);
        assert_eq!(report.summary.exact_values, 0);
    }

    #[test]
    fn values_beyond_i64_are_recovered_without_a_representation_failure() {
        let report = analyze::<HUGE>(None, vec![CellId::advice(0, 0)], 32);
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(1_u64 << 63)))
        );
        assert_eq!(report.summary.exact_values, 1);
        assert_eq!(report.summary.unique_cells, 1);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::Recovered
        );
        assert_eq!(report.cells[0].recovery_limitation, None);
    }

    #[test]
    fn reports_all_selected_secrets_even_when_some_are_non_unique() {
        let report = analyze::<MIXED>(
            Some(100),
            vec![CellId::advice(0, 0), CellId::advice(1, 0)],
            32,
        );
        assert_eq!(report.summary.exact_values, 1);
        assert_eq!(report.summary.non_unique_cells, 1);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    }

    #[test]
    fn supports_negative_public_field_representatives() {
        let report = analyze::<LINEAR>(Some(-1), vec![CellId::advice(0, 0)], 32);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(-6)))
        );
    }

    #[test]
    fn published_outputs_are_observations_through_instance_bindings() {
        //A public output is the same observation as a public input for recovery.
        let report = analyze::<PUBLISHED>(Some(100), vec![CellId::advice(1, 0)], 32);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(95)))
        );
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
    }

    #[test]
    fn independent_validation_checks_ucp_and_smt_recovered_values() {
        let report = analyze::<LINEAR>(Some(100), vec![CellId::advice(0, 0)], 32);
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<LINEAR>::default(),
            4,
            &input(Some(100)),
            &report,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::VerifiedDomains);
        assert_eq!(checked.domain_queries, 1);
        assert_eq!(checked.cells[0].status, DomainValidationStatus::Entailed);
        let smt_report = analyze::<EXPANDED>(None, vec![CellId::advice(0, 0)], 32);
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            &smt_report,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::VerifiedDomains);
    }

    #[test]
    fn independent_validation_refutes_a_fabricated_exact_value() {
        let mut report = analyze::<LINEAR>(Some(100), vec![CellId::advice(0, 0)], 32);
        //If the validator assumed this Delta fact, the contradiction would falsely pass.
        report.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(0)));
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<LINEAR>::default(),
            4,
            &input(Some(100)),
            &report,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::Refuted);
        assert_eq!(checked.cells[0].counterexample, Some(BigInt::from(95)));
    }

    #[test]
    fn finite_domain_validation_checks_coverage_not_candidate_feasibility() {
        let mut report = analyze::<CANDIDATES>(Some(2), vec![CellId::advice(0, 0)], 32);
        let circuit = ExampleCircuit::<CANDIDATES>::default();
        //0 is infeasible, but the superset {0,1,2} still covers every solution.
        report.cells[0].domain = UcpValueDomain::finite_set([0, 1, 2].map(BigInt::from));
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(2)), &report,)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        //Dropping feasible value 2 must produce a concrete counterexample.
        report.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(1)));
        let checked =
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(2)), &report)
                .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::Refuted);
        assert_eq!(checked.cells[0].counterexample, Some(BigInt::from(2)));
        report.cells[0].domain = Some(UcpValueDomain::FiniteSet(BTreeSet::new()));
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(2)), &report,)
                .unwrap()
                .status,
            RecoveryValidationStatus::Refuted
        );
    }

    #[test]
    fn validation_does_not_assume_other_claims_or_leak_query_scopes() {
        let mut report = analyze::<MIXED>(
            Some(100),
            vec![CellId::advice(0, 0), CellId::advice(1, 0)],
            32,
        );
        report.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(0)));
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<MIXED>::default(),
            4,
            &input(Some(100)),
            &report,
        )
        .unwrap();
        assert_eq!(checked.cells[0].status, DomainValidationStatus::Refuted);
        assert_eq!(checked.cells[1].status, DomainValidationStatus::Entailed);
        assert_eq!(checked.domain_queries, 2);
    }

    #[test]
    fn validation_never_certifies_absent_claims_or_unsatisfiable_contexts() {
        let unknown = analyze::<EXPANDED>(None, vec![CellId::advice(0, 0)], 0);
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            &unknown,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::NoDomainClaims);
        assert_eq!(
            checked.cells[0].status,
            DomainValidationStatus::NoDomainClaim
        );
        let mut impossible = analyze::<INCONSISTENT>(None, vec![CellId::advice(0, 0)], 32);
        impossible.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(5)));
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<INCONSISTENT>::default(),
            4,
            &input(None),
            &impossible,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::Inconsistent);
        assert_eq!(checked.domain_queries, 0);
    }

    #[test]
    fn validation_respects_field_equivalence_and_copy_constants() {
        let mut signed = analyze::<LINEAR>(Some(-1), vec![CellId::advice(0, 0)], 32);
        let field_modulus = super::super::extractor::field_modulus::<Fr>();
        signed.cells[0].domain = Some(UcpValueDomain::exact(field_modulus - BigInt::from(6)));
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(
                &ExampleCircuit::<LINEAR>::default(),
                4,
                &input(Some(-1)),
                &signed,
            )
            .unwrap()
            .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        let mut copied = analyze::<COPIED_CONSTANT>(None, vec![CellId::advice(0, 0)], 32);
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(
                &ExampleCircuit::<COPIED_CONSTANT>::default(),
                4,
                &input(None),
                &copied,
            )
            .unwrap()
            .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        copied.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(8)));
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<COPIED_CONSTANT>::default(),
            4,
            &input(None),
            &copied,
        )
        .unwrap();
        assert_eq!(checked.cells[0].counterexample, Some(BigInt::from(7)));
    }

    #[test]
    fn validation_rejects_changed_public_observations_and_invalid_cells() {
        let mut report = analyze::<LINEAR>(Some(100), vec![CellId::advice(0, 0)], 32);
        let circuit = ExampleCircuit::<LINEAR>::default();
        assert!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(101)), &report)
                .is_err()
        );
        report.cells.push(report.cells[0].clone());
        assert!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(100)), &report)
                .is_err()
        );
        report.cells.pop();
        report.cells[0].cell = CellId::advice(99, 0);
        assert!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(100)), &report)
                .is_err()
        );
    }

    #[test]
    fn validation_keeps_large_counterexamples_without_i64_truncation() {
        let mut report = analyze::<HUGE>(None, vec![CellId::advice(0, 0)], 32);
        report.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(0)));
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<HUGE>::default(),
            4,
            &input(None),
            &report,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::Refuted);
        assert_eq!(
            checked.cells[0].counterexample,
            Some(BigInt::from(1_u64 << 63))
        );
        assert_eq!(checked.solver_checks, 3);
    }

    #[test]
    fn validation_subset_sat_is_not_a_counterexample_to_a_nonlinear_claim() {
        let circuit = ExampleCircuit::<NONLINEAR_WITH_AFFINE>::default();
        let report = analyze::<NONLINEAR_WITH_AFFINE>(None, vec![CellId::advice(0, 0)], 32);
        let validation =
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(None), &report).unwrap();
        // The affine subset only fixes nonce=7; it allows secret!=1, unlike the full quadratic.
        assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
        assert_eq!(validation.subset_checks, 1);
        assert_eq!(validation.solver_checks, 3);
        assert_eq!(validation.cells[0].status, DomainValidationStatus::Entailed);
    }

    #[test]
    fn validation_subset_rejection_uses_an_actual_full_circuit_counterexample() {
        let circuit = ExampleCircuit::<NONLINEAR_WITH_AFFINE>::default();
        let mut report = analyze::<NONLINEAR_WITH_AFFINE>(None, vec![CellId::advice(0, 0)], 32);
        report.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(0)));
        let validation =
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(None), &report).unwrap();
        assert_eq!(validation.status, RecoveryValidationStatus::Refuted);
        assert_eq!(validation.subset_checks, 1);
        assert_eq!(validation.solver_checks, 3);
        assert_eq!(validation.cells[0].counterexample, Some(BigInt::from(1)));
    }

    #[test]
    fn validation_never_accepts_a_subset_proof_without_original_satisfiability() {
        let circuit = ExampleCircuit::<NONLINEAR_INCONSISTENT>::default();
        let report = analyze::<NONLINEAR_WITH_AFFINE>(None, vec![CellId::advice(0, 0)], 32);
        // The affine subset entails secret=1, but the omitted secret^2=0 makes full C inconsistent.
        let validation =
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(None), &report).unwrap();
        assert_eq!(validation.status, RecoveryValidationStatus::Inconsistent);
        assert_eq!(validation.domain_queries, 0);
        assert_eq!(validation.subset_checks, 0);
        assert_eq!(
            validation.cells[0].status,
            DomainValidationStatus::Inconsistent
        );
    }

    #[test]
    fn low_level_validation_rejects_inferred_premises() {
        let public = input(Some(100));
        let circuit = ExampleCircuit::<LINEAR>::default();
        let secret = CellId::advice(0, 0);
        let domain = UcpValueDomain::exact(BigInt::from(0));
        let mut analyzer = Analyzer::<Fr>::new(
            &circuit,
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&public),
        )
        .unwrap();
        let mut inferred = super::super::value::UcpValueFacts::new();
        inferred.mark_known(secret.clone(), BigInt::from(0));
        analyzer.set_ucp_value_facts(&inferred);
        assert!(analyzer
            .query_private_domain_entailment_after_sat(&public, &secret, &domain)
            .is_err());
        assert!(analyzer
            .query_private_domain_entailment(&public, &secret, &domain)
            .is_err());
        analyzer.set_ucp_value_facts(&super::super::value::UcpValueFacts::new());
        analyzer.set_ucp_unique_cells([secret.clone()]);
        assert!(analyzer
            .query_private_domain_entailment_after_sat(&public, &secret, &domain)
            .is_err());
        assert!(analyzer
            .query_private_domain_entailment(&public, &secret, &domain)
            .is_err());
    }

    #[test]
    fn inline_lookup_ranges_support_recovery_on_existing_sample_circuit() {
        use crate::sample_circuits::zcash::bit_decomposition::two_bit_decomp_lookup::TwoBitDecompCircuit;
        let circuit = TwoBitDecompCircuit::<Fr>::default();
        let targets = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(3)),
            targets.clone(),
            PrivacyAnalysisOptions::default(),
        )
        .unwrap();
        assert_eq!(report.summary.exact_values, 2);
        assert_eq!(report.semantic_queries, 0);
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(3)), &report,)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        for cell in &report.cells {
            assert_eq!(
                cell.baseline_domain,
                UcpValueDomain::finite_set([0, 1].map(BigInt::from))
            );
            assert_eq!(cell.domain, Some(UcpValueDomain::exact(BigInt::from(1))));
        }
        //An uninterpreted lookup may admit spurious models, so cannot prove NonUnique here.
        for method in [
            LookupMethod::Uninterpreted,
            LookupMethod::Interpreted,
            LookupMethod::None,
        ] {
            let mut unsupported = input(Some(3));
            unsupported.lookup_method = method;
            let error = analyze_private_recoverability::<Fr, _, _>(
                &circuit,
                4,
                &unsupported,
                targets.clone(),
                PrivacyAnalysisOptions::default(),
            )
            .unwrap_err();
            assert_eq!(
                error.downcast_ref::<UnsupportedPrivacyFeature>(),
                Some(&UnsupportedPrivacyFeature::InlineLookupsRequired)
            );
        }
    }

    fn unknown_error(reason: Option<&str>) -> anyhow::Error {
        anyhow::Error::new(UnknownSolverResult).context(SolverUnknownDetails {
            reason: reason.map(str::to_owned),
        })
    }

    fn search_report<const CASE: u8>(
        targets: Vec<CellId>,
        options: PrivacyAnalysisOptions,
        query: impl FnMut(&mut Analyzer<Fr>, &AnalyzerInput, &CellId) -> Result<SemanticQueryOutput>,
    ) -> PrivacyAnalysisReport {
        let mut context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<CASE>::default(),
            4,
            &input(None),
            targets,
        )
        .unwrap();
        let initial_check = context
            .analyzer
            .check_ucp_satisfiability(&context.analyzer_input);
        analyze_prepared(context, options, Instant::now(), initial_check, query).unwrap()
    }

    #[test]
    fn search_reserves_target_attempt_after_an_unknown_bridge() {
        // s=1 requires SMT; knowing s would propagate n=s*s. Try that useful bridge first.
        let target = CellId::advice(1, 0);
        let mut visited = Vec::new();
        let report = search_report::<SQUARED_DERIVED>(
            vec![target.clone()],
            PrivacyAnalysisOptions {
                max_semantic_queries: 2,
                search: PrivacySearchOptions {
                    max_queries_without_progress: 1,
                    ..Default::default()
                },
                ..Default::default()
            },
            |analyzer, input, cell| {
                visited.push(cell.clone());
                if cell != &target {
                    Err(unknown_error(Some("TIMEOUT")))
                } else {
                    analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
                }
            },
        );
        assert_eq!(visited, [CellId::advice(0, 0), target]);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.semantic_queries, 2);
        assert_eq!(report.search_statistics.bridge_queries, 1);
        assert_eq!(report.search_statistics.target_queries, 1);
        assert_eq!(report.search_statistics.unqueried_targets, 0);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(1.into()))
        );
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(
                &ExampleCircuit::<SQUARED_DERIVED>::default(),
                4,
                &input(None),
                &report,
            )
            .unwrap()
            .status,
            RecoveryValidationStatus::VerifiedDomains
        );
    }

    #[test]
    fn search_excludes_bridges_when_only_reserved_target_budget_remains() {
        let target = CellId::advice(1, 0);
        let report = search_report::<SQUARED_DERIVED>(
            vec![target.clone()],
            PrivacyAnalysisOptions {
                max_semantic_queries: 1,
                ..Default::default()
            },
            |analyzer, input, cell| {
                assert_eq!(cell, &target);
                analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
            },
        );
        assert_eq!(report.summary.exact_values, 1);
        assert_eq!(report.search_statistics.bridge_queries, 0);
        assert_eq!(report.semantic_queries, 1);
    }

    #[test]
    fn uniqueness_without_a_value_restarts_propagation_only_when_new() {
        let secret = CellId::advice(0, 0);
        let target = CellId::advice(1, 0);
        let mut visited = Vec::new();
        let report = search_report::<SQUARED_DERIVED>(
            vec![target.clone()],
            PrivacyAnalysisOptions {
                max_semantic_queries: 2,
                ..Default::default()
            },
            |_, _, cell| {
                visited.push(cell.clone());
                Ok(SemanticQueryResult::ProvenUnique.into())
            },
        );
        assert_eq!(visited, [secret.clone(), target.clone()]);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.search_statistics.propagation_runs, 2);
        assert_eq!(report.search_statistics.progress_rounds, 1);
        assert_eq!(report.semantic_queries, 2);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::UniqueWithoutValue
        );
        let result = report.ucp_result.unwrap();
        assert!(result.facts.is_unique(&secret));
        assert!(result.facts.is_unique(&target));
        assert!(result.all_expressions_unique());
        assert!(result.value_facts.known_value(&target).is_none());
    }

    #[test]
    fn refinement_reuses_exact_ucp_values_of_non_target_cells() {
        let circuit = ExampleCircuit::<MIXED>::default();
        let input = input(Some(100));
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input,
            [CellId::advice(1, 0)],
            PrivacyAnalysisOptions {
                max_semantic_queries: 0,
                solver_timeout_ms: Some(2_000),
                domain_refinement: PrivacyDomainRefinementOptions {
                    max_solver_checks: 3,
                    max_candidates_per_cell: 2,
                },
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.domain_refinement_statistics.solver_checks, 3);
        assert_eq!(report.summary.non_unique_cells, 1);
        assert_eq!(report.search_statistics.propagation_runs, 1);
        let query = std::fs::read_to_string("src/output/private_domain_refinement.smt2").unwrap();
        assert!(query.contains("( = A-0-0 (as ff95 F))"));
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
    }

    #[test]
    fn unchanged_refinements_advance_to_other_cells_without_repeating_propagation() {
        for checks in [4, 6] {
            let report = search_report::<TWO_BOOLEANS>(
                vec![CellId::advice(0, 0), CellId::advice(1, 0)],
                PrivacyAnalysisOptions {
                    max_semantic_queries: 0,
                    solver_timeout_ms: Some(2_000),
                    domain_refinement: PrivacyDomainRefinementOptions {
                        max_solver_checks: checks,
                        max_candidates_per_cell: 2,
                    },
                    ..Default::default()
                },
                |_, _, _| panic!("Refinement must not consume semantic queries"),
            );
            assert_eq!(report.search_statistics.propagation_runs, 1);
            assert_eq!(report.search_statistics.progress_rounds, 0);
            assert_eq!(report.domain_refinement_statistics.attempted_cells, 2);
            assert_eq!(report.domain_refinement_statistics.solver_checks, checks);
            assert_eq!(report.semantic_queries, 0);
            assert_eq!(
                report.summary.non_unique_cells,
                if checks == 6 { 2 } else { 1 }
            );
            assert_eq!(
                report.status,
                if checks == 6 {
                    PrivacyAnalysisStatus::Analyzed
                } else {
                    PrivacyAnalysisStatus::QueryLimitReached
                }
            );
            for cell in &report.cells {
                assert_eq!(
                    cell.domain,
                    UcpValueDomain::finite_set([0.into(), 1.into()])
                );
                assert!(cell.domain_refinement.is_some());
            }
        }
    }

    #[test]
    fn search_progress_renews_optional_budget_but_never_total_count() {
        let targets = vec![CellId::advice(0, 0), CellId::advice(1, 0)];
        for (hard_limit, expected, queries) in [
            (1, PrivacyAnalysisStatus::QueryLimitReached, 1),
            (2, PrivacyAnalysisStatus::Analyzed, 2),
        ] {
            let report = search_report::<TWO_EXPANDED>(
                targets.clone(),
                PrivacyAnalysisOptions {
                    max_semantic_queries: hard_limit,
                    search: PrivacySearchOptions {
                        max_queries_without_progress: 1,
                        ..Default::default()
                    },
                    ..Default::default()
                },
                |analyzer, input, cell| analyzer.query_ucp_cell_uniqueness_with_value(input, cell),
            );
            assert_eq!(report.status, expected);
            assert_eq!(report.semantic_queries, queries);
            assert_eq!(report.search_statistics.target_queries, queries);
            assert_eq!(report.search_statistics.progress_rounds, queries);
            assert_eq!(report.search_statistics.propagation_runs, queries + 1);
            assert_eq!(report.search_statistics.queries_without_progress, 0);
            assert_eq!(report.summary.exact_values, queries);
            assert_eq!(report.search_statistics.unqueried_targets, 2 - queries);
            if hard_limit == 1 {
                assert_eq!(
                    report.search_statistics.stop_reason,
                    Some(PrivacySearchStopReason::TotalQueryLimit)
                );
            }
        }
    }

    #[test]
    fn search_retries_unknown_target_after_other_target_progress() {
        // Both values are easy for SMT, but are not factorized by UCP. Inject one timeout.
        let secret = CellId::advice(0, 0);
        let nonce = CellId::advice(1, 0);
        let mut visited = Vec::new();
        let report = search_report::<TWO_EXPANDED>(
            vec![secret.clone(), nonce.clone()],
            PrivacyAnalysisOptions::default(),
            |analyzer, input, cell| {
                visited.push(cell.clone());
                if visited.len() == 1 {
                    Err(unknown_error(Some("TIMEOUT")))
                } else {
                    analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
                }
            },
        );
        assert_eq!(visited, [secret, nonce, CellId::advice(0, 0)]);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.exact_values, 2);
        assert_eq!(report.semantic_queries, 3);
        assert_eq!(report.search_statistics.retry_queries, 1);
        assert_eq!(report.search_statistics.propagation_runs, 3);
        assert_eq!(report.cells[0].query_attempts, 2);
        assert!(report
            .cells
            .iter()
            .all(|cell| cell.recovery_limitation.is_none()));
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(
                &ExampleCircuit::<TWO_EXPANDED>::default(),
                4,
                &input(None),
                &report,
            )
            .unwrap()
            .status,
            RecoveryValidationStatus::VerifiedDomains
        );
    }

    #[test]
    fn search_retries_with_larger_timeout_without_assuming_the_candidate() {
        let mut timeouts = Vec::new();
        let report = search_report::<EXPANDED>(
            vec![CellId::advice(0, 0)],
            PrivacyAnalysisOptions {
                solver_timeout_ms: Some(1_000),
                search: PrivacySearchOptions {
                    retry_solver_timeout_ms: Some(2_000),
                    ..Default::default()
                },
                ..Default::default()
            },
            |analyzer, input, cell| {
                timeouts.push(analyzer.smt_timeout_ms());
                assert!(analyzer.ucp_value_domains().is_empty());
                if timeouts.len() == 1 {
                    Err(unknown_error(Some("TIMEOUT")))
                } else {
                    analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
                }
            },
        );
        assert_eq!(timeouts, [Some(1_000), Some(2_000)]);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.exact_values, 1);
        assert_eq!(report.search_statistics.retry_queries, 1);
        assert_eq!(report.cells[0].query_attempts, 2);
    }

    #[test]
    fn search_no_progress_does_not_loop_or_repeat_a_decisive_result() {
        for result in [SemanticQueryResult::Unknown, SemanticQueryResult::NotUnique] {
            let report = search_report::<BOOLEAN>(
                vec![CellId::advice(0, 0)],
                PrivacyAnalysisOptions {
                    solver_timeout_ms: Some(1_000),
                    search: PrivacySearchOptions {
                        max_retries_per_target: 100,
                        retry_solver_timeout_ms: Some(2_000),
                        ..Default::default()
                    },
                    ..Default::default()
                },
                |_, _, _| Ok(result.into()),
            );
            // The larger budget permits only one retry; no new progress means no third attempt.
            let queries = if result == SemanticQueryResult::Unknown {
                2
            } else {
                1
            };
            assert_eq!(report.semantic_queries, queries);
            assert_eq!(report.cells[0].query_attempts, queries);
            assert_eq!(report.search_statistics.propagation_runs, 1);
            assert_eq!(
                report.status,
                if result == SemanticQueryResult::Unknown {
                    PrivacyAnalysisStatus::SolverUnknown
                } else {
                    PrivacyAnalysisStatus::Analyzed
                }
            );
        }
    }

    #[test]
    fn search_stagnation_limit_preserves_unknown_without_skipping_first_targets() {
        let report = search_report::<TWO_EXPANDED>(
            vec![CellId::advice(0, 0), CellId::advice(1, 0)],
            PrivacyAnalysisOptions {
                solver_timeout_ms: Some(1_000),
                search: PrivacySearchOptions {
                    max_queries_without_progress: 0,
                    ..Default::default()
                },
                ..Default::default()
            },
            |_, _, _| Err(unknown_error(Some("TIMEOUT"))),
        );
        assert_eq!(report.semantic_queries, 2);
        assert_eq!(report.search_statistics.propagation_runs, 1);
        assert_eq!(report.search_statistics.unqueried_targets, 0);
        assert_eq!(
            report.search_statistics.stop_reason,
            Some(PrivacySearchStopReason::NoProgressLimit)
        );
        assert_eq!(report.status, PrivacyAnalysisStatus::QueryLimitReached);
        assert!(report.cells.iter().all(|cell| cell.query_attempts == 1
            && cell.domain.is_none()
            && cell.uniqueness == PrivateCellUniqueness::Unknown));
    }

    #[test]
    fn search_detects_actual_domain_progress_not_repeated_or_equivalent_facts() {
        let context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<MASKED>::default(),
            4,
            &input(Some(10)),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        let facts = context.problem.initial_facts.clone();
        let mut values = UcpValueFacts::new();
        let cell = CellId::advice(0, 0);
        let mut state = RecoverySearchState::new(&facts, &values);
        state.statistics.queries_without_progress = 3;
        values.mark_domain(
            cell.clone(),
            UcpValueDomain::finite_set([0.into(), 1.into()]).unwrap(),
        );
        let first = context
            .problem
            .analyze_with_values(facts.clone(), values.clone());
        state.observe_progress(&first, &context.problem.field_modulus);
        assert_eq!(state.statistics.queries_without_progress, 0);
        state.statistics.queries_without_progress = 2;
        state.observe_progress(&first, &context.problem.field_modulus);
        assert_eq!(state.statistics.queries_without_progress, 2);
        values.mark_known(cell.clone(), 1.into());
        let mut exact = context.problem.analyze_with_values(facts, values);
        state.observe_progress(&exact, &context.problem.field_modulus);
        assert_eq!(state.statistics.progress_rounds, 2);
        state.statistics.queries_without_progress = 1;
        exact.value_facts = UcpValueFacts::new();
        exact
            .value_facts
            .mark_known(cell, &context.problem.field_modulus + 1);
        state.observe_progress(&exact, &context.problem.field_modulus);
        assert_eq!(state.statistics.progress_rounds, 2);
        assert_eq!(state.statistics.queries_without_progress, 1);
    }

    #[test]
    fn search_zero_retry_budget_is_rejected_before_synthesis() {
        let error = analyze_private_recoverability::<Fr, _, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            [CellId::advice(0, 0)],
            PrivacyAnalysisOptions {
                search: PrivacySearchOptions {
                    retry_solver_timeout_ms: Some(0),
                    ..Default::default()
                },
                ..Default::default()
            },
        )
        .unwrap_err();
        assert!(error.to_string().contains("Retry solver timeout"));
        assert_eq!(PrivacyAnalysisOptions::default().max_semantic_queries, 256);
        assert_eq!(PrivacyAnalysisOptions::default().retry_timeout_ms(), None);
    }

    #[test]
    fn search_default_budget_recovers_more_than_thirty_two_private_inputs() {
        let circuit = ExampleCircuit::<MANY_EXPANDED>::default();
        MockProver::run(6, &circuit, vec![])
            .unwrap()
            .assert_satisfied();
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            6,
            &input(None),
            (0..40).map(|row| CellId::advice(0, row)),
            PrivacyAnalysisOptions::default(),
        )
        .unwrap();
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.exact_values, 40);
        assert_eq!(report.semantic_queries, 40);
        assert_eq!(report.search_statistics.target_queries, 40);
        assert_eq!(report.search_statistics.unqueried_targets, 0);
        assert!(report
            .cells
            .iter()
            .all(|cell| cell.query_attempts == 1
                && cell.domain == Some(UcpValueDomain::exact(1.into()))));
    }

    #[test]
    fn explicit_solver_budget_is_instance_local_and_recorded() {
        let circuit = ExampleCircuit::<LINEAR>::default();
        let options = PrivacyAnalysisOptions {
            solver_timeout_ms: Some(10_000),
            ..Default::default()
        };
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(100)),
            [CellId::advice(0, 0)],
            options,
        )
        .unwrap();
        assert_eq!(report.options, options);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::Recovered
        );
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(100)), &report)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        let mut first = prepare_privacy_analysis::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(100)),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        let second = prepare_privacy_analysis::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(100)),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        first.analyzer.set_smt_timeout_ms(Some(123)).unwrap();
        assert_eq!(first.analyzer.smt_timeout_ms(), Some(123));
        assert_eq!(second.analyzer.smt_timeout_ms(), None);
        assert!(first.analyzer.set_smt_timeout_ms(Some(0)).is_err());
        assert_eq!(first.analyzer.smt_timeout_ms(), Some(123));
    }

    #[test]
    fn initial_unknown_never_exports_vacuous_ucp_facts() {
        for (reason, expected) in [
            (Some("TIMEOUT"), RecoveryLimitation::SolverTimeout),
            (
                Some(crate::smt_solver::process::WALLCLOCK_TIMEOUT_REASON),
                RecoveryLimitation::SolverTimeout,
            ),
            (
                Some("RESOURCEOUT"),
                RecoveryLimitation::SolverUnknown {
                    reason: Some("RESOURCEOUT".into()),
                },
            ),
            (None, RecoveryLimitation::SolverUnknown { reason: None }),
        ] {
            let context = prepare_privacy_analysis::<Fr, _, _>(
                &ExampleCircuit::<LINEAR>::default(),
                4,
                &input(Some(100)),
                [CellId::advice(0, 0)],
            )
            .unwrap();
            let report = analyze_prepared(
                context,
                PrivacyAnalysisOptions {
                    domain_discovery: PrivacyDomainDiscoveryOptions {
                        max_solver_checks: 3,
                        max_values_per_cell: 2,
                        ..Default::default()
                    },
                    domain_refinement: PrivacyDomainRefinementOptions {
                        max_solver_checks: 3,
                        max_candidates_per_cell: 2,
                    },
                    ..Default::default()
                },
                Instant::now(),
                Err(unknown_error(reason)),
                |_, _, _| panic!("No cell queries before SAT proof"),
            )
            .unwrap();
            assert_eq!(report.status, PrivacyAnalysisStatus::SolverUnknown);
            assert!(report.ucp_result.is_none());
            assert_eq!(report.summary.exact_values, 0);
            assert_eq!(report.semantic_queries, 0);
            assert_eq!(report.domain_discovery_statistics.solver_checks, 0);
            assert_eq!(report.domain_refinement_statistics.solver_checks, 0);
            assert!(report.cells[0].domain_discovery.is_none());
            assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unknown);
            assert_eq!(
                report.cells[0].recovery_status(),
                PrivateRecoveryStatus::Unresolved
            );
            assert_eq!(report.cells[0].recovery_limitation, Some(expected));
        }
    }

    #[test]
    fn semantic_timeout_preserves_recovery_of_other_cells() {
        let circuit = ExampleCircuit::<MIXED>::default();
        let context = prepare_privacy_analysis::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(100)),
            [CellId::advice(0, 0), CellId::advice(1, 0)],
        )
        .unwrap();
        let report = analyze_prepared(
            context,
            PrivacyAnalysisOptions::default(),
            Instant::now(),
            Ok(Satisfiability::Satisfiable),
            |_, _, _| Err(unknown_error(Some("TIMEOUT"))),
        )
        .unwrap();
        assert_eq!(report.status, PrivacyAnalysisStatus::SolverUnknown);
        assert_eq!(report.semantic_queries, 1);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(95)))
        );
        assert_eq!(report.cells[0].recovery_limitation, None);
        assert_eq!(
            report.cells[1].recovery_status(),
            PrivateRecoveryStatus::Unresolved
        );
        assert_eq!(
            report.cells[1].recovery_limitation,
            Some(RecoveryLimitation::SolverTimeout)
        );
        assert_eq!(report.cells[1].uniqueness, PrivateCellUniqueness::Unknown);
    }

    #[test]
    fn timeout_does_not_erase_prior_uniqueness_or_invent_a_representation_failure() {
        let mut context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        //A valid uniqueness premise for (s-1)^2=0, without supplying its numeric value.
        context
            .problem
            .initial_facts
            .mark_unique(CellId::advice(0, 0));
        let report = analyze_prepared(
            context,
            PrivacyAnalysisOptions::default(),
            Instant::now(),
            Ok(Satisfiability::Satisfiable),
            |_, _, _| Err(unknown_error(Some("TIMEOUT"))),
        )
        .unwrap();
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::UniqueWithoutValue
        );
        assert_eq!(
            report.cells[0].recovery_limitation,
            Some(RecoveryLimitation::SolverTimeout)
        );
        assert!(report.cells[0].domain.is_none());
    }

    #[test]
    fn query_limit_keeps_structurally_unique_cells_distinct_from_recovered_values() {
        let mut context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        context
            .problem
            .initial_facts
            .mark_unique(CellId::advice(0, 0));
        let report = analyze_prepared(
            context,
            PrivacyAnalysisOptions {
                max_semantic_queries: 0,
                ..PrivacyAnalysisOptions::default()
            },
            Instant::now(),
            Ok(Satisfiability::Satisfiable),
            |_, _, _| panic!("Zero query quota must not call SMT"),
        )
        .unwrap();
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::UniqueWithoutValue
        );
        //No model was requested: do not guess that it exceeded the representation limit.
        assert_eq!(
            report.cells[0].recovery_limitation,
            Some(RecoveryLimitation::QueryLimit)
        );
    }

    #[test]
    fn malformed_solver_output_is_an_error_not_an_unknown_report() {
        assert!(limitation_from_solver_error(anyhow::anyhow!("invalid solver response")).is_err());
        let context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        assert!(analyze_prepared(
            context,
            PrivacyAnalysisOptions::default(),
            Instant::now(),
            Ok(Satisfiability::Satisfiable),
            |_, _, _| Err(anyhow::anyhow!("invalid solver response")),
        )
        .is_err());
    }

    #[test]
    fn non_unique_status_can_still_have_a_finite_candidate_domain() {
        let report = analyze::<CANDIDATES>(Some(2), vec![CellId::advice(0, 0)], 32);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::NonUnique
        );
        assert!(matches!(
            report.cells[0].domain,
            Some(UcpValueDomain::FiniteSet(_))
        ));
        assert_eq!(report.cells[0].recovery_limitation, None);
    }

    #[test]
    fn zero_solver_budget_is_rejected_before_synthesis() {
        assert!(analyze_private_recoverability::<Fr, _, _>(
            &ExampleCircuit::<LINEAR>::default(),
            4,
            &input(Some(100)),
            [CellId::advice(0, 0)],
            PrivacyAnalysisOptions {
                solver_timeout_ms: Some(0),
                ..Default::default()
            },
        )
        .is_err());
    }

    #[test]
    fn validates_private_selection_and_public_observation_boundary() {
        let circuit = ExampleCircuit::<LINEAR>::default();
        for targets in [
            vec![],
            vec![CellId::instance(0, 0)],
            vec![CellId::fixed(0, 0)],
            vec![CellId::advice(99, 0)],
        ] {
            assert!(analyze_private_recoverability::<Fr, _, _>(
                &circuit,
                4,
                &input(Some(100)),
                targets,
                PrivacyAnalysisOptions::default(),
            )
            .is_err());
        }
        let mut private_seed = input(Some(100));
        private_seed
            .verification_input
            .instance_cells
            .insert("A-0-0".into(), 95.into());
        assert!(analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &private_seed,
            [CellId::advice(0, 0)],
            PrivacyAnalysisOptions::default(),
        )
        .is_err());
        let mut random = input(Some(100));
        random.verification_method = VerificationMethod::Random;
        assert!(analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &random,
            [CellId::advice(0, 0)],
            PrivacyAnalysisOptions::default(),
        )
        .is_err());
        assert!(analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input(None),
            [CellId::advice(0, 0)],
            PrivacyAnalysisOptions::default(),
        )
        .is_err());
    }
}
