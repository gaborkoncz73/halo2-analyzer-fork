#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

//! Keresési állapot, újrapróbálkozás és közös cella/művelet-választás.
//! Az ütemezés nem indít solverhívást. A heurisztikus szimuláció nem bizonyíték.
use super::{
    cell::CellId,
    choose_var::choose_query_cell,
    engine::UcpResult,
    extractor::UcpProblem,
    facts::UcpFacts,
    privacy::{
        domain_refined, PrivacyAnalysisOptions, PrivacyAnalysisStatus, PrivacySearchStatistics,
        PrivacySearchStopReason,
    },
    privacy_discovery::{DomainDiscoveryState, PrivateDomainDiscoveryStatus},
    privacy_domain::refinement_has_target_gain,
    privacy_domain::DomainRefinementState,
    value::{normalize_field_value, UcpValueDomain, UcpValueFacts},
};
use anyhow::{ensure, Context, Result};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet, HashSet};

// Csak valódi K/Delta-előrelépéskor vált keresési generációt; a teljes kereteket nem nullázza.
#[derive(Default)]
pub(super) struct CellQueryState {
    pub(super) attempts: usize,
    generation: usize,
    timeout_ms: Option<u64>,
    pub(super) retryable: bool,
}

pub(super) struct RecoverySearchState {
    pub(super) statistics: PrivacySearchStatistics,
    pub(super) cells: BTreeMap<CellId, CellQueryState>,
    previous_facts: UcpFacts,
    previous_values: UcpValueFacts,
    pub(super) generation: usize,
}

impl RecoverySearchState {
    pub(super) fn initialize_search(facts: &UcpFacts, values: &UcpValueFacts) -> Self {
        Self {
            statistics: PrivacySearchStatistics::default(),
            cells: BTreeMap::new(),
            previous_facts: facts.clone(),
            previous_values: values.clone(),
            generation: 0,
        }
    }

    // Csak új egyértelműség vagy valódi domainszűkülés esetén nyit új keresési generációt.
    // Pusztán új mintától vagy teljességi jelöléstől nem nullázza a stagnálási számlálót.
    pub(super) fn observe_progress(&mut self, result: &UcpResult, modulus: &BigInt) {
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

    pub(super) fn total_queries(&self) -> usize {
        self.statistics.target_queries + self.statistics.bridge_queries
    }

    // Egy szemantikai próbát számol; ez nem az alatta végzett solverhívások száma.
    pub(super) fn record_query(&mut self, cell: &CellId, is_target: bool, timeout_ms: Option<u64>) {
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

    // Csak bizonytalan eredmény próbálható újra, új tudás vagy nagyobb időkeret mellett.
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

// Query esetén engedélyezett próbát javasol; Stop esetén a leállási okot és az érintett célokat adja.
pub(super) enum ProbePlan {
    Query(CellId),
    Stop(
        PrivacyAnalysisStatus,
        Option<PrivacySearchStopReason>,
        Vec<CellId>,
    ),
}

// Előbb az első célcellapróbákra foglal keretet, és csak a maradékból enged köztes cellavizsgálatot.
fn plan_fast_probe(
    private_cells: &[CellId],
    non_unique: &HashSet<CellId>,
    problem: &UcpProblem,
    result: &UcpResult,
    search: &RecoverySearchState,
    options: &PrivacyAnalysisOptions,
) -> ProbePlan {
    let pending: Vec<_> = private_cells
        .iter()
        .filter(|cell| {
            !result.value_facts.domain_is_complete(cell)
                && !non_unique.contains(*cell)
                && search.cells.get(*cell).is_none_or(|state| state.retryable)
        })
        .cloned()
        .collect();
    if pending.is_empty() {
        return ProbePlan::Stop(PrivacyAnalysisStatus::Analyzed, None, pending);
    }
    let first_targets: Vec<_> = pending
        .iter()
        .filter(|cell| !search.cells.contains_key(*cell))
        .cloned()
        .collect();
    let retry = search.retry_candidate(&pending, options);
    if first_targets.is_empty() && retry.is_none() {
        return ProbePlan::Stop(PrivacyAnalysisStatus::SolverUnknown, None, pending);
    }
    if search.total_queries() >= options.max_semantic_queries {
        return ProbePlan::Stop(
            PrivacyAnalysisStatus::QueryLimitReached,
            Some(PrivacySearchStopReason::TotalQueryLimit),
            pending,
        );
    }
    let optional_work =
        search.statistics.queries_without_progress < options.search.max_queries_without_progress;
    let bridge_allowed = optional_work
        && search.statistics.bridge_queries + search.statistics.bridge_domain_checks
            < options.search.max_bridge_queries
        && options.max_semantic_queries - search.total_queries() > first_targets.len();
    let queried = search
        .cells
        .keys()
        .chain(non_unique.iter())
        .chain(
            result
                .value_facts
                .domains()
                .keys()
                .filter(|cell| result.value_facts.domain_is_complete(cell)),
        )
        .cloned()
        .collect();
    let cell = if first_targets.is_empty() {
        if !optional_work && retry.is_some() {
            return ProbePlan::Stop(
                PrivacyAnalysisStatus::QueryLimitReached,
                Some(PrivacySearchStopReason::NoProgressLimit),
                pending,
            );
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
    match cell {
        Some(cell) => ProbePlan::Query(cell),
        None => ProbePlan::Stop(PrivacyAnalysisStatus::SolverUnknown, None, pending),
    }
}

// A shortlist az engedélyezett lehetőségeket gyűjti össze; a choose_action rangsorolja őket.
// A ProbePlan eredményben leállási információt is adhat, de itt még nem indít solverhívást.
#[allow(clippy::too_many_arguments)]
pub(super) fn shortlist_actions(
    problem: &UcpProblem,
    private_cells: &[CellId],
    snapshot_cells: &[CellId],
    private_set: &HashSet<CellId>,
    result: &UcpResult,
    search: &RecoverySearchState,
    domain_search: &mut DomainRefinementState,
    discovery: &mut DomainDiscoveryState,
    evidence: &RecoveryEvidence,
    non_unique: &HashSet<CellId>,
    original_available: bool,
    options: &PrivacyAnalysisOptions,
) -> Result<(Vec<RecoveryAction>, ProbePlan)> {
    let _profile = super::profiling::scope("scheduler.shortlist");
    domain_search.observe_progress(search.generation);
    let probe_plan = plan_fast_probe(private_cells, non_unique, problem, result, search, options);
    let bridge_left = options
        .search
        .max_bridge_queries
        .saturating_sub(search.statistics.bridge_queries + search.statistics.bridge_domain_checks);
    let needs_help = private_cells.iter().any(|cell| {
        !result.value_facts.domain_is_complete(cell)
            && (result.value_facts.domain(cell).is_none() || !non_unique.contains(cell))
    });
    let optional_bridge = needs_help
        && bridge_left > 0
        && search.statistics.queries_without_progress < options.search.max_queries_without_progress;
    let mut actions = Vec::new();
    if original_available {
        // A más műveletekből származó mintákkal teljessé tett domaineket is kihagyja az új vizsgálatból.
        let refinement_targets: Vec<_> = private_cells
            .iter()
            .filter(|cell| {
                !result.value_facts.domain_is_complete(cell)
                    && discovery.cells.get(*cell).is_none_or(|evidence| {
                        evidence.status != PrivateDomainDiscoveryStatus::Complete
                    })
            })
            .cloned()
            .collect();
        if let Some(cell) = domain_search.choose_cell(&refinement_targets, problem, result)? {
            actions.push(RecoveryAction::Refine(cell, RecoveryStrategy::DomainSearch));
        }
        for cell in private_cells {
            if result.value_facts.domain(cell).is_none() {
                discovery.remember_samples(cell, &evidence.samples(cell));
            }
        }
        if let Some(cell) = discovery.choose_cell(
            private_cells,
            &problem.expressions,
            result,
            &problem.field_modulus,
            options.solver_timeout_ms,
        ) {
            actions.push(RecoveryAction::Discover(
                cell,
                RecoveryStrategy::DomainSearch,
            ));
        }
        if optional_bridge {
            let reserved_refinement = refinement_targets
                .iter()
                .filter(|cell| {
                    matches!(
                        result.value_facts.domain(cell),
                        Some(UcpValueDomain::FiniteSet(_))
                    ) && !domain_search.cells.contains_key(*cell)
                })
                .count();
            let remaining_refinement = options
                .domain_refinement
                .max_solver_checks
                .saturating_sub(domain_search.statistics.solver_checks)
                .saturating_sub(reserved_refinement);
            let bridges: Vec<_> = snapshot_cells
                .iter()
                .filter(|cell| !private_set.contains(*cell))
                .filter(|cell| !result.value_facts.domain_is_complete(cell))
                .cloned()
                .collect();
            let finite_bridges: Vec<_> = bridges
                .iter()
                .filter(|cell| {
                    if let Some(UcpValueDomain::FiniteSet(values)) = result.value_facts.domain(cell)
                    {
                        values.len() + 1 <= bridge_left.min(remaining_refinement)
                    } else {
                        false
                    }
                })
                .cloned()
                .collect();
            if let Some(cell) = domain_search.choose_cell(&finite_bridges, problem, result)? {
                if bridge_has_gain(&cell, private_cells, problem, result)? {
                    actions.push(RecoveryAction::Refine(cell, RecoveryStrategy::DomainSearch));
                }
            }
            let reserved_discovery = private_cells
                .iter()
                .filter(|cell| {
                    result.value_facts.domain(cell).is_none()
                        && discovery
                            .cells
                            .get(*cell)
                            .is_none_or(|entry| entry.solver_checks == 0)
                })
                .count();
            if options
                .domain_discovery
                .max_solver_checks
                .saturating_sub(discovery.statistics.solver_checks)
                > reserved_discovery
            {
                for cell in &bridges {
                    if result.value_facts.domain(cell).is_none() {
                        discovery.remember_samples(cell, &evidence.samples(cell));
                    }
                }
                if let Some(cell) = discovery.choose_cell(
                    &bridges,
                    &problem.expressions,
                    result,
                    &problem.field_modulus,
                    options.solver_timeout_ms,
                ) {
                    if bridge_has_gain(&cell, private_cells, problem, result)? {
                        actions.push(RecoveryAction::Discover(
                            cell,
                            RecoveryStrategy::DomainSearch,
                        ));
                    }
                }
            }
        }
    }
    if let ProbePlan::Query(cell) = &probe_plan {
        let discovery_available = discovery.can_discover(cell, result, options.solver_timeout_ms)
            && actions.iter().any(|action| {
                matches!(
                    action,
                    RecoveryAction::Discover(_, RecoveryStrategy::DomainSearch)
                )
            });
        integrate_fast_probe(
            &mut actions,
            cell,
            problem,
            result,
            evidence,
            discovery_available,
        );
    }
    Ok((actions, probe_plan))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RecoveryAction {
    Refine(CellId, RecoveryStrategy),
    Discover(CellId, RecoveryStrategy),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RecoveryStrategy {
    DomainSearch,
    FastProbe,
}

impl RecoveryAction {
    pub fn cell(&self) -> &CellId {
        match self {
            Self::Refine(cell, _) | Self::Discover(cell, _) => cell,
        }
    }

    pub fn strategy(&self) -> RecoveryStrategy {
        match self {
            Self::Refine(_, strategy) | Self::Discover(_, strategy) => *strategy,
        }
    }
}

#[derive(Default)]
pub(crate) struct RecoveryEvidence {
    feasible: BTreeMap<CellId, BTreeSet<BigInt>>,
}

impl RecoveryEvidence {
    pub fn samples(&self, cell: &CellId) -> BTreeSet<BigInt> {
        self.feasible.get(cell).cloned().unwrap_or_default()
    }

    pub fn remember_feasible_samples(
        &mut self,
        cell: &CellId,
        samples: impl IntoIterator<Item = BigInt>,
        modulus: &BigInt,
    ) -> Result<()> {
        for sample in samples {
            let value =
                normalize_field_value(sample, modulus).context("Unsupported recovery sample")?;
            self.feasible.entry(cell.clone()).or_default().insert(value);
        }
        Ok(())
    }

    /// Csak a teljességi jelölést frissítve nem kér új UCP-kört.
    /// Ha a testbeli azonosítás több jelöltet egyetlen értékre von össze, új propagációt kér.
    pub fn certify_complete_domains(
        &self,
        knowledge: &mut UcpResult,
        modulus: &BigInt,
    ) -> Result<bool> {
        let mut exact_added = false;
        for (cell, samples) in &self.feasible {
            ensure!(
                samples.len() < 2 || !knowledge.facts.is_unique(cell),
                "Uniqueness contradicts feasible samples for {}",
                cell
            );
            let was_exact = knowledge.value_facts.known_value(cell).is_some();
            knowledge
                .value_facts
                .mark_complete_from_samples(cell, samples, modulus)?;
            exact_added |= !was_exact && knowledge.value_facts.known_value(cell).is_some();
        }
        Ok(exact_added)
    }
}

fn refinement_cost(
    cell: &CellId,
    problem: &UcpProblem,
    result: &UcpResult,
    evidence: &RecoveryEvidence,
) -> usize {
    match result.value_facts.domain(cell) {
        Some(UcpValueDomain::FiniteSet(values)) => {
            let candidates: BTreeSet<_> = values
                .iter()
                .filter_map(|value| normalize_field_value(value.clone(), &problem.field_modulus))
                .collect();
            1 + candidates.difference(&evidence.samples(cell)).count()
        }
        _ => usize::MAX / 2,
    }
}

/// A hívóval ellenőrizteti a próba keretét, újrapróbálhatóságát és a célokra fenntartott keretet.
/// A Refine stratégiát választ; a Discover az elérhető értékfelsorolást részesíti előnyben.
pub(crate) fn integrate_fast_probe(
    actions: &mut Vec<RecoveryAction>,
    cell: &CellId,
    problem: &UcpProblem,
    result: &UcpResult,
    evidence: &RecoveryEvidence,
    discovery_available: bool,
) {
    if result.value_facts.domain_is_complete(cell) {
        return;
    }
    if evidence.samples(cell).len() >= 2 {
        return;
    }
    let existing = actions.iter().position(|action| action.cell() == cell);
    let action = match result.value_facts.domain(cell) {
        Some(UcpValueDomain::Exact(_)) => return,
        Some(UcpValueDomain::FiniteSet(_)) => {
            if existing.is_some() && refinement_cost(cell, problem, result, evidence) <= 2 {
                return;
            }
            RecoveryAction::Refine(cell.clone(), RecoveryStrategy::FastProbe)
        }
        None => {
            if existing.is_some() || discovery_available {
                return;
            }
            // Letiltott vagy lezárt értékfelsorolás mellett korlátos, csak pontos visszaállítást célzó próbát is enged.
            RecoveryAction::Discover(cell.clone(), RecoveryStrategy::FastProbe)
        }
    };
    if let Some(index) = existing {
        actions[index] = action;
    } else {
        actions.push(action);
    }
}

// A már engedélyezett jelölteket becsült propagációs haszon/költség szerint rangsorolja.
// A szimuláció saját másolatokon fut, így a hipotetikus tények nem kerülnek K-ba vagy Deltába.
pub(crate) fn choose_action(
    mut actions: Vec<RecoveryAction>,
    targets: &[CellId],
    problem: &UcpProblem,
    result: &UcpResult,
    evidence: &RecoveryEvidence,
) -> Option<RecoveryAction> {
    actions.retain(|action| !result.value_facts.domain_is_complete(action.cell()));
    if actions.len() <= 1 {
        return actions.pop();
    }
    actions
        .into_iter()
        .map(|action| {
            let cell = action.cell();
            let samples = evidence.samples(cell).len();
            let checks = match &action {
                _ if action.strategy() == RecoveryStrategy::FastProbe => 2,
                RecoveryAction::Refine(_, _) => refinement_cost(cell, problem, result, evidence),
                RecoveryAction::Discover(_, _) => {
                    if samples == 0 {
                        2
                    } else {
                        1
                    }
                }
            };
            let mut facts = result.facts.clone();
            facts.mark_unique(cell.clone());
            let simulated = problem
                .simulate_with_values(facts, result.value_facts.for_hypothetical_reasoning());
            let gain = 1 + targets
                .iter()
                .filter(|target| {
                    !result.facts.is_unique(target) && simulated.facts.is_unique(target)
                })
                .count();
            let target = targets.contains(cell);
            let known_unique = target && result.facts.is_unique(cell);
            // A domain teljességének vizsgálatát előnyben részesíti az ismert nemegyértelműség újbóli igazolásával szemben.
            let completion = samples > 0 && action.strategy() == RecoveryStrategy::DomainSearch;
            (action, known_unique, target, gain, checks, completion)
        })
        .max_by(|left, right| {
            left.1
                .cmp(&right.1)
                .then(left.2.cmp(&right.2))
                .then_with(|| {
                    ((left.3 as u128) * right.4 as u128).cmp(&((right.3 as u128) * left.4 as u128))
                })
                .then(left.5.cmp(&right.5))
                .then_with(|| right.4.cmp(&left.4))
                .then_with(|| right.0.cell().cmp(left.0.cell()))
                .then_with(|| {
                    let rank = |action: &RecoveryAction| match action {
                        RecoveryAction::Refine(_, _) => 0,
                        RecoveryAction::Discover(_, _) => 1,
                    };
                    rank(&left.0).cmp(&rank(&right.0))
                })
        })
        .map(|candidate| candidate.0)
}

#[cfg(test)]
mod tests {
    use super::super::{facts::UcpFacts, value::UcpValueFacts};
    use super::*;

    fn problem(cell: &CellId) -> UcpProblem {
        UcpProblem {
            expressions: Vec::new(),
            expression_domains: Vec::new(),
            lookups: Vec::new(),
            initial_facts: UcpFacts::new(),
            target_cells: vec![cell.clone()],
            output_cells: vec![cell.clone()],
            witness_cells: vec![cell.clone()],
            initial_value_facts: UcpValueFacts::new(),
            field_modulus: 101.into(),
        }
    }

    #[test]
    fn complete_domains_are_not_scheduled_or_reopened_as_fast_probes() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&cell);
        let mut values = UcpValueFacts::new();
        values.mark_domain(
            cell.clone(),
            UcpValueDomain::finite_set([3.into(), 7.into()]).unwrap(),
        );
        let mut result = problem.analyze_with_values(UcpFacts::new(), values);
        let mut evidence = RecoveryEvidence::default();
        evidence
            .remember_feasible_samples(&cell, [3.into(), 7.into()], &101.into())
            .unwrap();
        assert!(!evidence
            .certify_complete_domains(&mut result, &101.into())
            .unwrap());
        assert!(result.value_facts.domain_is_complete(&cell));
        assert!(!result.facts.is_unique(&cell));
        let mut actions = Vec::new();
        integrate_fast_probe(&mut actions, &cell, &problem, &result, &evidence, false);
        assert!(actions.is_empty());
        assert!(choose_action(
            vec![RecoveryAction::Refine(
                cell.clone(),
                RecoveryStrategy::DomainSearch
            )],
            &[cell.clone()],
            &problem,
            &result,
            &evidence
        )
        .is_none());
        assert!(!bridge_has_gain(&cell, &[cell.clone()], &problem, &result).unwrap());
        let mut refinement = super::super::privacy_domain::DomainRefinementState::new(
            super::super::privacy_domain::PrivacyDomainRefinementOptions {
                max_solver_checks: 10,
                max_candidates_per_cell: 2,
            },
        );
        assert!(refinement
            .choose_cell(&[cell.clone()], &problem, &result)
            .unwrap()
            .is_none());
        assert!(refinement
            .refine_domain(
                &cell,
                &result,
                &101.into(),
                &BTreeSet::new(),
                |_, _, _| unreachable!()
            )
            .unwrap()
            .is_none());
        assert_eq!(refinement.statistics.solver_checks, 0);
    }

    #[test]
    fn completeness_is_not_inferred_from_partial_samples_or_uniqueness_alone() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&cell);
        let mut values = UcpValueFacts::new();
        values.mark_domain(
            cell.clone(),
            UcpValueDomain::finite_set([3.into(), 7.into()]).unwrap(),
        );
        let mut result = problem.analyze_with_values(UcpFacts::from_iter([cell.clone()]), values);
        let mut evidence = RecoveryEvidence::default();
        evidence
            .remember_feasible_samples(&cell, [3.into()], &101.into())
            .unwrap();
        assert!(!evidence
            .certify_complete_domains(&mut result, &101.into())
            .unwrap());
        assert!(!result.value_facts.domain_is_complete(&cell));
        evidence
            .remember_feasible_samples(&cell, [7.into()], &101.into())
            .unwrap();
        assert!(evidence
            .certify_complete_domains(&mut result, &101.into())
            .is_err());
        assert!(!result.value_facts.domain_is_complete(&cell));
    }

    #[test]
    fn completeness_alias_canonicalization_requests_one_new_value_propagation() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&cell);
        let mut values = UcpValueFacts::new();
        values.mark_domain(
            cell.clone(),
            UcpValueDomain::finite_set([(-1).into(), 100.into()]).unwrap(),
        );
        let mut result = problem.analyze_with_values(UcpFacts::new(), values);
        let mut evidence = RecoveryEvidence::default();
        evidence
            .remember_feasible_samples(&cell, [100.into()], &101.into())
            .unwrap();
        assert!(evidence
            .certify_complete_domains(&mut result, &101.into())
            .unwrap());
        assert!(result.value_facts.known_value(&cell).is_some());
        assert!(!evidence
            .certify_complete_domains(&mut result, &101.into())
            .unwrap());
        let propagated = problem.analyze_with_values(result.facts, result.value_facts);
        assert!(propagated.facts.is_unique(&cell));
        assert!(propagated.value_facts.domain_is_complete(&cell));
    }

    #[test]
    fn refinement_selects_an_internal_probe_then_reuses_known_feasible_values() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&cell);
        let mut values = UcpValueFacts::new();
        values.mark_domain(
            cell.clone(),
            UcpValueDomain::finite_set((0..16).map(BigInt::from)).unwrap(),
        );
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        let before = result.clone();
        let mut evidence = RecoveryEvidence::default();
        let mut actions = vec![RecoveryAction::Refine(
            cell.clone(),
            RecoveryStrategy::DomainSearch,
        )];
        integrate_fast_probe(&mut actions, &cell, &problem, &result, &evidence, false);
        assert_eq!(actions.len(), 1);
        assert_eq!(
            choose_action(actions, &[cell.clone()], &problem, &result, &evidence),
            Some(RecoveryAction::Refine(
                cell.clone(),
                RecoveryStrategy::FastProbe
            ))
        );
        evidence
            .remember_feasible_samples(&cell, (0..16).map(BigInt::from), &101.into())
            .unwrap();
        let mut actions = vec![RecoveryAction::Refine(
            cell.clone(),
            RecoveryStrategy::DomainSearch,
        )];
        integrate_fast_probe(&mut actions, &cell, &problem, &result, &evidence, false);
        assert_eq!(
            choose_action(actions, &[cell.clone()], &problem, &result, &evidence),
            Some(RecoveryAction::Refine(cell, RecoveryStrategy::DomainSearch))
        );
        assert_eq!(result, before);
    }

    #[test]
    fn discovery_keeps_enumeration_and_does_not_reprove_known_non_uniqueness() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&cell);
        let result = problem.analyze_with_values(UcpFacts::new(), UcpValueFacts::new());
        let mut evidence = RecoveryEvidence::default();
        evidence
            .remember_feasible_samples(&cell, [3.into(), 7.into()], &101.into())
            .unwrap();
        let mut actions = vec![RecoveryAction::Discover(
            cell.clone(),
            RecoveryStrategy::DomainSearch,
        )];
        integrate_fast_probe(&mut actions, &cell, &problem, &result, &evidence, false);
        assert_eq!(
            choose_action(actions, &[cell.clone()], &problem, &result, &evidence),
            Some(RecoveryAction::Discover(
                cell.clone(),
                RecoveryStrategy::DomainSearch
            ))
        );
        let mut disabled = Vec::new();
        integrate_fast_probe(&mut disabled, &cell, &problem, &result, &evidence, false);
        assert!(disabled.is_empty());
        assert!(!result.facts.is_unique(&cell));
        assert!(result.value_facts.domain(&cell).is_none());
        assert!(evidence.samples(&CellId::advice(1, 0)).is_empty());
    }

    #[test]
    fn discovery_uses_a_bounded_probe_only_when_enumeration_is_unavailable() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&cell);
        let result = problem.analyze_with_values(UcpFacts::new(), UcpValueFacts::new());
        let evidence = RecoveryEvidence::default();
        let mut enabled = vec![RecoveryAction::Discover(
            cell.clone(),
            RecoveryStrategy::DomainSearch,
        )];
        integrate_fast_probe(&mut enabled, &cell, &problem, &result, &evidence, true);
        assert_eq!(
            enabled,
            vec![RecoveryAction::Discover(
                cell.clone(),
                RecoveryStrategy::DomainSearch
            )]
        );
        let mut disabled = Vec::new();
        integrate_fast_probe(&mut disabled, &cell, &problem, &result, &evidence, false);
        assert_eq!(
            disabled,
            vec![RecoveryAction::Discover(cell, RecoveryStrategy::FastProbe)]
        );
    }

    #[test]
    fn an_internal_probe_does_not_bypass_discovery_fairness() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&cell);
        let result = problem.analyze_with_values(UcpFacts::new(), UcpValueFacts::new());
        let mut actions = Vec::new();
        integrate_fast_probe(
            &mut actions,
            &cell,
            &problem,
            &result,
            &RecoveryEvidence::default(),
            true,
        );
        assert!(actions.is_empty());
    }

    #[test]
    fn refinement_prefers_cheap_candidate_checks_and_preserves_a_probe_fallback() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&cell);
        let mut values = UcpValueFacts::new();
        values.mark_domain(
            cell.clone(),
            UcpValueDomain::finite_set([3.into(), 7.into()]).unwrap(),
        );
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        let mut evidence = RecoveryEvidence::default();
        evidence
            .remember_feasible_samples(&cell, [3.into()], &101.into())
            .unwrap();
        let mut actions = vec![RecoveryAction::Refine(
            cell.clone(),
            RecoveryStrategy::DomainSearch,
        )];
        integrate_fast_probe(&mut actions, &cell, &problem, &result, &evidence, false);
        assert_eq!(
            actions,
            vec![RecoveryAction::Refine(
                cell.clone(),
                RecoveryStrategy::DomainSearch
            )]
        );
        let mut disabled = Vec::new();
        integrate_fast_probe(&mut disabled, &cell, &problem, &result, &evidence, false);
        assert_eq!(
            disabled,
            vec![RecoveryAction::Refine(cell, RecoveryStrategy::FastProbe)]
        );
    }

    #[test]
    fn two_feasible_values_prevent_a_probe_even_for_a_large_covering_domain() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&cell);
        let mut values = UcpValueFacts::new();
        values.mark_domain(
            cell.clone(),
            UcpValueDomain::finite_set((0..16).map(BigInt::from)).unwrap(),
        );
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        let mut evidence = RecoveryEvidence::default();
        evidence
            .remember_feasible_samples(&cell, [3.into(), 7.into()], &101.into())
            .unwrap();
        let mut actions = vec![RecoveryAction::Refine(
            cell.clone(),
            RecoveryStrategy::DomainSearch,
        )];
        integrate_fast_probe(&mut actions, &cell, &problem, &result, &evidence, false);
        assert_eq!(
            actions,
            vec![RecoveryAction::Refine(cell, RecoveryStrategy::DomainSearch)]
        );
    }
}

pub(crate) fn bridge_has_gain(
    cell: &CellId,
    targets: &[CellId],
    problem: &UcpProblem,
    result: &UcpResult,
) -> Result<bool> {
    if result.value_facts.domain_is_complete(cell) {
        return Ok(false);
    }
    if matches!(
        result.value_facts.domain(cell),
        Some(UcpValueDomain::FiniteSet(_))
    ) {
        return refinement_has_target_gain(cell, targets, problem, result);
    }
    let mut facts = result.facts.clone();
    facts.mark_unique(cell.clone());
    let simulated =
        problem.simulate_with_values(facts, result.value_facts.for_hypothetical_reasoning());
    Ok(targets.iter().any(|target| {
        (!result.facts.is_unique(target) && simulated.facts.is_unique(target))
            || domain_refined(
                result.value_facts.domain(target),
                simulated.value_facts.domain(target),
                &problem.field_modulus,
            )
    }))
}
