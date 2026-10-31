#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

//! A meglévő véges lefedő halmazokat korlátosan szűkíti, költség és szimulált haszon szerint ütemezve.
//! A recovery igazolt Delta-domainjéből indul; csak a jelöltek megvalósíthatóságát vizsgálja SMT-vel.

use super::{
    cell::CellId,
    engine::UcpResult,
    extractor::UcpProblem,
    privacy::{domain_refined, limitation_from_solver_error, RecoveryLimitation},
    value::{normalize_field_value, UcpValueDomain, MAX_FINITE_DOMAIN_SIZE},
};
use crate::smt_solver::smt_parser::Satisfiability;
use anyhow::{ensure, Context, Result};
use num_bigint::BigInt;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

#[path = "privacy_refinement_plan.rs"]
mod plan;
use plan::{critical_exclusions, RefinementPlan};

pub(crate) const PRIVACY_DOMAIN_REFINEMENT_POLICY: &str = "established-domain-refinement-v7";

const MAX_REFINEMENT_SCORED_CELLS: usize = 32;
const MAX_REFINEMENT_SIMULATIONS_PER_CELL: usize = 4;
const MAX_REFINEMENT_CACHED_SCORES: usize = 128;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrivacyDomainRefinementOptions {
    /// A tényleges jelöltvizsgálati solverhívásokat összesítve korlátozza; nulla esetén letiltja.
    pub max_solver_checks: usize,
    /// Csak a legfeljebb ekkora, már kikövetkeztetett véges halmazokat vizsgálja.
    pub max_candidates_per_cell: usize,
}

impl Default for PrivacyDomainRefinementOptions {
    fn default() -> Self {
        Self {
            max_solver_checks: 0,
            max_candidates_per_cell: 16,
        }
    }
}

impl PrivacyDomainRefinementOptions {
    pub(crate) fn validate(&self) -> Result<()> {
        ensure!(
            self.max_solver_checks == 0
                || (2..=MAX_FINITE_DOMAIN_SIZE).contains(&self.max_candidates_per_cell),
            "Enabled domain refinement requires 2..={} candidates per cell",
            MAX_FINITE_DOMAIN_SIZE
        );
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrivateDomainRefinementStatus {
    /// Igazolta a lefedést és az összes megmaradt jelölt megvalósíthatóságát az eredeti kontextusban.
    Complete,
    /// Igazolta a lefedést; a nem ellenőrzött vagy bizonytalan jelölteket lehetőségként megtartja.
    Partial,
    /// Önálló ellenőrzésben nem sikerült igazolni a lefedést; a recovery igazolt Deltából indul.
    CoverageUnknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrivateDomainRefinement {
    pub status: PrivateDomainRefinementStatus,
    /// A cella összes szűkítési kísérletének solverhívásait tárolja.
    pub solver_checks: usize,
    /// A legutóbbi kísérlet bemeneti méretét tárolja, különböző testelemeket számolva.
    pub candidate_count: usize,
    pub excluded_candidates: usize,
    pub feasible_candidates: usize,
    pub unresolved_candidates: usize,
    /// A domainkeresés további korlátját jelzi, az egyértelműségi eredménytől függetlenül.
    pub limitation: Option<RecoveryLimitation>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PrivacyDomainRefinementStatistics {
    pub solver_checks: usize,
    pub attempted_cells: usize,
    pub complete_domains: usize,
    pub removed_candidates: usize,
    pub budget_exhausted: bool,
}

pub(crate) struct DomainRefinementState {
    pub statistics: PrivacyDomainRefinementStatistics,
    pub cells: BTreeMap<CellId, PrivateDomainRefinement>,
    options: PrivacyDomainRefinementOptions,
    generation: usize,
    attempts: BTreeMap<CellId, RefinementAttempt>,
    score_cache: RefinementScoreCache,
    plans: BTreeMap<CellId, RefinementPlan>,
}

#[derive(Default)]
struct RefinementAttempt {
    generation: usize,
    order: usize,
    covered: Option<BTreeSet<BigInt>>,
    feasible: BTreeSet<BigInt>,
    excluded: BTreeSet<BigInt>,
    yielded: bool,
}

enum RefinementCoverage {
    /// A valódi recovery-állapotból átvett domain lefedését a Delta-invariáns biztosítja.
    Established,
    #[cfg(test)]
    CheckOriginal,
}

impl DomainRefinementState {
    pub fn new(options: PrivacyDomainRefinementOptions) -> Self {
        Self {
            options,
            statistics: Default::default(),
            cells: BTreeMap::new(),
            generation: 0,
            attempts: BTreeMap::new(),
            plans: BTreeMap::new(),
            score_cache: RefinementScoreCache {
                enabled: std::env::var("HALO2_ANALYZER_REFINEMENT_CACHE").as_deref() != Ok("0"),
                ..Default::default()
            },
        }
    }

    pub(crate) fn observe_progress(&mut self, generation: usize) {
        if generation > self.generation {
            self.plans.clear();
        }
        self.generation = self.generation.max(generation);
    }

    fn can_attempt(&self, cell: &CellId) -> bool {
        match self.cells.get(cell) {
            None => true,
            Some(evidence) if evidence.status == PrivateDomainRefinementStatus::Complete => false,
            Some(_) => self
                .attempts
                .get(cell)
                .is_some_and(|attempt| attempt.generation < self.generation),
        }
    }

    pub(super) fn planned_gain(&self, cell: &CellId) -> Option<usize> {
        self.plans
            .get(cell)
            .filter(|plan| !plan.yield_after.is_empty())
            .map(|plan| plan.expected_gain)
    }

    /// Részleges vizsgálatot csak új tudásgeneráció után enged folytatni.
    #[cfg(test)]
    pub fn refine_next(
        &mut self,
        private_cells: &[CellId],
        problem: &UcpProblem,
        result: &UcpResult,
        mut check: impl FnMut(&CellId, &UcpValueDomain, bool) -> Result<Satisfiability>,
    ) -> Result<Option<(CellId, UcpValueDomain, bool)>> {
        let Some(cell) = self.choose_cell(private_cells, problem, result)? else {
            return Ok(None);
        };
        self.refine_domain(
            &cell,
            result,
            &problem.field_modulus,
            &BTreeSet::new(),
            |cell, domain, exclude| check(cell, domain, exclude),
        )
    }

    pub(crate) fn choose_cell(
        &mut self,
        private_cells: &[CellId],
        problem: &UcpProblem,
        result: &UcpResult,
    ) -> Result<Option<CellId>> {
        let _profile = super::profiling::scope("scheduler.refinement");
        if self.options.max_solver_checks == 0 {
            return Ok(None);
        }
        let mut eligible = Vec::new();
        for cell in private_cells {
            if !self.can_attempt(cell) || result.value_facts.domain_is_complete(cell) {
                continue;
            }
            let Some(domain @ UcpValueDomain::FiniteSet(_)) = result.value_facts.domain(cell)
            else {
                continue;
            };
            let candidates = canonical_candidates(domain, &problem.field_modulus)?;
            if candidates.len() > self.options.max_candidates_per_cell {
                continue;
            }
            eligible.push(RefinementCandidate { cell, candidates });
        }
        if eligible.is_empty() {
            return Ok(None);
        }
        // Az UCP kedvéért félbehagyott vizsgálatot az új tudással egyszer előbb folytatja.
        // A can_attempt változatlan állapotban ezt sem engedi újra; újabb átadás csak új kizárásból lehet.
        if eligible
            .iter()
            .any(|candidate| self.attempts.get(candidate.cell).is_some_and(|a| a.yielded))
        {
            eligible
                .retain(|candidate| self.attempts.get(candidate.cell).is_some_and(|a| a.yielded));
        }
        // A friss cellákat sorolja előre, majd a régebbi próbákat, és csak ezután pontozza a hasznot.
        let oldest = eligible
            .iter()
            .map(|candidate| {
                self.attempts
                    .get(candidate.cell)
                    .map(|attempt| (attempt.generation, attempt.order))
            })
            .min()
            .unwrap();
        eligible.retain(|candidate| {
            self.attempts
                .get(candidate.cell)
                .map(|attempt| (attempt.generation, attempt.order))
                == oldest
        });
        let remaining = self.options.max_solver_checks - self.statistics.solver_checks;
        if remaining == 0 {
            self.statistics.budget_exhausted = true;
            return Ok(None);
        }
        // Az olcsó előszűréssel korlátozza a szimulációs munkát; a ki nem választott cellákat nem zárja ki végleg.
        eligible.sort_by_key(|candidate| {
            (
                candidate.candidates.len() > remaining,
                candidate.candidates.len(),
                candidate.cell,
            )
        });
        self.score_cache.observe(problem, result);
        // Előbb a tényleges propagációs nyereséget ígérő premisszafeloldást pontozza.
        // Sikeres előszűrésnél nem futtatja le az összes általános jelöltszimulációt.
        let critical = if remaining > 1 {
            eligible
                .iter()
                .take(MAX_REFINEMENT_SCORED_CELLS)
                .enumerate()
                .filter(|(_, candidate)| {
                    !critical_exclusions(candidate, problem, &result.value_facts).is_empty()
                })
                .map(|(index, candidate)| {
                    (
                        index,
                        self.score_cache.score(
                            candidate,
                            private_cells,
                            problem,
                            result,
                            remaining,
                        ),
                    )
                })
                .filter(|(_, score)| score.fits_budget && !score.plan.yield_after.is_empty())
                .max_by(|(_, left), (_, right)| left.compare(right))
        } else {
            None
        };
        let (selected, plan) = if let Some((index, score)) = critical {
            super::profiling::count("refinement.premise_shortlist");
            (index, score.plan)
        } else if remaining == 1 || eligible.len() == 1 {
            let plan = if remaining > 1
                && !critical_exclusions(&eligible[0], problem, &result.value_facts).is_empty()
            {
                self.score_cache
                    .score(&eligible[0], private_cells, problem, result, remaining)
                    .plan
            } else {
                RefinementPlan::default()
            };
            (0, plan)
        } else {
            let (index, score) = eligible
                .iter()
                .take(MAX_REFINEMENT_SCORED_CELLS)
                .enumerate()
                .map(|(index, candidate)| {
                    (
                        index,
                        self.score_cache.score(
                            candidate,
                            private_cells,
                            problem,
                            result,
                            remaining,
                        ),
                    )
                })
                .max_by(|(_, left), (_, right)| left.compare(right))
                .unwrap();
            (index, score.plan)
        };
        self.plans.insert(eligible[selected].cell.clone(), plan);
        Ok(Some(eligible[selected].cell.clone()))
    }

    pub(crate) fn refine_domain(
        &mut self,
        cell: &CellId,
        result: &UcpResult,
        modulus: &BigInt,
        feasible: &BTreeSet<BigInt>,
        mut check: impl FnMut(&CellId, &UcpValueDomain, bool) -> Result<Satisfiability>,
    ) -> Result<Option<(CellId, UcpValueDomain, bool)>> {
        if !self.can_attempt(cell)
            || result.value_facts.domain_is_complete(cell)
            || self.statistics.solver_checks >= self.options.max_solver_checks
        {
            return Ok(None);
        }
        let Some(domain @ UcpValueDomain::FiniteSet(_)) = result.value_facts.domain(cell) else {
            return Ok(None);
        };
        let candidates = canonical_candidates(domain, modulus)?;
        let remaining = self.options.max_solver_checks - self.statistics.solver_checks;
        let previous_checks = self
            .cells
            .get(cell)
            .map_or(0, |evidence| evidence.solver_checks);
        let resumed = self.cells.contains_key(cell);
        let plan = self.plans.remove(cell).unwrap_or_default();
        let attempt = self.attempts.entry(cell.clone()).or_default();
        attempt.generation = self.generation;
        attempt.order = self.statistics.solver_checks;
        let previous_exclusions = attempt.excluded.len();
        let (refined, mut evidence) = refine_domain_with_plan(
            domain,
            candidates,
            remaining,
            feasible,
            attempt,
            &plan,
            RefinementCoverage::Established,
            |domain, exclude| check(cell, domain, exclude),
        )?;
        self.statistics.solver_checks += evidence.solver_checks;
        evidence.solver_checks += previous_checks;
        self.statistics.attempted_cells += usize::from(!resumed);
        self.statistics.complete_domains +=
            usize::from(evidence.status == PrivateDomainRefinementStatus::Complete);
        self.statistics.removed_candidates += attempt.excluded.len() - previous_exclusions;
        self.statistics.budget_exhausted |=
            evidence.limitation == Some(RecoveryLimitation::QueryLimit);
        // Két SAT-jelöltből nemegyértelműséget igazol akkor is, ha a többi jelölt vizsgálata részleges marad.
        let non_unique = evidence.feasible_candidates >= 2;
        self.cells.insert(cell.clone(), evidence);
        Ok(Some((cell.clone(), refined, non_unique)))
    }
}

struct RefinementCandidate<'a> {
    cell: &'a CellId,
    candidates: BTreeMap<BigInt, BigInt>,
}

struct RefinementScore<'a> {
    cell: &'a CellId,
    fits_budget: bool,
    checks: usize,
    simulations: usize,
    exact_targets: usize,
    refined_targets: usize,
    unique_targets: usize,
    refined_cells: usize,
    unique_cells: usize,
    unlock_exact_targets: usize,
    unlock_refined_targets: usize,
    plan: RefinementPlan,
}

#[derive(Clone)]
struct RefinementBenefit {
    simulations: usize,
    exact_targets: usize,
    refined_targets: usize,
    unique_targets: usize,
    refined_cells: usize,
    unique_cells: usize,
    unlock_exact_targets: usize,
    unlock_refined_targets: usize,
    plan: RefinementPlan,
}

#[derive(Default)]
struct RefinementScoreCache {
    enabled: bool,
    context: Option<(
        UcpProblem,
        super::facts::UcpFacts,
        super::value::UcpValueFacts,
    )>,
    benefits: BTreeMap<(Vec<CellId>, CellId), RefinementBenefit>,
}

impl RefinementScoreCache {
    fn observe(&mut self, problem: &UcpProblem, result: &UcpResult) {
        if !self.enabled {
            return;
        }
        let unchanged = self.context.as_ref().is_some_and(|(p, facts, values)| {
            p == problem && facts == &result.facts && values == &result.value_facts
        });
        if !unchanged {
            self.context = Some((
                problem.clone(),
                result.facts.clone(),
                result.value_facts.clone(),
            ));
            self.benefits.clear();
        }
    }

    fn score<'a>(
        &mut self,
        candidate: &RefinementCandidate<'a>,
        targets: &[CellId],
        problem: &UcpProblem,
        result: &UcpResult,
        remaining: usize,
    ) -> RefinementScore<'a> {
        if !self.enabled {
            return score_refinement(candidate, targets, problem, result, remaining);
        }
        let key = (targets.to_vec(), candidate.cell.clone());
        if let Some(benefit) = self.benefits.get(&key) {
            super::profiling::count("refinement_score_cache.hit");
            // Csak a szimulált hasznot őrzi meg; a költséget és a keretbe férő munkát újraszámítja.
            let checks = candidate.candidates.len();
            return RefinementScore {
                cell: candidate.cell,
                fits_budget: checks <= remaining,
                checks,
                simulations: benefit.simulations,
                exact_targets: benefit.exact_targets,
                refined_targets: benefit.refined_targets,
                unique_targets: benefit.unique_targets,
                refined_cells: benefit.refined_cells,
                unique_cells: benefit.unique_cells,
                unlock_exact_targets: benefit.unlock_exact_targets,
                unlock_refined_targets: benefit.unlock_refined_targets,
                plan: benefit.plan.clone(),
            };
        }
        super::profiling::count("refinement_score_cache.miss");
        let score = score_refinement(candidate, targets, problem, result, remaining);
        // A tárolás elmaradása csak újraszámítást okoz, jelöltet vagy domaint nem zár ki.
        if self.benefits.len() < MAX_REFINEMENT_CACHED_SCORES {
            self.benefits.insert(
                key,
                RefinementBenefit {
                    simulations: score.simulations,
                    exact_targets: score.exact_targets,
                    refined_targets: score.refined_targets,
                    unique_targets: score.unique_targets,
                    refined_cells: score.refined_cells,
                    unique_cells: score.unique_cells,
                    unlock_exact_targets: score.unlock_exact_targets,
                    unlock_refined_targets: score.unlock_refined_targets,
                    plan: score.plan.clone(),
                },
            );
        }
        score
    }
}

impl RefinementScore<'_> {
    fn compare(&self, other: &Self) -> Ordering {
        let rate = |left: usize, right: usize| {
            ((left as u128) * (other.simulations * other.checks) as u128)
                .cmp(&((right as u128) * (self.simulations * self.checks) as u128))
        };
        self.fits_budget
            .cmp(&other.fits_budget)
            .then(self.unlock_exact_targets.cmp(&other.unlock_exact_targets))
            .then(
                self.unlock_refined_targets
                    .cmp(&other.unlock_refined_targets),
            )
            .then_with(|| rate(self.exact_targets, other.exact_targets))
            .then_with(|| rate(self.refined_targets, other.refined_targets))
            .then_with(|| rate(self.unique_targets, other.unique_targets))
            .then_with(|| rate(self.refined_cells, other.refined_cells))
            .then_with(|| rate(self.unique_cells, other.unique_cells))
            .then_with(|| other.checks.cmp(&self.checks))
            .then_with(|| other.cell.cmp(self.cell))
    }
}

fn score_refinement<'a>(
    candidate: &RefinementCandidate<'a>,
    targets: &[CellId],
    problem: &UcpProblem,
    result: &UcpResult,
    remaining: usize,
) -> RefinementScore<'a> {
    let count = candidate.candidates.len();
    let critical = critical_exclusions(candidate, problem, &result.value_facts);
    let mut removals: Vec<_> = critical
        .iter()
        .take(MAX_REFINEMENT_SIMULATIONS_PER_CELL)
        .cloned()
        .collect();
    let uniform = count.min(MAX_REFINEMENT_SIMULATIONS_PER_CELL);
    let candidates: Vec<_> = candidate.candidates.keys().cloned().collect();
    for trial in 0..uniform {
        let index = if uniform == 1 {
            0
        } else {
            trial * (count - 1) / (uniform - 1)
        };
        if removals.len() < MAX_REFINEMENT_SIMULATIONS_PER_CELL
            && !removals.contains(&candidates[index])
        {
            removals.push(candidates[index].clone());
        }
    }
    let simulations = removals.len();
    let mut score = RefinementScore {
        cell: candidate.cell,
        fits_budget: count <= remaining,
        checks: count,
        simulations,
        exact_targets: 0,
        refined_targets: 0,
        unique_targets: 0,
        refined_cells: 0,
        unique_cells: 0,
        unlock_exact_targets: 0,
        unlock_refined_targets: 0,
        plan: RefinementPlan::default(),
    };
    let mut priorities = Vec::new();
    for removed in removals {
        let hypothetical = UcpValueDomain::finite_set(
            candidate
                .candidates
                .iter()
                // A testben egyező jelöltekből álló egyelemű domainnél csak kanonizálást végez.
                .filter(|(canonical, _)| count == 1 || **canonical != removed)
                .map(|(_, value)| value.clone()),
        )
        .expect("A simulated refinement retains at least one candidate");
        let mut values = result.value_facts.for_hypothetical_reasoning();
        values.mark_domain(candidate.cell.clone(), hypothetical);
        // A feltételezett kizárásokat csak rangsorolásra használja, tényként nem jegyzi be.
        let simulated = problem.simulate_with_values(result.facts.clone(), values);
        let mut exact_gain = 0;
        let mut other_gain = 0;
        for target in targets {
            let exact = usize::from(
                result.value_facts.known_value(target).is_none()
                    && simulated.value_facts.known_value(target).is_some(),
            );
            let refined = usize::from(domain_refined(
                result.value_facts.domain(target),
                simulated.value_facts.domain(target),
                &problem.field_modulus,
            ));
            score.exact_targets += exact;
            score.refined_targets += refined;
            exact_gain += usize::from(target != candidate.cell) * exact;
            other_gain += usize::from(target != candidate.cell) * refined;
            score.unique_targets +=
                usize::from(!result.facts.is_unique(target) && simulated.facts.is_unique(target));
        }
        score.refined_cells += simulated
            .value_facts
            .domains()
            .iter()
            .filter(|(cell, domain)| {
                domain_refined(
                    result.value_facts.domain(cell),
                    Some(domain),
                    &problem.field_modulus,
                )
            })
            .count();
        score.unique_cells += simulated
            .facts
            .unique_cells()
            .difference(result.facts.unique_cells())
            .count();
        if critical.contains(&removed) && (exact_gain > 0 || other_gain > 0) {
            score.unlock_exact_targets = score.unlock_exact_targets.max(exact_gain);
            score.unlock_refined_targets = score.unlock_refined_targets.max(other_gain);
            score.plan.yield_after.insert(removed.clone());
            score.plan.expected_gain = score.plan.expected_gain.max(exact_gain.max(other_gain));
            priorities.push((exact_gain, other_gain, removed));
        }
    }
    priorities.sort_by(|left, right| {
        right
            .0
            .cmp(&left.0)
            .then(right.1.cmp(&left.1))
            .then(left.2.cmp(&right.2))
    });
    score.plan.priority = priorities.into_iter().map(|(_, _, value)| value).collect();
    score
}

pub(crate) fn refinement_has_target_gain(
    cell: &CellId,
    targets: &[CellId],
    problem: &UcpProblem,
    result: &UcpResult,
) -> Result<bool> {
    if result.value_facts.domain_is_complete(cell) {
        return Ok(false);
    }
    let Some(domain @ UcpValueDomain::FiniteSet(_)) = result.value_facts.domain(cell) else {
        return Ok(false);
    };
    let candidate = RefinementCandidate {
        cell,
        candidates: canonical_candidates(domain, &problem.field_modulus)?,
    };
    let score = score_refinement(&candidate, targets, problem, result, usize::MAX);
    Ok(score.exact_targets > 0 || score.refined_targets > 0 || score.unique_targets > 0)
}

// A Delta-metszéshez megtartja az eredeti reprezentánsokat, és test szerint szűri ki az ismétléseket.
fn canonical_candidates(
    domain: &UcpValueDomain,
    modulus: &BigInt,
) -> Result<BTreeMap<BigInt, BigInt>> {
    let values: Vec<_> = match domain {
        UcpValueDomain::Exact(value) => vec![value],
        UcpValueDomain::FiniteSet(values) => values.iter().collect(),
    };
    let mut candidates = BTreeMap::new();
    for value in values {
        candidates
            .entry(
                normalize_field_value(value.clone(), modulus)
                    .context("Unsupported finite-domain field value")?,
            )
            .or_insert_with(|| value.clone());
    }
    ensure!(
        !candidates.is_empty(),
        "Cannot refine an empty candidate domain"
    );
    Ok(candidates)
}

#[cfg(test)]
fn refine_domain(
    domain: &UcpValueDomain,
    candidates: BTreeMap<BigInt, BigInt>,
    max_checks: usize,
    check: impl FnMut(&UcpValueDomain, bool) -> Result<Satisfiability>,
) -> Result<(UcpValueDomain, PrivateDomainRefinement)> {
    refine_domain_with_samples(
        domain,
        candidates,
        max_checks,
        &BTreeSet::new(),
        &mut RefinementAttempt::default(),
        check,
    )
}

#[cfg(test)]
fn refine_domain_with_samples(
    domain: &UcpValueDomain,
    candidates: BTreeMap<BigInt, BigInt>,
    max_checks: usize,
    known_feasible: &BTreeSet<BigInt>,
    attempt: &mut RefinementAttempt,
    check: impl FnMut(&UcpValueDomain, bool) -> Result<Satisfiability>,
) -> Result<(UcpValueDomain, PrivateDomainRefinement)> {
    refine_domain_with_plan(
        domain,
        candidates,
        max_checks,
        known_feasible,
        attempt,
        &RefinementPlan::default(),
        RefinementCoverage::CheckOriginal,
        check,
    )
}

#[allow(clippy::too_many_arguments)]
fn refine_domain_with_plan(
    domain: &UcpValueDomain,
    candidates: BTreeMap<BigInt, BigInt>,
    max_checks: usize,
    known_feasible: &BTreeSet<BigInt>,
    attempt: &mut RefinementAttempt,
    plan: &RefinementPlan,
    coverage: RefinementCoverage,
    mut check: impl FnMut(&UcpValueDomain, bool) -> Result<Satisfiability>,
) -> Result<(UcpValueDomain, PrivateDomainRefinement)> {
    attempt.yielded = false;
    let mut evidence = PrivateDomainRefinement {
        status: PrivateDomainRefinementStatus::CoverageUnknown,
        solver_checks: 0,
        candidate_count: candidates.len(),
        excluded_candidates: 0,
        feasible_candidates: 0,
        unresolved_candidates: candidates.len(),
        limitation: None,
    };
    ensure!(
        known_feasible
            .iter()
            .chain(&attempt.feasible)
            .all(|value| candidates.contains_key(value)),
        "Refinement domain excludes a previously feasible value"
    );
    attempt.feasible.extend(known_feasible.iter().cloned());
    ensure!(
        attempt.feasible.is_disjoint(&attempt.excluded),
        "Refinement evidence contradicts a previously feasible value"
    );
    // A recoveryban a lefedés már bizonyított premissza, ezért nem indít új SMT-lefedésvizsgálatot.
    if matches!(coverage, RefinementCoverage::Established) {
        attempt.covered = Some(candidates.keys().cloned().collect());
    }
    // Az önálló ellenőrzés is újrahasználhat korábbi lefedési bizonyítékot és igazolt kizárásokat.
    let coverage_known = attempt.covered.as_ref().is_some_and(|covered| {
        covered
            .difference(&attempt.excluded)
            .all(|value| candidates.contains_key(value))
    });
    if !coverage_known {
        evidence.solver_checks += 1;
        match check(domain, true) {
            Ok(Satisfiability::Unsatisfiable) => {
                attempt.covered = Some(candidates.keys().cloned().collect());
            }
            Ok(Satisfiability::Satisfiable) => {
                anyhow::bail!("Finite candidate domain does not cover the original circuit")
            }
            Err(error) => {
                evidence.limitation = Some(limitation_from_solver_error(error)?);
                return Ok((domain.clone(), evidence));
            }
        }
    }
    evidence.status = PrivateDomainRefinementStatus::Partial;
    let priority: BTreeSet<_> = plan.priority.iter().collect();
    let order = plan
        .priority
        .iter()
        .filter(|value| candidates.contains_key(*value))
        .chain(candidates.keys().filter(|value| !priority.contains(value)));
    for value in order {
        if attempt.feasible.contains(value) || attempt.excluded.contains(value) {
            continue;
        }
        if evidence.solver_checks >= max_checks {
            evidence.limitation = Some(RecoveryLimitation::QueryLimit);
            break;
        }
        evidence.solver_checks += 1;
        match check(&UcpValueDomain::exact(value.clone()), false) {
            Ok(Satisfiability::Unsatisfiable) => {
                attempt.excluded.insert(value.clone());
                // Csak igazolt kizárás után adja át a részleges domaint az új propagációnak.
                if plan.yield_after.contains(value) {
                    attempt.yielded = true;
                    super::profiling::count("refinement.early_yield");
                    break;
                }
            }
            Ok(Satisfiability::Satisfiable) => {
                attempt.feasible.insert(value.clone());
            }
            Err(error) => {
                evidence.limitation = Some(limitation_from_solver_error(error)?);
            }
        }
    }
    let retained: Vec<_> = candidates
        .iter()
        .filter(|(value, _)| !attempt.excluded.contains(*value))
        .collect();
    ensure!(
        !retained.is_empty(),
        "Candidate exclusion contradicts the originally satisfiable circuit"
    );
    // Az eredeti SAT és az egyelemű lefedés alapján külön SAT-válasz nélkül is igazolja a megvalósíthatóságot.
    if retained.len() == 1 {
        attempt.feasible.insert(retained[0].0.clone());
    }
    evidence.excluded_candidates = candidates.len() - retained.len();
    evidence.feasible_candidates = retained
        .iter()
        .filter(|(value, _)| attempt.feasible.contains(*value))
        .count();
    evidence.unresolved_candidates = retained.len() - evidence.feasible_candidates;
    if evidence.unresolved_candidates == 0 {
        evidence.status = PrivateDomainRefinementStatus::Complete;
        evidence.limitation = None;
    }
    let refined =
        UcpValueDomain::finite_set(retained.into_iter().map(|(_, original)| original.clone()))
            .context("Refined domain exceeds the representation limit")?;
    Ok((refined, evidence))
}

#[cfg(test)]
mod tests {
    use super::super::{expr::UcpExpr, facts::UcpFacts, value::UcpValueFacts};
    use super::*;
    use crate::smt_solver::smt_parser::{SolverUnknownDetails, UnknownSolverResult};

    fn domain(values: &[i64]) -> UcpValueDomain {
        UcpValueDomain::finite_set(values.iter().copied().map(BigInt::from)).unwrap()
    }

    fn unknown() -> anyhow::Error {
        anyhow::anyhow!(UnknownSolverResult).context(SolverUnknownDetails {
            reason: Some("TIMEOUT".into()),
        })
    }

    fn problem(targets: &[CellId], expressions: Vec<UcpExpr>) -> UcpProblem {
        UcpProblem {
            expressions,
            expression_domains: Vec::new(),
            lookups: Vec::new(),
            initial_facts: UcpFacts::new(),
            target_cells: targets.to_vec(),
            output_cells: targets.to_vec(),
            witness_cells: targets.to_vec(),
            initial_value_facts: UcpValueFacts::new(),
            field_modulus: 101.into(),
        }
    }

    fn refine_one(
        targets: &[CellId],
        problem: &UcpProblem,
        result: &UcpResult,
        checks: usize,
    ) -> (CellId, DomainRefinementState) {
        let before = result.clone();
        let mut state = DomainRefinementState::new(PrivacyDomainRefinementOptions {
            max_solver_checks: checks,
            max_candidates_per_cell: 16,
        });
        let mut actual_checks = 0;
        let (cell, refined, non_unique) = state
            .refine_next(targets, problem, result, |_, _, exclude| {
                actual_checks += 1;
                Ok(if exclude {
                    Satisfiability::Unsatisfiable
                } else {
                    Satisfiability::Satisfiable
                })
            })
            .unwrap()
            .unwrap();
        assert_eq!(actual_checks, state.statistics.solver_checks);
        assert_eq!(*result, before);
        assert_eq!(
            canonical_candidates(&refined, &problem.field_modulus).unwrap(),
            canonical_candidates(
                result.value_facts.domain(&cell).unwrap(),
                &problem.field_modulus
            )
            .unwrap()
        );
        assert_eq!(non_unique, actual_checks >= 2);
        (cell, state)
    }

    #[test]
    fn refinement_score_cache_reuses_benefits_but_rechecks_budget_and_context() {
        let targets = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let mut problem = problem(&targets, Vec::new());
        let mut values = UcpValueFacts::new();
        values.mark_domain(targets[0].clone(), domain(&[0, 1]));
        values.mark_domain(targets[1].clone(), domain(&[0, 1, 2]));
        let mut result = problem.analyze_with_values(UcpFacts::new(), values);
        let mut state = DomainRefinementState::new(PrivacyDomainRefinementOptions {
            max_solver_checks: 10,
            max_candidates_per_cell: 16,
        });
        state.score_cache.enabled = true;
        let profiling = super::super::profiling::ProfilingSession::start();
        let first = state.choose_cell(&targets, &problem, &result).unwrap();
        let simulations = profiling.snapshot().measurements["ucp.simulation"].calls;
        state.choose_cell(&targets[1..], &problem, &result).unwrap();
        state.statistics.solver_checks = 8;
        assert_eq!(
            first,
            state.choose_cell(&targets, &problem, &result).unwrap()
        );
        assert_eq!(
            profiling.snapshot().measurements["ucp.simulation"].calls,
            simulations
        );
        assert_eq!(
            profiling.snapshot().counters["refinement_score_cache.hit"],
            2
        );
        let candidate = RefinementCandidate {
            cell: &targets[0],
            candidates: canonical_candidates(
                result.value_facts.domain(&targets[0]).unwrap(),
                &problem.field_modulus,
            )
            .unwrap(),
        };
        assert!(
            !state
                .score_cache
                .score(&candidate, &targets, &problem, &result, 1)
                .fits_budget
        );
        problem.field_modulus = BigInt::from(103);
        state.choose_cell(&targets, &problem, &result).unwrap();
        assert!(profiling.snapshot().measurements["ucp.simulation"].calls > simulations);
        result
            .value_facts
            .mark_complete_from_samples(
                &targets[0],
                &[0.into(), 1.into()].into(),
                &problem.field_modulus,
            )
            .unwrap();
        state.choose_cell(&targets, &problem, &result).unwrap();
        assert!(state.score_cache.benefits.is_empty());
        let selected = state.choose_cell(&targets, &problem, &result).unwrap();
        state.score_cache.enabled = false;
        assert_eq!(
            selected,
            state.choose_cell(&targets, &problem, &result).unwrap()
        );
    }

    #[test]
    fn refinement_priority_prefers_a_cheaper_later_cell_and_preserves_the_hard_cap() {
        let targets = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let problem = problem(&targets, Vec::new());
        let mut values = UcpValueFacts::new();
        values.mark_domain(targets[0].clone(), domain(&[0, 1, 2, 3]));
        values.mark_domain(targets[1].clone(), domain(&[0, 1]));
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        let (selected, mut state) = refine_one(&targets, &problem, &result, 2);
        assert_eq!(selected, targets[1]);
        assert_eq!(state.statistics.solver_checks, 2);
        assert_eq!(state.statistics.attempted_cells, 1);
        assert!(state
            .refine_next(&targets, &problem, &result, |_, _, _| unreachable!())
            .unwrap()
            .is_none());
        assert!(state.statistics.budget_exhausted);
    }

    #[test]
    fn refinement_priority_simulates_non_singleton_exclusions_without_exporting_them() {
        let targets = [
            CellId::advice(0, 0),
            CellId::advice(1, 0),
            CellId::advice(2, 0),
        ];
        let problem = problem(
            &targets,
            vec![UcpExpr::mul(
                UcpExpr::var(targets[2].clone()),
                UcpExpr::add(
                    UcpExpr::var(targets[1].clone()),
                    UcpExpr::known_constant_i64(-5),
                ),
            )],
        );
        let mut values = UcpValueFacts::new();
        values.mark_domain(targets[0].clone(), domain(&[3, 4, 7]));
        values.mark_domain(targets[1].clone(), domain(&[3, 5, 7]));
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        assert!(result.value_facts.domain(&targets[2]).is_none());
        // A teszt az 5 kizárását szimulálja: a domain nem egyelemű, de a függő szorzat nullává válna.
        let (selected, _) = refine_one(&targets, &problem, &result, 4);
        assert_eq!(selected, targets[1]);
        assert!(!result.facts.is_unique(&targets[1]));
        assert!(result.value_facts.domain(&targets[2]).is_none());
    }

    #[test]
    fn critical_exclusion_yields_then_resumes_without_rechecking_coverage_or_values() {
        for root in [2, 5, 8] {
            let targets = [
                CellId::advice(9, 4),
                CellId::advice(7, -2),
                CellId::advice(2, 9),
            ];
            let mode = UcpExpr::var(targets[1].clone());
            let problem = problem(
                &targets,
                vec![
                    UcpExpr::mul(
                        UcpExpr::var(targets[2].clone()),
                        UcpExpr::add(mode.clone(), UcpExpr::known_constant_i64(-root)),
                    ),
                    UcpExpr::add(
                        UcpExpr::add(
                            UcpExpr::mul(mode.clone(), mode.clone()),
                            UcpExpr::scale_by(
                                mode,
                                super::super::expr::UcpScalar::Known((-10).into()),
                            ),
                        ),
                        UcpExpr::known_constant_i64(9),
                    ),
                ],
            );
            let mut values = UcpValueFacts::new();
            values.mark_domain(targets[0].clone(), domain(&[0, 1]));
            values.mark_domain(targets[1].clone(), domain(&(0..10).collect::<Vec<_>>()));
            let mut result = problem.analyze_with_values(UcpFacts::new(), values);
            let before = result.clone();
            let mut state = DomainRefinementState::new(PrivacyDomainRefinementOptions {
                max_solver_checks: 32,
                max_candidates_per_cell: 16,
            });
            assert_eq!(
                state.choose_cell(&targets, &problem, &result).unwrap(),
                Some(targets[1].clone())
            );
            assert!(state.planned_gain(&targets[1]).is_some());
            assert_eq!(result, before);
            let mut first_checks = Vec::new();
            let (_, narrowed, non_unique) = state
                .refine_domain(
                    &targets[1],
                    &result,
                    &problem.field_modulus,
                    &BTreeSet::new(),
                    |_, candidate, exclude| {
                        first_checks.push((candidate.clone(), exclude));
                        assert!(exclude || candidate == &domain(&[root]));
                        Ok(Satisfiability::Unsatisfiable)
                    },
                )
                .unwrap()
                .unwrap();
            assert_eq!(first_checks.len(), 1);
            assert!(first_checks.iter().all(|(_, exclude)| !exclude));
            assert!(!non_unique);
            assert_eq!(
                state.cells[&targets[1]].status,
                PrivateDomainRefinementStatus::Partial
            );
            assert_eq!(state.cells[&targets[1]].limitation, None);
            assert!(!canonical_candidates(&narrowed, &problem.field_modulus)
                .unwrap()
                .contains_key(&root.into()));
            assert!(state
                .choose_cell(&targets[1..2], &problem, &result)
                .unwrap()
                .is_none());
            result.value_facts.mark_domain(targets[1].clone(), narrowed);
            result = problem.analyze_with_values(result.facts, result.value_facts);
            assert_eq!(result.value_facts.known_value(&targets[2]), Some(&0.into()));
            state.observe_progress(1);
            // A szándékosan félbehagyott vizsgálatot a friss, független cél előtt folytatja.
            assert_eq!(
                state.choose_cell(&targets, &problem, &result).unwrap(),
                Some(targets[1].clone())
            );
            let mut resumed = Vec::new();
            let (_, refined, non_unique) = state
                .refine_domain(
                    &targets[1],
                    &result,
                    &problem.field_modulus,
                    &BTreeSet::new(),
                    |_, candidate, exclude| {
                        assert!(!exclude);
                        let value = candidate.exact_value().unwrap().clone();
                        assert_ne!(value, root.into());
                        resumed.push(value.clone());
                        Ok(if value == 1.into() || value == 9.into() {
                            Satisfiability::Satisfiable
                        } else {
                            Satisfiability::Unsatisfiable
                        })
                    },
                )
                .unwrap()
                .unwrap();
            assert_eq!(resumed.len(), 9);
            assert_eq!(refined, domain(&[1, 9]));
            assert!(non_unique);
            assert_eq!(
                state.cells[&targets[1]].status,
                PrivateDomainRefinementStatus::Complete
            );
            assert_eq!(state.statistics.solver_checks, 10);
            state.observe_progress(2);
            assert!(state
                .choose_cell(&targets[1..2], &problem, &result)
                .unwrap()
                .is_none());
        }
    }

    #[test]
    fn critical_probe_sat_or_unknown_never_causes_a_hypothetical_exclusion() {
        let targets = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let problem = problem(
            &targets,
            vec![UcpExpr::mul(
                UcpExpr::var(targets[1].clone()),
                UcpExpr::add(
                    UcpExpr::var(targets[0].clone()),
                    UcpExpr::known_constant_i64(-5),
                ),
            )],
        );
        let initial = domain(&(0..10).collect::<Vec<_>>());
        let mut values = UcpValueFacts::new();
        values.mark_domain(targets[0].clone(), initial.clone());
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        for feasible in [false, true] {
            let mut state = DomainRefinementState::new(PrivacyDomainRefinementOptions {
                max_solver_checks: 4,
                max_candidates_per_cell: 16,
            });
            assert_eq!(
                state.choose_cell(&targets, &problem, &result).unwrap(),
                Some(targets[0].clone())
            );
            let mut probes = Vec::new();
            let (_, refined, _) = state
                .refine_domain(
                    &targets[0],
                    &result,
                    &problem.field_modulus,
                    &BTreeSet::new(),
                    |_, candidate, exclude| {
                        if exclude {
                            return Ok(Satisfiability::Unsatisfiable);
                        }
                        probes.push(candidate.clone());
                        if feasible && candidate == &domain(&[5]) {
                            Ok(Satisfiability::Satisfiable)
                        } else {
                            Err(unknown())
                        }
                    },
                )
                .unwrap()
                .unwrap();
            assert_eq!(probes.len(), 4);
            assert_eq!(probes[0], domain(&[5]));
            assert_eq!(refined, initial);
            assert!(!state.attempts[&targets[0]].yielded);
            assert!(state
                .choose_cell(&targets, &problem, &result)
                .unwrap()
                .is_none());
        }
    }

    #[test]
    fn refinement_priority_prefers_a_complete_affordable_check_over_partial_high_gain() {
        let targets = [
            CellId::advice(0, 0),
            CellId::advice(1, 0),
            CellId::advice(2, 0),
        ];
        let problem = problem(
            &targets,
            vec![UcpExpr::mul(
                UcpExpr::var(targets[2].clone()),
                UcpExpr::add(
                    UcpExpr::var(targets[0].clone()),
                    UcpExpr::known_constant_i64(-5),
                ),
            )],
        );
        let mut values = UcpValueFacts::new();
        values.mark_domain(targets[0].clone(), domain(&[3, 5, 7]));
        values.mark_domain(targets[1].clone(), domain(&[0, 1]));
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        assert_eq!(refine_one(&targets, &problem, &result, 2).0, targets[1]);
    }

    #[test]
    fn refinement_priority_keeps_lookup_projections_in_its_simulations() {
        let targets = [
            CellId::advice(0, 0),
            CellId::advice(1, 0),
            CellId::advice(2, 0),
        ];
        let mut problem = problem(&targets, Vec::new());
        problem.expression_domains.push((
            UcpExpr::add(
                UcpExpr::var(targets[2].clone()),
                UcpExpr::neg(UcpExpr::var(targets[1].clone())),
            ),
            domain(&[0]),
        ));
        let mut values = UcpValueFacts::new();
        values.mark_domain(targets[0].clone(), domain(&[3, 4, 7]));
        values.mark_domain(targets[1].clone(), domain(&[3, 5, 7]));
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        assert_eq!(
            result.value_facts.domain(&targets[2]),
            Some(&domain(&[3, 5, 7]))
        );
        assert_eq!(refine_one(&targets, &problem, &result, 4).0, targets[1]);
    }

    #[test]
    fn refinement_priority_uses_field_cardinality_and_stable_cell_ties() {
        let targets = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let problem = problem(&targets, Vec::new());
        let mut values = UcpValueFacts::new();
        values.mark_domain(targets[0].clone(), domain(&[0, 1]));
        values.mark_domain(targets[1].clone(), domain(&[0, 1, 102]));
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        let reversed = [targets[1].clone(), targets[0].clone()];
        assert_eq!(refine_one(&reversed, &problem, &result, 3).0, targets[0]);
        // A teszt ellenőrzi, hogy egyetlen lefedési próbára elegendő keretnél nem módosítja spekulatív haszonnal a sorrendet.
        assert_eq!(refine_one(&reversed, &problem, &result, 1).0, targets[0]);
    }

    #[test]
    fn partial_budget_exports_a_superset_not_the_seen_feasible_subset() {
        let initial = domain(&[0, 1, 2, 3]);
        let (refined, evidence) = refine_domain(
            &initial,
            canonical_candidates(&initial, &101.into()).unwrap(),
            3,
            |candidate, exclude| {
                if exclude || candidate == &domain(&[0]) {
                    Ok(Satisfiability::Unsatisfiable)
                } else {
                    Ok(Satisfiability::Satisfiable)
                }
            },
        )
        .unwrap();
        assert_eq!(refined, domain(&[1, 2, 3]));
        assert_eq!(evidence.status, PrivateDomainRefinementStatus::Partial);
        assert_eq!(evidence.feasible_candidates, 1);
        assert_eq!(evidence.unresolved_candidates, 2);
        assert_eq!(evidence.solver_checks, 3);
        assert_eq!(evidence.limitation, Some(RecoveryLimitation::QueryLimit));
    }

    #[test]
    fn already_feasible_samples_are_not_queried_again_or_charged_again() {
        let initial = domain(&[0, 1, 2]);
        let known = BTreeSet::from([0.into(), 2.into()]);
        let mut checks = Vec::new();
        let (refined, evidence) = refine_domain_with_samples(
            &initial,
            canonical_candidates(&initial, &101.into()).unwrap(),
            2,
            &known,
            &mut RefinementAttempt::default(),
            |candidate, exclude| {
                checks.push((candidate.clone(), exclude));
                Ok(Satisfiability::Unsatisfiable)
            },
        )
        .unwrap();
        assert_eq!(checks, [(initial, true), (domain(&[1]), false)]);
        assert_eq!(refined, domain(&[0, 2]));
        assert_eq!(evidence.solver_checks, 2);
        assert_eq!(evidence.feasible_candidates, 2);
        assert_eq!(evidence.status, PrivateDomainRefinementStatus::Complete);
    }

    #[test]
    fn candidate_timeout_is_retained_and_does_not_hide_other_exclusions() {
        let initial = domain(&[0, 1, 2]);
        let (refined, evidence) = refine_domain(
            &initial,
            canonical_candidates(&initial, &101.into()).unwrap(),
            4,
            |candidate, exclude| {
                if exclude || candidate == &domain(&[2]) {
                    Ok(Satisfiability::Unsatisfiable)
                } else if candidate == &domain(&[0]) {
                    Err(unknown())
                } else {
                    Ok(Satisfiability::Satisfiable)
                }
            },
        )
        .unwrap();
        assert_eq!(refined, domain(&[0, 1]));
        assert_eq!(evidence.status, PrivateDomainRefinementStatus::Partial);
        assert_eq!(evidence.unresolved_candidates, 1);
        assert_eq!(evidence.limitation, Some(RecoveryLimitation::SolverTimeout));
    }

    #[test]
    fn coverage_timeout_exports_no_candidate_exclusions() {
        let initial = domain(&[0, 1]);
        let (refined, evidence) = refine_domain(
            &initial,
            canonical_candidates(&initial, &101.into()).unwrap(),
            3,
            |_, _| Err(unknown()),
        )
        .unwrap();
        assert_eq!(refined, initial);
        assert_eq!(
            evidence.status,
            PrivateDomainRefinementStatus::CoverageUnknown
        );
        assert_eq!(evidence.solver_checks, 1);
        assert_eq!(evidence.excluded_candidates, 0);
    }

    #[test]
    fn missing_feasible_candidates_and_total_exclusion_fail_closed() {
        let initial = domain(&[0, 1]);
        for outside_exists in [true, false] {
            let result = refine_domain(
                &initial,
                canonical_candidates(&initial, &101.into()).unwrap(),
                3,
                |_, exclude| {
                    Ok(if exclude && outside_exists {
                        Satisfiability::Satisfiable
                    } else {
                        Satisfiability::Unsatisfiable
                    })
                },
            );
            assert!(result.is_err());
        }
        assert!(refine_domain(
            &initial,
            canonical_candidates(&initial, &101.into()).unwrap(),
            3,
            |_, _| Err(anyhow::anyhow!("malformed solver output"))
        )
        .is_err());
    }

    #[test]
    fn field_aliases_count_once_and_a_covering_singleton_is_exact() {
        let initial = domain(&[-1, 12, 0]);
        let candidates = canonical_candidates(&initial, &13.into()).unwrap();
        assert_eq!(candidates.len(), 2);
        let (refined, evidence) = refine_domain(&initial, candidates, 3, |candidate, exclude| {
            if exclude || candidate == &domain(&[0]) {
                Ok(Satisfiability::Unsatisfiable)
            } else {
                Err(unknown())
            }
        })
        .unwrap();
        assert_eq!(refined, domain(&[-1]));
        assert_eq!(evidence.status, PrivateDomainRefinementStatus::Complete);
        assert_eq!(evidence.feasible_candidates, 1);
        assert_eq!(evidence.unresolved_candidates, 0);
    }

    #[test]
    fn eligibility_and_total_check_budget_never_reset() {
        let cells = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let mut values = UcpValueFacts::new();
        for cell in &cells {
            values.mark_domain(cell.clone(), domain(&[0, 1, 2]));
        }
        let mut state = DomainRefinementState::new(PrivacyDomainRefinementOptions {
            max_solver_checks: 2,
            max_candidates_per_cell: 2,
        });
        let problem = problem(&cells, Vec::new());
        assert!(state
            .refine_next(
                &cells,
                &problem,
                &problem.analyze_with_values(UcpFacts::new(), values.clone()),
                |_, _, _| unreachable!()
            )
            .unwrap()
            .is_none());
        values.mark_domain(cells[0].clone(), domain(&[0, 1]));
        let mut calls = 0;
        assert!(state
            .refine_next(
                &cells,
                &problem,
                &problem.analyze_with_values(UcpFacts::new(), values.clone()),
                |_, _, _| {
                    calls += 1;
                    Err(unknown())
                }
            )
            .unwrap()
            .is_some());
        values.mark_domain(cells[1].clone(), domain(&[0, 1]));
        assert!(state
            .refine_next(
                &cells,
                &problem,
                &problem.analyze_with_values(UcpFacts::new(), values.clone()),
                |_, _, _| unreachable!()
            )
            .unwrap()
            .is_none());
        assert_eq!(calls, 2);
        assert_eq!(state.statistics.solver_checks, 2);
        assert!(state.statistics.budget_exhausted);
    }

    #[test]
    fn partial_refinement_resumes_after_progress_without_rechecking_proven_values() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&[cell.clone()], Vec::new());
        let mut values = UcpValueFacts::new();
        values.mark_domain(cell.clone(), domain(&[0, 1, 2]));
        let mut result = problem.analyze_with_values(UcpFacts::new(), values);
        let mut state = DomainRefinementState::new(PrivacyDomainRefinementOptions {
            max_solver_checks: 10,
            max_candidates_per_cell: 3,
        });
        let (_, refined, _) = state
            .refine_next(
                &[cell.clone()],
                &problem,
                &result,
                |_, candidate, exclude| {
                    if exclude || candidate == &domain(&[2]) {
                        Ok(Satisfiability::Unsatisfiable)
                    } else if candidate == &domain(&[0]) {
                        Err(unknown())
                    } else {
                        Ok(Satisfiability::Satisfiable)
                    }
                },
            )
            .unwrap()
            .unwrap();
        result.value_facts.mark_domain(cell.clone(), refined);
        assert_eq!(
            state.cells[&cell].status,
            PrivateDomainRefinementStatus::Partial
        );
        assert_eq!(state.statistics.solver_checks, 3);
        assert!(state
            .refine_next(&[cell.clone()], &problem, &result, |_, _, _| unreachable!())
            .unwrap()
            .is_none());
        assert!(state
            .refine_domain(
                &cell,
                &result,
                &101.into(),
                &BTreeSet::new(),
                |_, _, _| unreachable!()
            )
            .unwrap()
            .is_none());

        state.observe_progress(1);
        let (_, refined, non_unique) = state
            .refine_next(
                &[cell.clone()],
                &problem,
                &result,
                |_, candidate, exclude| {
                    assert!(
                        !exclude,
                        "Original coverage minus proven exclusions is reusable"
                    );
                    assert_eq!(candidate, &domain(&[0]));
                    Ok(Satisfiability::Satisfiable)
                },
            )
            .unwrap()
            .unwrap();
        assert_eq!(refined, domain(&[0, 1]));
        assert!(non_unique);
        assert_eq!(
            state.cells[&cell].status,
            PrivateDomainRefinementStatus::Complete
        );
        assert_eq!(state.cells[&cell].solver_checks, 4);
        assert_eq!(state.cells[&cell].limitation, None);
        assert_eq!(state.statistics.solver_checks, 4);
        assert_eq!(state.statistics.attempted_cells, 1);
        assert_eq!(state.statistics.complete_domains, 1);
        assert_eq!(state.statistics.removed_candidates, 1);
        state.observe_progress(2);
        assert!(state
            .choose_cell(&[cell], &problem, &result)
            .unwrap()
            .is_none());
    }

    #[test]
    fn fresh_cells_and_older_attempts_precede_recent_retries() {
        let cells = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let problem = problem(&cells, Vec::new());
        let mut values = UcpValueFacts::new();
        for cell in &cells {
            values.mark_domain(cell.clone(), domain(&[0, 1]));
        }
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        let mut state = DomainRefinementState::new(PrivacyDomainRefinementOptions {
            max_solver_checks: 32,
            max_candidates_per_cell: 2,
        });
        let mut visited = Vec::new();
        for generation in [0, 1, 1, 2, 2] {
            state.observe_progress(generation);
            let (cell, _, _) = state
                .refine_next(&cells, &problem, &result, |_, _, exclude| {
                    if exclude {
                        Ok(Satisfiability::Unsatisfiable)
                    } else {
                        Err(unknown())
                    }
                })
                .unwrap()
                .unwrap();
            visited.push(cell);
        }
        assert_eq!(
            visited,
            [
                cells[0].clone(),
                cells[1].clone(),
                cells[0].clone(),
                cells[1].clone(),
                cells[0].clone()
            ]
        );
        assert!(state
            .refine_next(&cells, &problem, &result, |_, _, _| unreachable!())
            .unwrap()
            .is_none());
        assert_eq!(state.statistics.attempted_cells, 2);
        assert_eq!(state.statistics.solver_checks, 10);
        assert_eq!(state.cells[&cells[0]].solver_checks, 6);
        assert_eq!(state.cells[&cells[1]].solver_checks, 4);
    }

    #[test]
    fn progress_never_resets_the_refinement_allowance() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&[cell.clone()], Vec::new());
        let mut values = UcpValueFacts::new();
        values.mark_domain(cell.clone(), domain(&[0, 1]));
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        let mut state = DomainRefinementState::new(PrivacyDomainRefinementOptions {
            max_solver_checks: 2,
            max_candidates_per_cell: 2,
        });
        state
            .refine_next(&[cell.clone()], &problem, &result, |_, _, exclude| {
                if exclude {
                    Ok(Satisfiability::Unsatisfiable)
                } else {
                    Err(unknown())
                }
            })
            .unwrap()
            .unwrap();
        for generation in 1..4 {
            state.observe_progress(generation);
            assert!(state
                .refine_next(&[cell.clone()], &problem, &result, |_, _, _| unreachable!())
                .unwrap()
                .is_none());
            assert!(state
                .refine_domain(
                    &cell,
                    &result,
                    &101.into(),
                    &BTreeSet::new(),
                    |_, _, _| unreachable!()
                )
                .unwrap()
                .is_none());
        }
        assert_eq!(state.statistics.solver_checks, 2);
        assert!(state.statistics.budget_exhausted);
    }

    #[test]
    fn candidate_timeouts_are_retryable_only_after_progress_without_coverage_checks() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&[cell.clone()], Vec::new());
        let mut values = UcpValueFacts::new();
        values.mark_domain(cell.clone(), domain(&[0, 1]));
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        let mut state = DomainRefinementState::new(PrivacyDomainRefinementOptions {
            max_solver_checks: 4,
            max_candidates_per_cell: 2,
        });
        state
            .refine_next(&[cell.clone()], &problem, &result, |_, _, exclude| {
                assert!(!exclude);
                Err(unknown())
            })
            .unwrap()
            .unwrap();
        assert!(state
            .choose_cell(&[cell.clone()], &problem, &result)
            .unwrap()
            .is_none());
        state.observe_progress(1);
        let mut coverage_checks = 0;
        state
            .refine_next(&[cell.clone()], &problem, &result, |_, _, exclude| {
                if exclude {
                    coverage_checks += 1;
                    Ok(Satisfiability::Unsatisfiable)
                } else {
                    Ok(Satisfiability::Satisfiable)
                }
            })
            .unwrap()
            .unwrap();
        assert_eq!(coverage_checks, 0);
        assert_eq!(
            state.cells[&cell].status,
            PrivateDomainRefinementStatus::Complete
        );
        assert_eq!(state.cells[&cell].solver_checks, 4);
        assert_eq!(state.statistics.solver_checks, 4);
    }

    #[test]
    fn propagated_covering_domain_is_reused_without_becoming_complete_from_coverage_alone() {
        let cell = CellId::advice(0, 0);
        let problem = problem(&[cell.clone()], Vec::new());
        let mut values = UcpValueFacts::new();
        values.mark_domain(cell.clone(), domain(&[0, 1, 2]));
        let mut result = problem.analyze_with_values(UcpFacts::new(), values);
        let mut state = DomainRefinementState::new(PrivacyDomainRefinementOptions {
            max_solver_checks: 5,
            max_candidates_per_cell: 3,
        });
        let (_, retained, non_unique) = state
            .refine_next(&[cell.clone()], &problem, &result, |_, _, exclude| {
                assert!(!exclude);
                Err(unknown())
            })
            .unwrap()
            .unwrap();
        assert_eq!(retained, domain(&[0, 1, 2]));
        assert!(!non_unique);
        assert_eq!(
            state.cells[&cell].status,
            PrivateDomainRefinementStatus::Partial
        );
        assert_eq!(state.cells[&cell].feasible_candidates, 0);
        assert!(!result.value_facts.domain_is_complete(&cell));

        // Az új valódi Delta-domain lefedését akkor is elfogadja, ha nem régi SMT-kizárásból származik.
        result
            .value_facts
            .mark_domain(cell.clone(), domain(&[0, 1]));
        state.observe_progress(1);
        let (_, refined, non_unique) = state
            .refine_next(
                &[cell.clone()],
                &problem,
                &result,
                |_, candidate, exclude| {
                    assert!(!exclude);
                    assert!([domain(&[0]), domain(&[1])].contains(candidate));
                    Ok(Satisfiability::Satisfiable)
                },
            )
            .unwrap()
            .unwrap();
        assert_eq!(refined, domain(&[0, 1]));
        assert!(non_unique);
        assert_eq!(
            state.cells[&cell].status,
            PrivateDomainRefinementStatus::Complete
        );
        assert_eq!(state.statistics.solver_checks, 5);
    }

    #[test]
    fn unverified_domain_changes_require_an_independent_coverage_check() {
        let initial = domain(&[0, 1, 2]);
        let mut attempt = RefinementAttempt::default();
        refine_domain_with_samples(
            &initial,
            canonical_candidates(&initial, &101.into()).unwrap(),
            4,
            &BTreeSet::new(),
            &mut attempt,
            |candidate, exclude| {
                if exclude {
                    Ok(Satisfiability::Unsatisfiable)
                } else if candidate == &domain(&[0]) {
                    Ok(Satisfiability::Satisfiable)
                } else {
                    Err(unknown())
                }
            },
        )
        .unwrap();
        let narrower = domain(&[0, 1]);
        let error = refine_domain_with_samples(
            &narrower,
            canonical_candidates(&narrower, &101.into()).unwrap(),
            2,
            &BTreeSet::new(),
            &mut attempt,
            |candidate, exclude| {
                assert!(
                    exclude,
                    "A propagated exclusion is not an original-context coverage certificate"
                );
                assert_eq!(candidate, &narrower);
                Ok(Satisfiability::Satisfiable)
            },
        )
        .unwrap_err();
        assert!(error.to_string().contains("does not cover"));
    }

    #[test]
    fn cached_feasibility_cannot_be_removed_by_a_later_domain() {
        let initial = domain(&[0, 1]);
        let mut attempt = RefinementAttempt::default();
        refine_domain_with_samples(
            &initial,
            canonical_candidates(&initial, &101.into()).unwrap(),
            3,
            &BTreeSet::new(),
            &mut attempt,
            |candidate, exclude| {
                if exclude {
                    Ok(Satisfiability::Unsatisfiable)
                } else if candidate == &domain(&[0]) {
                    Ok(Satisfiability::Satisfiable)
                } else {
                    Err(unknown())
                }
            },
        )
        .unwrap();
        let invalid = domain(&[1]);
        assert!(refine_domain_with_samples(
            &invalid,
            canonical_candidates(&invalid, &101.into()).unwrap(),
            3,
            &BTreeSet::new(),
            &mut attempt,
            |_, _| unreachable!(),
        )
        .unwrap_err()
        .to_string()
        .contains("previously feasible"));
    }
}
