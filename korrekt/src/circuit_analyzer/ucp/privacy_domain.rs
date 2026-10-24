#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

//! Bounded refinement of existing finite supersets, scheduled by cost and simulated domain gain.
//! Coverage and candidate feasibility are different claims; partial results remain supersets.

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

pub(crate) const PRIVACY_DOMAIN_REFINEMENT_POLICY: &str =
    "coverage-candidate-feasibility-cost-domain-gain-v2";

const MAX_REFINEMENT_SCORED_CELLS: usize = 32;
const MAX_REFINEMENT_SIMULATIONS_PER_CELL: usize = 4;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrivacyDomainRefinementOptions {
    /// Separate hard cap on actual solver invocations, including coverage checks. Zero disables.
    pub max_solver_checks: usize,
    /// Only already inferred finite sets at or below this size are examined.
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
    /// Coverage verified and every remaining candidate feasible in the original context.
    Complete,
    /// Coverage verified; untested/unknown candidates remain possible, not proven feasible.
    Partial,
    /// No refinement exported: the original covering claim could not be checked.
    CoverageUnknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrivateDomainRefinement {
    pub status: PrivateDomainRefinementStatus,
    pub solver_checks: usize,
    /// Counts distinct field elements, not different integer representatives.
    pub candidate_count: usize,
    pub excluded_candidates: usize,
    pub feasible_candidates: usize,
    pub unresolved_candidates: usize,
    /// Additional domain-search limitation, independent of the uniqueness result.
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
}

impl DomainRefinementState {
    pub fn new(options: PrivacyDomainRefinementOptions) -> Self {
        Self {
            options,
            statistics: Default::default(),
            cells: BTreeMap::new(),
        }
    }

    /// One attempt per selected cell; later propagation can make additional cells eligible.
    pub fn refine_next(
        &mut self,
        private_cells: &[CellId],
        problem: &UcpProblem,
        result: &UcpResult,
        mut check: impl FnMut(&CellId, &UcpValueDomain, bool) -> Result<Satisfiability>,
    ) -> Result<Option<(CellId, UcpValueDomain, bool)>> {
        if self.options.max_solver_checks == 0 {
            return Ok(None);
        }
        let mut eligible = Vec::new();
        for cell in private_cells {
            if self.cells.contains_key(cell) {
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
            eligible.push(RefinementCandidate {
                cell,
                domain,
                candidates,
            });
        }
        if eligible.is_empty() {
            return Ok(None);
        }
        let remaining = self.options.max_solver_checks - self.statistics.solver_checks;
        if remaining == 0 {
            self.statistics.budget_exhausted = true;
            return Ok(None);
        }
        // Cheap shortlisting bounds UCP simulation work; all unselected cells remain eligible.
        eligible.sort_by_key(|candidate| {
            (
                candidate.candidates.len() + 1 > remaining,
                candidate.candidates.len(),
                candidate.cell,
            )
        });
        let selected = if remaining == 1 || eligible.len() == 1 {
            0
        } else {
            eligible
                .iter()
                .take(MAX_REFINEMENT_SCORED_CELLS)
                .enumerate()
                .map(|(index, candidate)| {
                    (
                        index,
                        score_refinement(candidate, private_cells, problem, result, remaining),
                    )
                })
                .max_by(|(_, left), (_, right)| left.compare(right))
                .unwrap()
                .0
        };
        let RefinementCandidate {
            cell,
            domain,
            candidates,
        } = eligible.swap_remove(selected);
        let (refined, evidence) =
            refine_domain(domain, candidates, remaining, |domain, exclude| {
                check(cell, domain, exclude)
            })?;
        self.statistics.solver_checks += evidence.solver_checks;
        self.statistics.attempted_cells += 1;
        self.statistics.complete_domains +=
            usize::from(evidence.status == PrivateDomainRefinementStatus::Complete);
        self.statistics.removed_candidates += evidence.excluded_candidates;
        self.statistics.budget_exhausted |=
            evidence.limitation == Some(RecoveryLimitation::QueryLimit);
        // Two SAT candidate checks certify non-uniqueness even if the remaining search is partial.
        let non_unique = evidence.feasible_candidates >= 2;
        self.cells.insert(cell.clone(), evidence);
        Ok(Some((cell.clone(), refined, non_unique)))
    }
}

struct RefinementCandidate<'a> {
    cell: &'a CellId,
    domain: &'a UcpValueDomain,
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
}

impl RefinementScore<'_> {
    fn compare(&self, other: &Self) -> Ordering {
        let rate = |left: usize, right: usize| {
            ((left as u128) * (other.simulations * other.checks) as u128)
                .cmp(&((right as u128) * (self.simulations * self.checks) as u128))
        };
        self.fits_budget
            .cmp(&other.fits_budget)
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
    let simulations = count.min(MAX_REFINEMENT_SIMULATIONS_PER_CELL);
    let mut score = RefinementScore {
        cell: candidate.cell,
        fits_budget: count + 1 <= remaining,
        checks: count + 1,
        simulations,
        exact_targets: 0,
        refined_targets: 0,
        unique_targets: 0,
        refined_cells: 0,
        unique_cells: 0,
    };
    for trial in 0..simulations {
        let removed = if simulations == 1 {
            0
        } else {
            trial * (count - 1) / (simulations - 1)
        };
        let hypothetical = UcpValueDomain::finite_set(
            candidate
                .candidates
                .values()
                .enumerate()
                // Field-equivalent singleton candidates need only canonicalization.
                .filter(|(index, _)| count == 1 || *index != removed)
                .map(|(_, value)| value.clone()),
        )
        .expect("A simulated refinement retains at least one candidate");
        let mut values = result.value_facts.clone();
        values.mark_domain(candidate.cell.clone(), hypothetical);
        // Hypothetical exclusions are used only for ranking, never as recovered facts.
        let simulated = problem.analyze_with_values(result.facts.clone(), values);
        for target in targets {
            score.exact_targets += usize::from(
                result.value_facts.known_value(target).is_none()
                    && simulated.value_facts.known_value(target).is_some(),
            );
            score.refined_targets += usize::from(domain_refined(
                result.value_facts.domain(target),
                simulated.value_facts.domain(target),
                &problem.field_modulus,
            ));
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
    }
    score
}

// Keep original representatives for Delta intersections, deduplicating modulo the actual field.
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

fn refine_domain(
    domain: &UcpValueDomain,
    candidates: BTreeMap<BigInt, BigInt>,
    max_checks: usize,
    mut check: impl FnMut(&UcpValueDomain, bool) -> Result<Satisfiability>,
) -> Result<(UcpValueDomain, PrivateDomainRefinement)> {
    let mut evidence = PrivateDomainRefinement {
        status: PrivateDomainRefinementStatus::CoverageUnknown,
        solver_checks: 1,
        candidate_count: candidates.len(),
        excluded_candidates: 0,
        feasible_candidates: 0,
        unresolved_candidates: candidates.len(),
        limitation: None,
    };
    // Never assume the proposed domain while verifying that it contains all original solutions.
    match check(domain, true) {
        Ok(Satisfiability::Unsatisfiable) => {}
        Ok(Satisfiability::Satisfiable) => {
            anyhow::bail!("Finite candidate domain does not cover the original circuit")
        }
        Err(error) => {
            evidence.limitation = Some(limitation_from_solver_error(error)?);
            return Ok((domain.clone(), evidence));
        }
    }
    evidence.status = PrivateDomainRefinementStatus::Partial;
    let mut excluded = BTreeSet::new();
    let mut feasible = BTreeSet::new();
    for value in candidates.keys() {
        if evidence.solver_checks >= max_checks {
            evidence.limitation = Some(RecoveryLimitation::QueryLimit);
            break;
        }
        evidence.solver_checks += 1;
        match check(&UcpValueDomain::exact(value.clone()), false) {
            Ok(Satisfiability::Unsatisfiable) => {
                excluded.insert(value.clone());
            }
            Ok(Satisfiability::Satisfiable) => {
                feasible.insert(value.clone());
            }
            Err(error) => {
                evidence.limitation = Some(limitation_from_solver_error(error)?);
            }
        }
    }
    let retained: Vec<_> = candidates
        .iter()
        .filter(|(value, _)| !excluded.contains(*value))
        .collect();
    ensure!(
        !retained.is_empty(),
        "Candidate exclusion contradicts the originally satisfiable circuit"
    );
    // Original SAT + covering singleton already proves its feasibility, even without a SAT answer.
    if retained.len() == 1 {
        feasible.insert(retained[0].0.clone());
    }
    evidence.excluded_candidates = excluded.len();
    evidence.feasible_candidates = feasible.len();
    evidence.unresolved_candidates = retained.len() - feasible.len();
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
        assert_eq!(non_unique, actual_checks >= 3);
        (cell, state)
    }

    #[test]
    fn refinement_priority_prefers_a_cheaper_later_cell_and_preserves_the_hard_cap() {
        let targets = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let problem = problem(&targets, Vec::new());
        let mut values = UcpValueFacts::new();
        values.mark_domain(targets[0].clone(), domain(&[0, 1, 2, 3]));
        values.mark_domain(targets[1].clone(), domain(&[0, 1]));
        let result = problem.analyze_with_values(UcpFacts::new(), values);
        let (selected, mut state) = refine_one(&targets, &problem, &result, 3);
        assert_eq!(selected, targets[1]);
        assert_eq!(state.statistics.solver_checks, 3);
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
        // Excluding 5 leaves a non-singleton domain but would make the dependent product zero.
        let (selected, _) = refine_one(&targets, &problem, &result, 4);
        assert_eq!(selected, targets[1]);
        assert!(!result.facts.is_unique(&targets[1]));
        assert!(result.value_facts.domain(&targets[2]).is_none());
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
        assert_eq!(refine_one(&targets, &problem, &result, 3).0, targets[1]);
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
        // With only a coverage check left, no speculative gain justifies changing the cheap ordering.
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
                    Ok(Satisfiability::Unsatisfiable)
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
}
