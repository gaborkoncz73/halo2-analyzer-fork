#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

//! Bounded refinement of existing finite supersets against original constraints only.
//! Coverage and candidate feasibility are different claims; partial results remain supersets.

use super::{
    cell::CellId,
    privacy::{limitation_from_solver_error, RecoveryLimitation},
    value::{normalize_field_value, UcpValueDomain, UcpValueFacts, MAX_FINITE_DOMAIN_SIZE},
};
use crate::smt_solver::smt_parser::Satisfiability;
use anyhow::{ensure, Context, Result};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) const PRIVACY_DOMAIN_REFINEMENT_POLICY: &str =
    "original-coverage-and-candidate-feasibility-v1";

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
        values: &UcpValueFacts,
        modulus: &BigInt,
        mut check: impl FnMut(&CellId, &UcpValueDomain, bool) -> Result<Satisfiability>,
    ) -> Result<Option<(CellId, UcpValueDomain, bool)>> {
        if self.options.max_solver_checks == 0 {
            return Ok(None);
        }
        for cell in private_cells {
            if self.cells.contains_key(cell) {
                continue;
            }
            let Some(domain @ UcpValueDomain::FiniteSet(_)) = values.domain(cell) else {
                continue;
            };
            let candidates = canonical_candidates(domain, modulus)?;
            if candidates.len() > self.options.max_candidates_per_cell {
                continue;
            }
            let remaining = self.options.max_solver_checks - self.statistics.solver_checks;
            if remaining == 0 {
                self.statistics.budget_exhausted = true;
                return Ok(None);
            }
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
            return Ok(Some((cell.clone(), refined, non_unique)));
        }
        Ok(None)
    }
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
        assert!(state
            .refine_next(&cells, &values, &101.into(), |_, _, _| unreachable!())
            .unwrap()
            .is_none());
        values.mark_domain(cells[0].clone(), domain(&[0, 1]));
        let mut calls = 0;
        assert!(state
            .refine_next(&cells, &values, &101.into(), |_, _, _| {
                calls += 1;
                Ok(Satisfiability::Unsatisfiable)
            })
            .unwrap()
            .is_some());
        values.mark_domain(cells[1].clone(), domain(&[0, 1]));
        assert!(state
            .refine_next(&cells, &values, &101.into(), |_, _, _| unreachable!())
            .unwrap()
            .is_none());
        assert_eq!(calls, 2);
        assert_eq!(state.statistics.solver_checks, 2);
        assert!(state.statistics.budget_exhausted);
    }
}
