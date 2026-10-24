#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

//! Joint cell/operation scheduling. Hypothetical gain never becomes analysis evidence.
use super::{
    cell::CellId,
    engine::UcpResult,
    extractor::UcpProblem,
    privacy::domain_refined,
    privacy_domain::refinement_has_target_gain,
    value::{normalize_field_value, UcpValueDomain},
};
use anyhow::{Context, Result};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

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

/// The caller has checked the probe allowance, retry eligibility, and target reservations.
/// Refine chooses its strategy; Discover keeps enumeration whenever it is available.
pub(crate) fn integrate_fast_probe(
    actions: &mut Vec<RecoveryAction>,
    cell: &CellId,
    problem: &UcpProblem,
    result: &UcpResult,
    evidence: &RecoveryEvidence,
    discovery_available: bool,
) {
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
            // A bounded exact-only attempt is still available when enumeration is disabled or done.
            RecoveryAction::Discover(cell.clone(), RecoveryStrategy::FastProbe)
        }
    };
    if let Some(index) = existing {
        actions[index] = action;
    } else {
        actions.push(action);
    }
}

pub(crate) fn choose_action(
    mut actions: Vec<RecoveryAction>,
    targets: &[CellId],
    problem: &UcpProblem,
    result: &UcpResult,
    evidence: &RecoveryEvidence,
) -> Option<RecoveryAction> {
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
            let simulated = problem.analyze_with_values(facts, result.value_facts.clone());
            let gain = 1 + targets
                .iter()
                .filter(|target| {
                    !result.facts.is_unique(target) && simulated.facts.is_unique(target)
                })
                .count();
            let target = targets.contains(cell);
            let known_unique = target && result.facts.is_unique(cell);
            // Domain completion is preferred to re-proving non-uniqueness from already seen samples.
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
            initial_facts: UcpFacts::new(),
            target_cells: vec![cell.clone()],
            output_cells: vec![cell.clone()],
            witness_cells: vec![cell.clone()],
            initial_value_facts: UcpValueFacts::new(),
            field_modulus: 101.into(),
        }
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
    if matches!(
        result.value_facts.domain(cell),
        Some(UcpValueDomain::FiniteSet(_))
    ) {
        return refinement_has_target_gain(cell, targets, problem, result);
    }
    let mut facts = result.facts.clone();
    facts.mark_unique(cell.clone());
    let simulated = problem.analyze_with_values(facts, result.value_facts.clone());
    Ok(targets.iter().any(|target| {
        (!result.facts.is_unique(target) && simulated.facts.is_unique(target))
            || domain_refined(
                result.value_facts.domain(target),
                simulated.value_facts.domain(target),
                &problem.field_modulus,
            )
    }))
}
