#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

//! Discover small complete cell projections without a pre-existing Delta domain.
//! SAT samples always come from the original context. A literal subset may prove exhaustion.

use super::{
    cell::CellId,
    choose_var::choose_query_cell,
    engine::UcpResult,
    expr::UcpExpr,
    privacy::{limitation_from_solver_error, RecoveryLimitation},
    value::{normalize_field_value, UcpValueDomain, MAX_FINITE_DOMAIN_SIZE},
};
use anyhow::{ensure, Context, Result};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet, HashSet};

pub(crate) const PRIVACY_DOMAIN_DISCOVERY_POLICY: &str =
    "original-fair-subset-exclusion-resumable-v3";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DiscoveryProbe {
    Full,
    SubsetExclusion,
}

pub(crate) enum DiscoveryResponse {
    Full(Option<BigInt>),
    FullUnknown(RecoveryLimitation),
    SubsetUnsat,
    SubsetFallback { unknown: bool },
}

pub(crate) fn full_discovery_response(answer: Result<Option<BigInt>>) -> Result<DiscoveryResponse> {
    match answer {
        Ok(value) => Ok(DiscoveryResponse::Full(value)),
        Err(error) => Ok(DiscoveryResponse::FullUnknown(
            limitation_from_solver_error(error)?,
        )),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrivacyDomainDiscoveryOptions {
    /// Separate hard total on solver invocations. Zero disables discovery.
    pub max_solver_checks: usize,
    /// At most this many samples are retained; a final exhaustion probe is still allowed.
    pub max_values_per_cell: usize,
    /// Check quantum per cell before every other eligible cell gets the same allowance.
    pub max_checks_per_round: usize,
    /// Retries of inconclusive checks only, not continuation after a SAT sample.
    pub max_retries_per_cell: usize,
    /// Inconclusive checks can resume only with a strictly larger per-process budget.
    /// None disables budget escalation; the uniqueness retry floor is not inherited.
    pub retry_solver_timeout_ms: Option<u64>,
    /// Opt-in literal original subsets for exclusion only; SAT samples remain full-model.
    pub use_targeted_subsets: bool,
}

impl Default for PrivacyDomainDiscoveryOptions {
    fn default() -> Self {
        Self {
            max_solver_checks: 0,
            max_values_per_cell: 16,
            max_checks_per_round: 1,
            max_retries_per_cell: 1,
            retry_solver_timeout_ms: None,
            use_targeted_subsets: false,
        }
    }
}

impl PrivacyDomainDiscoveryOptions {
    pub(crate) fn validate(&self) -> Result<()> {
        ensure!(
            self.max_solver_checks == 0
                || (1..=MAX_FINITE_DOMAIN_SIZE).contains(&self.max_values_per_cell),
            "Enabled domain discovery requires 1..={} values per cell",
            MAX_FINITE_DOMAIN_SIZE
        );
        ensure!(
            self.max_solver_checks == 0 || self.max_checks_per_round > 0,
            "Enabled domain discovery requires at least one check per round"
        );
        ensure!(
            self.retry_solver_timeout_ms != Some(0),
            "Domain discovery retry timeout must be greater than zero"
        );
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrivateDomainDiscoveryStatus {
    /// All possible target values were enumerated; the final blocked-value query was UNSAT.
    Complete,
    /// Observed values are feasible samples only, never a complete candidate superset.
    Partial,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrivateDomainDiscovery {
    pub status: PrivateDomainDiscoveryStatus,
    pub solver_checks: usize,
    /// These partition solver_checks. A subset SAT never contributes a model sample.
    pub full_solver_checks: usize,
    pub subset_solver_checks: usize,
    pub subset_fallbacks: usize,
    pub subset_unknown_checks: usize,
    pub subset_unsat_proofs: usize,
    /// Includes a possible overflow probe beyond the retained-sample limit.
    pub models_found: usize,
    /// Feasible values imported from other full-model search operations, not extra solver calls.
    pub reused_values: usize,
    /// Included in solver_checks, not an additional count.
    pub retry_checks: usize,
    /// Not a Delta domain unless status is Complete. No joint witness claim across cells.
    pub observed_values: BTreeSet<BigInt>,
    pub witnessed_non_unique: bool,
    pub limitation: Option<RecoveryLimitation>,
}

impl Default for PrivateDomainDiscovery {
    fn default() -> Self {
        Self {
            status: PrivateDomainDiscoveryStatus::Partial,
            solver_checks: 0,
            full_solver_checks: 0,
            subset_solver_checks: 0,
            subset_fallbacks: 0,
            subset_unknown_checks: 0,
            subset_unsat_proofs: 0,
            models_found: 0,
            reused_values: 0,
            retry_checks: 0,
            observed_values: BTreeSet::new(),
            witnessed_non_unique: false,
            limitation: None,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PrivacyDomainDiscoveryStatistics {
    pub solver_checks: usize,
    pub full_solver_checks: usize,
    pub subset_solver_checks: usize,
    pub subset_fallbacks: usize,
    pub subset_unknown_checks: usize,
    pub subset_unsat_proofs: usize,
    pub models_found: usize,
    pub reused_values: usize,
    pub attempted_cells: usize,
    pub complete_domains: usize,
    /// Checks after a cell's first check, including any retries.
    pub resumed_checks: usize,
    /// A subset of resumed_checks and solver_checks.
    pub retry_checks: usize,
    pub budget_exhausted: bool,
}

pub(crate) struct DomainDiscoveryState {
    options: PrivacyDomainDiscoveryOptions,
    pub cells: BTreeMap<CellId, PrivateDomainDiscovery>,
    pub statistics: PrivacyDomainDiscoveryStatistics,
    timeouts: BTreeMap<CellId, Option<u64>>,
    pending_full: BTreeSet<CellId>,
}

impl DomainDiscoveryState {
    pub fn new(options: PrivacyDomainDiscoveryOptions) -> Self {
        Self {
            options,
            cells: BTreeMap::new(),
            statistics: Default::default(),
            timeouts: BTreeMap::new(),
            pending_full: BTreeSet::new(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    #[cfg(test)]
    pub fn discover_next(
        &mut self,
        private_cells: &[CellId],
        expressions: &[UcpExpr],
        result: &UcpResult,
        modulus: &BigInt,
        initial_timeout_ms: Option<u64>,
        mut query: impl FnMut(&CellId, &BTreeSet<BigInt>, Option<u64>) -> Result<Option<BigInt>>,
    ) -> Result<Option<(CellId, Option<UcpValueDomain>, bool)>> {
        self.discover_next_with_subsets(
            private_cells,
            expressions,
            result,
            modulus,
            initial_timeout_ms,
            |cell, blocked, timeout, _| full_discovery_response(query(cell, blocked, timeout)),
        )
    }

    /// One actual check per step, including subset probes and deferred full fallbacks.
    #[allow(clippy::too_many_arguments)]
    #[cfg(test)]
    pub fn discover_next_with_subsets(
        &mut self,
        private_cells: &[CellId],
        expressions: &[UcpExpr],
        result: &UcpResult,
        modulus: &BigInt,
        initial_timeout_ms: Option<u64>,
        mut query: impl FnMut(
            &CellId,
            &BTreeSet<BigInt>,
            Option<u64>,
            DiscoveryProbe,
        ) -> Result<DiscoveryResponse>,
    ) -> Result<Option<(CellId, Option<UcpValueDomain>, bool)>> {
        let Some(cell) = self.choose_cell(
            private_cells,
            expressions,
            result,
            modulus,
            initial_timeout_ms,
        ) else {
            return Ok(None);
        };
        self.discover_domain(
            &cell,
            modulus,
            initial_timeout_ms,
            |cell, blocked, timeout, probe| query(cell, blocked, timeout, probe),
        )
    }

    pub(crate) fn remember_samples(&mut self, cell: &CellId, samples: &BTreeSet<BigInt>) {
        if samples.is_empty() || self.options.max_solver_checks == 0 {
            return;
        }
        let evidence = self.cells.entry(cell.clone()).or_default();
        let before = evidence.observed_values.len();
        evidence.witnessed_non_unique |= evidence.observed_values.union(samples).count() >= 2;
        for sample in samples {
            if evidence.observed_values.contains(sample) {
                continue;
            }
            if evidence.observed_values.len() == self.options.max_values_per_cell {
                evidence.limitation = Some(RecoveryLimitation::DomainSizeLimit);
                break;
            }
            evidence.observed_values.insert(sample.clone());
        }
        let added = evidence.observed_values.len() - before;
        evidence.reused_values += added;
        self.statistics.reused_values += added;
    }

    pub(crate) fn can_discover(
        &self,
        cell: &CellId,
        result: &UcpResult,
        initial_timeout_ms: Option<u64>,
    ) -> bool {
        self.statistics.solver_checks < self.options.max_solver_checks
            && result.value_facts.domain(cell).is_none()
            && self.next_timeout(cell, initial_timeout_ms).is_some()
    }

    pub(crate) fn choose_cell(
        &mut self,
        private_cells: &[CellId],
        expressions: &[UcpExpr],
        result: &UcpResult,
        modulus: &BigInt,
        initial_timeout_ms: Option<u64>,
    ) -> Option<CellId> {
        if self.options.max_solver_checks == 0 {
            return None;
        }
        let eligible: Vec<_> = private_cells
            .iter()
            .filter(|cell| {
                result.value_facts.domain(cell).is_none()
                    && self.next_timeout(cell, initial_timeout_ms).is_some()
            })
            .cloned()
            .collect();
        if eligible.is_empty() {
            return None;
        }
        if self.statistics.solver_checks >= self.options.max_solver_checks {
            self.statistics.budget_exhausted = true;
            for cell in eligible {
                if let Some(evidence) = self.cells.get_mut(&cell) {
                    evidence
                        .limitation
                        .get_or_insert(RecoveryLimitation::QueryLimit);
                }
            }
            return None;
        }
        // Fairness gates priority: high-impact cells cannot consume later cells' entire allowance.
        let round = |cell: &CellId| {
            self.cells
                .get(cell)
                .map_or(0, |evidence| evidence.solver_checks)
                / self.options.max_checks_per_round
        };
        let earliest_round = eligible.iter().map(round).min().unwrap();
        let candidates: Vec<_> = eligible
            .into_iter()
            .filter(|cell| round(cell) == earliest_round)
            .collect();
        let excluded: HashSet<_> = private_cells
            .iter()
            .filter(|cell| !candidates.contains(cell))
            .cloned()
            .collect();
        let cell = candidates
            .iter()
            .filter(|cell| result.facts.is_unique(cell))
            .min()
            .cloned()
            .or_else(|| {
                choose_query_cell(
                    expressions,
                    &result.facts,
                    &result.value_facts,
                    modulus,
                    private_cells,
                    &[],
                    &excluded,
                )
            })
            .expect("Eligible discovery cells include a selectable target");
        Some(cell)
    }

    pub(crate) fn discover_domain(
        &mut self,
        cell: &CellId,
        modulus: &BigInt,
        initial_timeout_ms: Option<u64>,
        mut query: impl FnMut(
            &CellId,
            &BTreeSet<BigInt>,
            Option<u64>,
            DiscoveryProbe,
        ) -> Result<DiscoveryResponse>,
    ) -> Result<Option<(CellId, Option<UcpValueDomain>, bool)>> {
        if self.statistics.solver_checks >= self.options.max_solver_checks {
            return Ok(None);
        }
        let Some(timeout) = self.next_timeout(cell, initial_timeout_ms) else {
            return Ok(None);
        };
        let cell = cell.clone();
        let evidence = self.cells.entry(cell.clone()).or_default();
        let resumed = evidence.solver_checks > 0;
        let retry = matches!(
            evidence.limitation,
            Some(RecoveryLimitation::SolverTimeout | RecoveryLimitation::SolverUnknown { .. })
        );
        self.statistics.attempted_cells += usize::from(!resumed);
        self.statistics.resumed_checks += usize::from(resumed);
        self.statistics.retry_checks += usize::from(retry);
        evidence.retry_checks += usize::from(retry);
        evidence.limitation = None;
        self.timeouts.insert(cell.clone(), timeout);
        let models_before = evidence.models_found;
        let counters_before = (
            evidence.full_solver_checks,
            evidence.subset_solver_checks,
            evidence.subset_fallbacks,
            evidence.subset_unknown_checks,
            evidence.subset_unsat_proofs,
        );
        let probe = if self.options.use_targeted_subsets
            && !evidence.observed_values.is_empty()
            && !self.pending_full.contains(&cell)
        {
            DiscoveryProbe::SubsetExclusion
        } else {
            DiscoveryProbe::Full
        };
        let (domain, pending_full) = discover_probe(
            evidence,
            self.options.max_values_per_cell,
            modulus,
            |blocked| query(&cell, blocked, timeout, probe),
        )?;
        if pending_full {
            self.pending_full.insert(cell.clone());
        } else {
            self.pending_full.remove(&cell);
        }
        self.statistics.solver_checks += 1;
        self.statistics.full_solver_checks += evidence.full_solver_checks - counters_before.0;
        self.statistics.subset_solver_checks += evidence.subset_solver_checks - counters_before.1;
        self.statistics.subset_fallbacks += evidence.subset_fallbacks - counters_before.2;
        self.statistics.subset_unknown_checks += evidence.subset_unknown_checks - counters_before.3;
        self.statistics.subset_unsat_proofs += evidence.subset_unsat_proofs - counters_before.4;
        self.statistics.models_found += evidence.models_found - models_before;
        self.statistics.complete_domains += usize::from(domain.is_some());
        Ok(Some((cell, domain, evidence.witnessed_non_unique)))
    }

    // Original C/P is unchanged by UCP progress: repeating an unknown needs a larger time budget.
    fn next_timeout(&self, cell: &CellId, initial: Option<u64>) -> Option<Option<u64>> {
        let Some(evidence) = self.cells.get(cell) else {
            return Some(initial);
        };
        if evidence.status == PrivateDomainDiscoveryStatus::Complete {
            return None;
        }
        let previous = self.timeouts.get(cell).copied().unwrap_or(initial);
        match &evidence.limitation {
            None => Some(previous),
            Some(RecoveryLimitation::SolverTimeout | RecoveryLimitation::SolverUnknown { .. })
                if evidence.retry_checks < self.options.max_retries_per_cell =>
            {
                match (previous, self.options.retry_solver_timeout_ms) {
                    (Some(previous), Some(next)) if next > previous => Some(Some(next)),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

fn discover_probe(
    evidence: &mut PrivateDomainDiscovery,
    max_values: usize,
    modulus: &BigInt,
    mut query: impl FnMut(&BTreeSet<BigInt>) -> Result<DiscoveryResponse>,
) -> Result<(Option<UcpValueDomain>, bool)> {
    evidence.solver_checks += 1;
    let answer = match query(&evidence.observed_values)? {
        DiscoveryResponse::Full(answer) => {
            evidence.full_solver_checks += 1;
            answer
        }
        DiscoveryResponse::FullUnknown(limitation) => {
            evidence.full_solver_checks += 1;
            evidence.limitation = Some(limitation);
            return Ok((None, true));
        }
        DiscoveryResponse::SubsetFallback { unknown } => {
            ensure!(
                !evidence.observed_values.is_empty(),
                "Subset exclusion requires a full-original sample"
            );
            evidence.subset_solver_checks += 1;
            evidence.subset_fallbacks += 1;
            evidence.subset_unknown_checks += usize::from(unknown);
            // SAT/unknown of a weaker formula cannot add a feasible value or invalidate exhaustion.
            return Ok((None, true));
        }
        DiscoveryResponse::SubsetUnsat => {
            ensure!(
                !evidence.observed_values.is_empty(),
                "Subset exclusion requires a full-original sample"
            );
            evidence.subset_solver_checks += 1;
            evidence.subset_unsat_proofs += 1;
            None
        }
    };
    let Some(value) = answer else {
        ensure!(
            !evidence.observed_values.is_empty(),
            "Domain discovery contradicts original satisfiability"
        );
        // C implies its literal subset S; either UNSAT exclusion covers the full projection.
        let domain = UcpValueDomain::finite_set(evidence.observed_values.iter().cloned())
            .context("Discovered complete domain exceeds the representation limit")?;
        evidence.status = PrivateDomainDiscoveryStatus::Complete;
        return Ok((Some(domain), false));
    };
    evidence.models_found += 1;
    let Some(value) = normalize_field_value(value, modulus) else {
        evidence.limitation = Some(RecoveryLimitation::ValueRepresentationLimit);
        return Ok((None, false));
    };
    ensure!(
        !evidence.observed_values.contains(&value),
        "SMT model repeats an excluded field value during domain discovery"
    );
    evidence.witnessed_non_unique |= !evidence.observed_values.is_empty();
    if evidence.observed_values.len() >= max_values {
        // A SAT exhaustion probe is evidence of additional values, not a covering finite set.
        evidence.limitation = Some(RecoveryLimitation::DomainSizeLimit);
    } else {
        evidence.observed_values.insert(value);
    }
    Ok((None, false))
}

#[cfg(test)]
fn discover_one(
    evidence: &mut PrivateDomainDiscovery,
    max_values: usize,
    modulus: &BigInt,
    mut query: impl FnMut(&BTreeSet<BigInt>) -> Result<Option<BigInt>>,
) -> Result<Option<UcpValueDomain>> {
    Ok(discover_probe(evidence, max_values, modulus, |blocked| {
        full_discovery_response(query(blocked))
    })?
    .0)
}

#[cfg(test)]
fn discover_domain(
    max_checks: usize,
    max_values: usize,
    modulus: &BigInt,
    mut query: impl FnMut(&BTreeSet<BigInt>) -> Result<Option<BigInt>>,
) -> Result<(Option<UcpValueDomain>, PrivateDomainDiscovery)> {
    let mut evidence = PrivateDomainDiscovery::default();
    loop {
        if evidence.solver_checks >= max_checks {
            evidence.limitation = Some(RecoveryLimitation::QueryLimit);
            break;
        }
        if let Some(domain) = discover_one(&mut evidence, max_values, modulus, &mut query)? {
            return Ok((Some(domain), evidence));
        }
        if evidence.limitation.is_some() {
            break;
        }
    }
    Ok((None, evidence))
}

#[cfg(test)]
mod tests {
    use super::super::{
        engine::analyze_expressions_with_values_and_modulus, facts::UcpFacts, value::UcpValueFacts,
    };
    use super::*;
    use crate::smt_solver::smt_parser::{SolverUnknownDetails, UnknownSolverResult};

    fn timeout() -> anyhow::Error {
        anyhow::anyhow!(UnknownSolverResult).context(SolverUnknownDetails {
            reason: Some("TIMEOUT".into()),
        })
    }

    fn finite_query(values: &[i64], blocked: &BTreeSet<BigInt>) -> Option<BigInt> {
        values
            .iter()
            .copied()
            .map(BigInt::from)
            .find(|value| !blocked.contains(value))
    }

    #[test]
    fn imported_samples_respect_the_retained_value_cap_and_disabled_search() {
        let cell = CellId::advice(0, 0);
        let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
            max_values_per_cell: 2,
            ..options(4)
        });
        state.remember_samples(&cell, &BTreeSet::from([7.into()]));
        state.remember_samples(&cell, &BTreeSet::from([1.into(), 3.into()]));
        let evidence = &state.cells[&cell];
        assert_eq!(evidence.observed_values.len(), 2);
        assert!(evidence.observed_values.contains(&7.into()));
        assert!(evidence.witnessed_non_unique);
        assert_eq!(
            evidence.limitation,
            Some(RecoveryLimitation::DomainSizeLimit)
        );
        assert_eq!(state.statistics.solver_checks, 0);
        assert_eq!(state.statistics.reused_values, 2);

        let mut disabled = DomainDiscoveryState::new(Default::default());
        disabled.remember_samples(&cell, &BTreeSet::from([3.into(), 7.into()]));
        assert!(disabled.cells.is_empty());
        assert_eq!(disabled.statistics.reused_values, 0);
    }

    #[test]
    fn samples_from_another_operation_need_only_an_exhaustion_check() {
        let cell = CellId::advice(0, 0);
        let mut state = DomainDiscoveryState::new(options(1));
        let samples = BTreeSet::from([3.into(), 7.into()]);
        state.remember_samples(&cell, &samples);
        state.remember_samples(&cell, &samples);
        let baseline = result(UcpValueFacts::new());
        let found = state
            .discover_next(
                &[cell.clone()],
                &[],
                &baseline,
                &101.into(),
                Some(100),
                |queried, blocked, _| {
                    assert_eq!(queried, &cell);
                    assert_eq!(blocked, &samples);
                    Ok(None)
                },
            )
            .unwrap()
            .unwrap();
        assert_eq!(found.1, UcpValueDomain::finite_set(samples));
        assert!(found.2);
        assert_eq!(state.statistics.solver_checks, 1);
        assert_eq!(state.statistics.models_found, 0);
        assert_eq!(state.statistics.reused_values, 2);
        assert!(baseline.value_facts.domain(&cell).is_none());
    }

    #[test]
    fn imported_single_sample_and_unknown_never_become_an_exact_value() {
        let cell = CellId::advice(0, 0);
        let mut state = DomainDiscoveryState::new(options(1));
        state.remember_samples(&cell, &BTreeSet::from([3.into()]));
        let found = state
            .discover_next(
                &[cell.clone()],
                &[],
                &result(UcpValueFacts::new()),
                &101.into(),
                Some(100),
                |_, _, _| Err(timeout()),
            )
            .unwrap()
            .unwrap();
        assert!(found.1.is_none());
        assert!(!found.2);
        assert_eq!(
            state.cells[&cell].status,
            PrivateDomainDiscoveryStatus::Partial
        );
        assert_eq!(state.statistics.solver_checks, 1);
        assert_eq!(state.statistics.reused_values, 1);
    }

    fn result(values: UcpValueFacts) -> UcpResult {
        analyze_expressions_with_values_and_modulus(&[], UcpFacts::new(), values, &101.into())
    }

    fn options(checks: usize) -> PrivacyDomainDiscoveryOptions {
        PrivacyDomainDiscoveryOptions {
            max_solver_checks: checks,
            ..Default::default()
        }
    }

    #[test]
    fn exhaustion_at_the_value_cap_proves_a_complete_domain() {
        let (domain, evidence) = discover_domain(3, 2, &101.into(), |blocked| {
            Ok(finite_query(&[3, 7], blocked))
        })
        .unwrap();
        assert_eq!(
            domain,
            UcpValueDomain::finite_set([3, 7].into_iter().map(BigInt::from))
        );
        assert_eq!(evidence.status, PrivateDomainDiscoveryStatus::Complete);
        assert_eq!(evidence.solver_checks, 3);
        assert_eq!(evidence.models_found, 2);
        assert!(evidence.witnessed_non_unique);
        assert!(evidence.limitation.is_none());
    }

    #[test]
    fn a_single_sample_is_not_exact_until_exhaustion_is_proven() {
        for checks in [1, 2] {
            let (domain, evidence) = discover_domain(checks, 1, &101.into(), |blocked| {
                Ok(finite_query(&[3], blocked))
            })
            .unwrap();
            assert_eq!(
                domain,
                if checks == 2 {
                    Some(UcpValueDomain::exact(3.into()))
                } else {
                    None
                }
            );
            assert_eq!(evidence.observed_values, BTreeSet::from([3.into()]));
            assert!(!evidence.witnessed_non_unique);
            assert_eq!(evidence.solver_checks, checks);
        }
    }

    #[test]
    fn partial_checks_and_value_overflow_never_export_samples_as_a_domain() {
        for (checks, size, reason, models) in [
            (2, 2, RecoveryLimitation::QueryLimit, 2),
            (3, 2, RecoveryLimitation::DomainSizeLimit, 3),
            (2, 1, RecoveryLimitation::DomainSizeLimit, 2),
        ] {
            let (domain, evidence) = discover_domain(checks, size, &101.into(), |blocked| {
                Ok(finite_query(&[3, 7, 11], blocked))
            })
            .unwrap();
            assert!(domain.is_none());
            assert_eq!(evidence.status, PrivateDomainDiscoveryStatus::Partial);
            assert_eq!(evidence.limitation, Some(reason));
            assert_eq!(evidence.models_found, models);
            assert!(evidence.observed_values.len() <= size);
            assert!(evidence.witnessed_non_unique);
        }
    }

    #[test]
    fn timeout_preserves_samples_but_not_a_covering_claim() {
        for samples in [0, 1, 2] {
            let (domain, evidence) = discover_domain(3, 2, &101.into(), |blocked| {
                if blocked.len() >= samples {
                    Err(timeout())
                } else {
                    Ok(finite_query(&[3, 7], blocked))
                }
            })
            .unwrap();
            assert!(domain.is_none());
            assert_eq!(evidence.observed_values.len(), samples);
            assert_eq!(evidence.witnessed_non_unique, samples == 2);
            assert_eq!(evidence.solver_checks, samples + 1);
            assert_eq!(evidence.limitation, Some(RecoveryLimitation::SolverTimeout));
        }
    }

    #[test]
    fn empty_exhaustion_duplicates_and_malformed_output_fail_closed() {
        assert!(discover_domain(1, 2, &101.into(), |_| Ok(None)).is_err());
        assert!(discover_domain(2, 2, &13.into(), |_| Ok(Some(12.into()))).is_err());
        assert!(discover_domain(1, 2, &101.into(), |_| Err(anyhow::anyhow!(
            "malformed model"
        )))
        .is_err());
    }

    #[test]
    fn field_values_are_normalized_before_blocking_or_deduplication() {
        let (domain, evidence) = discover_domain(2, 1, &13.into(), |blocked| {
            if blocked.is_empty() {
                Ok(Some(12.into()))
            } else {
                assert_eq!(blocked, &BTreeSet::from([BigInt::from(-1)]));
                Ok(None)
            }
        })
        .unwrap();
        assert_eq!(domain, Some(UcpValueDomain::exact((-1).into())));
        assert_eq!(evidence.observed_values, BTreeSet::from([(-1).into()]));
        let (_, unsupported) =
            discover_domain(1, 2, &(BigInt::from(1) << 4097), |_| Ok(Some(1.into()))).unwrap();
        assert_eq!(
            unsupported.limitation,
            Some(RecoveryLimitation::ValueRepresentationLimit)
        );
    }

    #[test]
    fn domain_representation_boundary_requires_a_final_unsat_check() {
        let modulus = BigInt::from(1009);
        let query = |blocked: &BTreeSet<BigInt>| {
            Ok((0..256)
                .map(BigInt::from)
                .find(|value| !blocked.contains(value)))
        };
        let (domain, evidence) = discover_domain(257, 256, &modulus, query).unwrap();
        assert!(matches!(domain, Some(UcpValueDomain::FiniteSet(values)) if values.len() == 256));
        assert_eq!(evidence.solver_checks, 257);
        assert_eq!(evidence.status, PrivateDomainDiscoveryStatus::Complete);
        let (domain, evidence) = discover_domain(256, 256, &modulus, query).unwrap();
        assert!(domain.is_none());
        assert_eq!(evidence.limitation, Some(RecoveryLimitation::QueryLimit));
    }

    #[test]
    fn total_budget_and_attempts_do_not_reset_after_new_facts() {
        let cells = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let mut values = UcpValueFacts::new();
        let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
            max_solver_checks: 3,
            max_values_per_cell: 2,
            max_checks_per_round: 3,
            ..Default::default()
        });
        for _ in 0..3 {
            let step = state
                .discover_next(
                    &cells,
                    &[],
                    &result(values.clone()),
                    &101.into(),
                    None,
                    |_, blocked, _| Ok(finite_query(&[3, 7], blocked)),
                )
                .unwrap()
                .unwrap();
            if let Some(domain) = step.1 {
                values.mark_domain(step.0, domain);
            }
        }
        assert!(state
            .discover_next(
                &cells,
                &[],
                &result(values),
                &101.into(),
                None,
                |_, _, _| unreachable!()
            )
            .unwrap()
            .is_none());
        assert_eq!(state.statistics.solver_checks, 3);
        assert_eq!(state.statistics.attempted_cells, 1);
        assert!(state.statistics.budget_exhausted);
    }

    #[test]
    fn existing_delta_domains_and_disabled_discovery_are_not_enumerated() {
        let cell = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();
        values.mark_domain(
            cell.clone(),
            UcpValueDomain::finite_set([0, 1].into_iter().map(BigInt::from)).unwrap(),
        );
        let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
            max_solver_checks: 3,
            max_values_per_cell: 2,
            ..Default::default()
        });
        assert!(state
            .discover_next(
                &[cell.clone()],
                &[],
                &result(values),
                &101.into(),
                None,
                |_, _, _| unreachable!()
            )
            .unwrap()
            .is_none());
        assert_eq!(state.statistics.solver_checks, 0);
        let mut disabled = DomainDiscoveryState::new(Default::default());
        assert!(disabled
            .discover_next(
                &[cell],
                &[],
                &result(Default::default()),
                &101.into(),
                None,
                |_, _, _| unreachable!()
            )
            .unwrap()
            .is_none());
    }

    #[test]
    fn scheduler_preserves_samples_and_shares_checks_across_rounds() {
        let cells = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let mut state = DomainDiscoveryState::new(options(5));
        let result = result(Default::default());
        let mut order = Vec::new();
        while state
            .discover_next(
                &cells,
                &[],
                &result,
                &101.into(),
                Some(10),
                |cell, blocked, _| {
                    order.push(cell.clone());
                    assert_eq!(
                        blocked.len(),
                        order.iter().filter(|seen| *seen == cell).count() - 1
                    );
                    Ok(Some(BigInt::from(blocked.len())))
                },
            )
            .unwrap()
            .is_some()
        {}
        assert_eq!(
            order,
            vec![
                cells[0].clone(),
                cells[1].clone(),
                cells[0].clone(),
                cells[1].clone(),
                cells[0].clone()
            ]
        );
        assert_eq!(state.statistics.solver_checks, 5);
        assert_eq!(state.statistics.attempted_cells, 2);
        assert_eq!(state.statistics.resumed_checks, 3);
        assert_eq!(state.statistics.retry_checks, 0);
        assert!(state.statistics.budget_exhausted);
        for evidence in state.cells.values() {
            assert_eq!(evidence.status, PrivateDomainDiscoveryStatus::Partial);
            assert_eq!(evidence.limitation, Some(RecoveryLimitation::QueryLimit));
        }
        assert!(result.value_facts.domains().is_empty());
    }

    #[test]
    fn fairness_recovers_a_later_singleton_with_the_same_total_budget() {
        let cells = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let result = result(Default::default());
        for (quantum, recovered) in [(1, true), (4, false)] {
            let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
                max_checks_per_round: quantum,
                ..options(4)
            });
            let mut found = None;
            while let Some((cell, domain, _)) = state
                .discover_next(
                    &cells,
                    &[],
                    &result,
                    &101.into(),
                    None,
                    |cell, blocked, _| {
                        if cell == &cells[0] {
                            Ok(Some(BigInt::from(blocked.len())))
                        } else {
                            Ok(finite_query(&[7], blocked))
                        }
                    },
                )
                .unwrap()
            {
                if cell == cells[1] && domain.is_some() {
                    found = domain;
                }
            }
            assert_eq!(found, recovered.then(|| UcpValueDomain::exact(7.into())));
            assert_eq!(state.statistics.solver_checks, 4);
        }
    }

    #[test]
    fn quantum_changes_fair_round_size_without_resetting_counts() {
        let cells = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
            max_checks_per_round: 2,
            ..options(5)
        });
        let mut order = Vec::new();
        let result = result(Default::default());
        while state
            .discover_next(
                &cells,
                &[],
                &result,
                &101.into(),
                None,
                |cell, blocked, _| {
                    order.push(cell.clone());
                    Ok(Some(BigInt::from(blocked.len())))
                },
            )
            .unwrap()
            .is_some()
        {}
        assert_eq!(
            order,
            vec![
                cells[0].clone(),
                cells[0].clone(),
                cells[1].clone(),
                cells[1].clone(),
                cells[0].clone()
            ]
        );
        assert_eq!(state.statistics.solver_checks, 5);
    }

    #[test]
    fn scheduler_prioritizes_ucp_gain_without_promoting_simulated_facts() {
        let decoy = CellId::advice(0, 0);
        let a = CellId::advice(1, 0);
        let b = CellId::advice(2, 0);
        let x = CellId::advice(3, 0);
        let public = CellId::instance(0, 0);
        let expressions = vec![
            UcpExpr::mul(UcpExpr::var(a.clone()), UcpExpr::var(x.clone())),
            UcpExpr::mul(
                UcpExpr::var(b.clone()),
                UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(-1)),
            ),
            UcpExpr::add(
                UcpExpr::add(UcpExpr::var(a.clone()), UcpExpr::var(b.clone())),
                UcpExpr::neg(UcpExpr::var(public.clone())),
            ),
        ];
        let result = analyze_expressions_with_values_and_modulus(
            &expressions,
            UcpFacts::from_iter([public]),
            UcpValueFacts::new(),
            &101.into(),
        );
        let original = result.clone();
        let cells = [decoy, a, b, x.clone()];
        let mut state = DomainDiscoveryState::new(options(1));
        let step = state
            .discover_next(
                &cells,
                &expressions,
                &result,
                &101.into(),
                None,
                |cell, _, _| {
                    assert_eq!(cell, &x);
                    Ok(Some(3.into()))
                },
            )
            .unwrap()
            .unwrap();
        assert_eq!(step.0, x);
        assert!(step.1.is_none());
        assert_eq!(result, original);
    }

    #[test]
    fn known_unique_priority_obeys_fairness_and_new_domains_stop_enumeration() {
        let cells = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let mut result = result(Default::default());
        result.facts.mark_unique(cells[1].clone());
        let mut state = DomainDiscoveryState::new(options(3));
        let first = state
            .discover_next(&cells, &[], &result, &101.into(), None, |_, _, _| {
                Ok(Some(3.into()))
            })
            .unwrap()
            .unwrap();
        assert_eq!(first.0, cells[1]);
        let second = state
            .discover_next(&cells, &[], &result, &101.into(), None, |_, _, _| {
                Ok(Some(7.into()))
            })
            .unwrap()
            .unwrap();
        assert_eq!(second.0, cells[0]); // Even a unique target must yield its first-round slot.
        result.value_facts.mark_known(cells[1].clone(), 3.into());
        let third = state
            .discover_next(
                &cells,
                &[],
                &result,
                &101.into(),
                None,
                |cell, blocked, _| {
                    assert_eq!(cell, &cells[0]);
                    assert_eq!(blocked, &BTreeSet::from([7.into()]));
                    Ok(None)
                },
            )
            .unwrap()
            .unwrap();
        assert_eq!(third.1, Some(UcpValueDomain::exact(7.into())));
        assert_eq!(state.statistics.solver_checks, 3);
    }

    #[test]
    fn timeout_resume_keeps_samples_and_requires_a_larger_explicit_budget() {
        let cell = CellId::advice(0, 0);
        let result = result(Default::default());
        let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
            retry_solver_timeout_ms: Some(20),
            ..options(4)
        });
        let mut calls = 0;
        let mut found = None;
        while let Some((_, domain, _)) = state
            .discover_next(
                &[cell.clone()],
                &[],
                &result,
                &101.into(),
                Some(10),
                |_, blocked, budget| {
                    calls += 1;
                    assert_eq!(budget, Some(if calls <= 2 { 10 } else { 20 }));
                    if calls == 2 {
                        assert_eq!(blocked, &BTreeSet::from([3.into()]));
                        Err(timeout())
                    } else {
                        if calls == 3 {
                            assert_eq!(blocked, &BTreeSet::from([3.into()]));
                        }
                        Ok(finite_query(&[3, 7], blocked))
                    }
                },
            )
            .unwrap()
        {
            found = found.or(domain);
        }
        assert_eq!(
            found,
            UcpValueDomain::finite_set([3, 7].into_iter().map(BigInt::from))
        );
        let evidence = &state.cells[&cell];
        assert_eq!(evidence.retry_checks, 1);
        assert!(evidence.limitation.is_none());
        assert_eq!(state.statistics.solver_checks, 4);
        assert_eq!(state.statistics.retry_checks, 1);
        assert_eq!(state.statistics.resumed_checks, 3);
    }

    #[test]
    fn timeouts_do_not_loop_without_a_strict_budget_increase_or_after_retry() {
        for (initial, floor, retry_limit, expected_checks) in [
            (Some(10), None, 1, 1),
            (Some(10), Some(10), 1, 1),
            (None, Some(20), 1, 1),
            (Some(10), Some(20), 0, 1),
            (Some(10), Some(20), 5, 2),
        ] {
            let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
                retry_solver_timeout_ms: floor,
                max_retries_per_cell: retry_limit,
                ..options(20)
            });
            let result = result(Default::default());
            while state
                .discover_next(
                    &[CellId::advice(0, 0)],
                    &[],
                    &result,
                    &101.into(),
                    initial,
                    |_, _, _| Err(timeout()),
                )
                .unwrap()
                .is_some()
            {}
            assert_eq!(state.statistics.solver_checks, expected_checks);
            assert_eq!(state.statistics.complete_domains, 0);
        }
    }

    #[test]
    fn fresh_target_receives_a_check_before_a_timeout_retry() {
        let cells = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let result = result(Default::default());
        let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
            retry_solver_timeout_ms: Some(20),
            ..options(4)
        });
        let mut order = Vec::new();
        let mut found = None;
        while let Some((_, domain, _)) = state
            .discover_next(
                &cells,
                &[],
                &result,
                &101.into(),
                Some(10),
                |cell, blocked, _| {
                    order.push(cell.clone());
                    if cell == &cells[0] {
                        Err(timeout())
                    } else {
                        Ok(finite_query(&[7], blocked))
                    }
                },
            )
            .unwrap()
        {
            found = found.or(domain);
        }
        assert_eq!(
            order,
            vec![
                cells[0].clone(),
                cells[1].clone(),
                cells[0].clone(),
                cells[1].clone()
            ]
        );
        assert_eq!(found, Some(UcpValueDomain::exact(7.into())));
        assert_eq!(state.statistics.solver_checks, 4);
        assert_eq!(state.cells[&cells[0]].retry_checks, 1);
    }

    #[test]
    fn retry_and_continuation_never_reset_the_hard_total() {
        let cell = CellId::advice(0, 0);
        let result = result(Default::default());
        let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
            retry_solver_timeout_ms: Some(20),
            ..options(3)
        });
        let mut calls = 0;
        while let Some((_, domain, _)) = state
            .discover_next(
                &[cell.clone()],
                &[],
                &result,
                &101.into(),
                Some(10),
                |_, blocked, _| {
                    calls += 1;
                    if calls == 2 {
                        Err(timeout())
                    } else {
                        Ok(finite_query(&[3, 7], blocked))
                    }
                },
            )
            .unwrap()
        {
            assert!(domain.is_none());
        }
        assert_eq!(state.statistics.solver_checks, 3);
        assert_eq!(
            state.cells[&cell].observed_values,
            BTreeSet::from([3.into(), 7.into()])
        );
        assert_eq!(
            state.cells[&cell].limitation,
            Some(RecoveryLimitation::QueryLimit)
        );
        assert!(state.statistics.budget_exhausted);
    }

    #[test]
    fn zero_quantum_and_zero_retry_timeout_are_rejected() {
        assert!(PrivacyDomainDiscoveryOptions {
            max_checks_per_round: 0,
            ..options(3)
        }
        .validate()
        .is_err());
        assert!(PrivacyDomainDiscoveryOptions {
            retry_solver_timeout_ms: Some(0),
            ..options(3)
        }
        .validate()
        .is_err());
    }

    #[test]
    fn subset_unsat_closes_a_full_model_sample_without_an_extra_full_check() {
        let cell = CellId::advice(0, 0);
        let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
            use_targeted_subsets: true,
            ..options(2)
        });
        let result = result(Default::default());
        let mut probes = Vec::new();
        let mut found = None;
        while let Some((_, domain, _)) = state
            .discover_next_with_subsets(
                &[cell.clone()],
                &[],
                &result,
                &101.into(),
                Some(10),
                |_, blocked, _, probe| {
                    probes.push(probe);
                    if blocked.is_empty() {
                        assert_eq!(probe, DiscoveryProbe::Full);
                        Ok(DiscoveryResponse::Full(Some(7.into())))
                    } else {
                        assert_eq!(blocked, &BTreeSet::from([7.into()]));
                        assert_eq!(probe, DiscoveryProbe::SubsetExclusion);
                        Ok(DiscoveryResponse::SubsetUnsat)
                    }
                },
            )
            .unwrap()
        {
            found = found.or(domain);
        }
        assert_eq!(found, Some(UcpValueDomain::exact(7.into())));
        assert_eq!(
            probes,
            [DiscoveryProbe::Full, DiscoveryProbe::SubsetExclusion]
        );
        assert_eq!(state.statistics.solver_checks, 2);
        assert_eq!(state.statistics.full_solver_checks, 1);
        assert_eq!(state.statistics.subset_solver_checks, 1);
        assert_eq!(state.statistics.subset_unsat_proofs, 1);
        assert_eq!(state.statistics.models_found, 1);
        assert!(!state.statistics.budget_exhausted);
    }

    #[test]
    fn subset_sat_and_unknown_require_a_separately_budgeted_full_fallback() {
        for unknown in [false, true] {
            for budget in [2, 3] {
                let cell = CellId::advice(0, 0);
                let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
                    use_targeted_subsets: true,
                    ..options(budget)
                });
                let result = result(Default::default());
                let mut probes = Vec::new();
                let mut found = None;
                while let Some((_, domain, _)) = state
                    .discover_next_with_subsets(
                        &[cell.clone()],
                        &[],
                        &result,
                        &101.into(),
                        Some(10),
                        |_, blocked, timeout, probe| {
                            assert_eq!(timeout, Some(10)); // A subset unknown needs fallback, not escalation.
                            probes.push(probe);
                            match probes.len() {
                                1 => Ok(DiscoveryResponse::Full(Some(7.into()))),
                                2 => {
                                    assert_eq!(probe, DiscoveryProbe::SubsetExclusion);
                                    assert_eq!(blocked, &BTreeSet::from([7.into()]));
                                    Ok(DiscoveryResponse::SubsetFallback { unknown })
                                }
                                3 => {
                                    assert_eq!(probe, DiscoveryProbe::Full);
                                    assert_eq!(blocked, &BTreeSet::from([7.into()]));
                                    Ok(DiscoveryResponse::Full(None))
                                }
                                _ => unreachable!(),
                            }
                        },
                    )
                    .unwrap()
                {
                    found = found.or(domain);
                }
                assert_eq!(probes.len(), budget);
                assert_eq!(
                    found,
                    (budget == 3).then(|| UcpValueDomain::exact(7.into()))
                );
                let evidence = &state.cells[&cell];
                assert_eq!(evidence.observed_values, BTreeSet::from([7.into()]));
                assert_eq!(evidence.models_found, 1);
                assert_eq!(evidence.retry_checks, 0);
                assert_eq!(state.statistics.full_solver_checks, budget - 1);
                assert_eq!(state.statistics.subset_solver_checks, 1);
                assert_eq!(state.statistics.subset_fallbacks, 1);
                assert_eq!(state.statistics.subset_unknown_checks, usize::from(unknown));
                assert_eq!(state.statistics.subset_unsat_proofs, 0);
                if budget == 2 {
                    assert_eq!(evidence.status, PrivateDomainDiscoveryStatus::Partial);
                    assert_eq!(evidence.limitation, Some(RecoveryLimitation::QueryLimit));
                }
            }
        }
    }

    #[test]
    fn subset_fallback_phases_and_samples_survive_fair_cell_switches() {
        let cells = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
            use_targeted_subsets: true,
            ..options(6)
        });
        let result = result(Default::default());
        let mut order = Vec::new();
        let mut found = 0;
        while let Some((_, domain, _)) = state
            .discover_next_with_subsets(
                &cells,
                &[],
                &result,
                &101.into(),
                None,
                |cell, blocked, _, probe| {
                    order.push((cell.clone(), probe));
                    if blocked.is_empty() {
                        Ok(DiscoveryResponse::Full(Some(BigInt::from(cell.column + 3))))
                    } else if probe == DiscoveryProbe::SubsetExclusion {
                        Ok(DiscoveryResponse::SubsetFallback { unknown: false })
                    } else {
                        assert_eq!(blocked, &BTreeSet::from([BigInt::from(cell.column + 3)]));
                        Ok(DiscoveryResponse::Full(None))
                    }
                },
            )
            .unwrap()
        {
            found += usize::from(domain.is_some());
        }
        assert_eq!(found, 2);
        assert_eq!(
            order,
            vec![
                (cells[0].clone(), DiscoveryProbe::Full),
                (cells[1].clone(), DiscoveryProbe::Full),
                (cells[0].clone(), DiscoveryProbe::SubsetExclusion),
                (cells[1].clone(), DiscoveryProbe::SubsetExclusion),
                (cells[0].clone(), DiscoveryProbe::Full),
                (cells[1].clone(), DiscoveryProbe::Full),
            ]
        );
        assert_eq!(state.statistics.solver_checks, 6);
        assert_eq!(state.statistics.full_solver_checks, 4);
        assert_eq!(state.statistics.subset_solver_checks, 2);
        assert_eq!(state.statistics.resumed_checks, 4);
    }

    #[test]
    fn a_missing_subset_uses_one_full_check_and_full_unknown_retries_stay_full() {
        let cell = CellId::advice(0, 0);
        let result = result(Default::default());
        let mut state = DomainDiscoveryState::new(PrivacyDomainDiscoveryOptions {
            use_targeted_subsets: true,
            retry_solver_timeout_ms: Some(20),
            ..options(4)
        });
        let mut probes = Vec::new();
        let mut found = None;
        while let Some((_, domain, _)) = state
            .discover_next_with_subsets(
                &[cell.clone()],
                &[],
                &result,
                &101.into(),
                Some(10),
                |_, _, timeout_ms, probe| {
                    probes.push(probe);
                    match probes.len() {
                        1 => Ok(DiscoveryResponse::Full(Some(7.into()))),
                        2 => full_discovery_response(Err(timeout())), // No stored subset: actual check is full.
                        3 => {
                            assert_eq!(probe, DiscoveryProbe::Full);
                            assert_eq!(timeout_ms, Some(20));
                            Ok(DiscoveryResponse::Full(None))
                        }
                        _ => unreachable!(),
                    }
                },
            )
            .unwrap()
        {
            found = found.or(domain);
        }
        assert_eq!(found, Some(UcpValueDomain::exact(7.into())));
        assert_eq!(state.statistics.full_solver_checks, 3);
        assert_eq!(state.statistics.subset_solver_checks, 0);
        assert_eq!(state.statistics.retry_checks, 1);
        assert_eq!(state.statistics.solver_checks, 3);
    }

    #[test]
    fn subset_errors_and_unsampled_exhaustion_fail_closed() {
        let mut evidence = PrivateDomainDiscovery::default();
        assert!(discover_probe(&mut evidence, 2, &101.into(), |_| Ok(
            DiscoveryResponse::SubsetUnsat
        ))
        .is_err());
        assert!(discover_probe(&mut evidence, 2, &101.into(), |_| Ok(
            DiscoveryResponse::SubsetFallback { unknown: false }
        ))
        .is_err());
        assert!(
            discover_probe(&mut evidence, 2, &101.into(), |_| Err(anyhow::anyhow!(
                "malformed subset output"
            )))
            .is_err()
        );
        assert!(evidence.observed_values.is_empty());
        assert_eq!(evidence.status, PrivateDomainDiscoveryStatus::Partial);
    }
}
