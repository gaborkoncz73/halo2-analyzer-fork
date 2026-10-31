//! A tényleges recovery-lépésekből fázisnaplót készít, a bizonyított állapot módosítása nélkül.

use super::super::super::{cell::CellId, engine::UcpResult, value::UcpValueDomain};
use super::{PrivateCellUniqueness, RecoveryLimitation};
use num_bigint::BigInt;
use std::{
    collections::{BTreeMap, HashSet},
    time::Duration,
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RecoveryPhaseCounts {
    pub exact_values: usize,
    /// Csak a nem egyelemű lefedő domaineket számolja, a pontos értékeket külön tartja nyilván.
    pub domains: usize,
    pub unique_cells: usize,
    pub non_unique_cells: usize,
    pub complete_domains: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecoveryCellUpdate {
    pub cell: CellId,
    pub domain: Option<UcpValueDomain>,
    pub domain_changed: bool,
    pub uniqueness: PrivateCellUniqueness,
    pub uniqueness_changed: bool,
    pub domain_is_complete: bool,
    pub completeness_changed: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RecoverySmtAction {
    Refine,
    Discover,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RecoverySmtStrategy {
    FastProbe,
    Candidates,
    Enumeration,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RecoverySmtCheckKind {
    FastProbe,
    Coverage,
    CandidateFeasibility,
    Enumeration,
    SubsetExclusion,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecoverySmtCalls {
    pub kind: RecoverySmtCheckKind,
    /// A tényleges solverfolyamatokat számolja, a fallbackeket és timeoutokat is beleértve.
    pub calls: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecoverySmtStep {
    pub cell: CellId,
    pub is_target: bool,
    pub action: RecoverySmtAction,
    pub strategy: RecoverySmtStrategy,
    pub checks: Vec<RecoverySmtCalls>,
    pub elapsed: Duration,
    pub propagation_requested: bool,
    /// Csak az adott lépésben újonnan megőrzött, megvalósítható értékeket sorolja fel.
    pub feasible_samples: Vec<BigInt>,
    /// Ugyanazon teljes SAT-modellek más cellákhoz újonnan megőrzött vetületeit sorolja fel.
    pub model_samples: BTreeMap<CellId, Vec<BigInt>>,
    pub updates: Vec<RecoveryCellUpdate>,
    pub limitation: Option<RecoveryLimitation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RecoveryPhase {
    Ucp {
        elapsed: Duration,
        counts: RecoveryPhaseCounts,
        updates: Vec<RecoveryCellUpdate>,
    },
    Smt {
        elapsed: Duration,
        counts: RecoveryPhaseCounts,
        steps: Vec<RecoverySmtStep>,
    },
}

#[derive(Clone, Eq, PartialEq)]
pub(crate) struct CellState {
    pub domain: Option<UcpValueDomain>,
    pub uniqueness: PrivateCellUniqueness,
    pub complete: bool,
}

impl CellState {
    pub(crate) fn capture(cell: &CellId, result: &UcpResult, non_unique: &HashSet<CellId>) -> Self {
        Self {
            domain: result.value_facts.domain(cell).cloned(),
            complete: result.value_facts.domain_is_complete(cell),
            uniqueness: if result.facts.is_unique(cell)
                || result.value_facts.known_value(cell).is_some()
            {
                PrivateCellUniqueness::Unique
            } else if non_unique.contains(cell) || result.value_facts.domain_is_complete(cell) {
                PrivateCellUniqueness::NonUnique
            } else {
                PrivateCellUniqueness::Unknown
            },
        }
    }

    pub(crate) fn update(&self, cell: CellId, after: &Self) -> Option<RecoveryCellUpdate> {
        (self != after).then(|| RecoveryCellUpdate {
            cell,
            domain: after.domain.clone(),
            domain_changed: self.domain != after.domain,
            uniqueness: after.uniqueness,
            uniqueness_changed: self.uniqueness != after.uniqueness,
            domain_is_complete: after.complete,
            completeness_changed: self.complete != after.complete,
        })
    }
}

pub(crate) struct PhaseSnapshot(BTreeMap<CellId, CellState>);

impl PhaseSnapshot {
    pub(crate) fn capture(
        targets: &[CellId],
        result: &UcpResult,
        non_unique: &HashSet<CellId>,
    ) -> Self {
        Self(
            targets
                .iter()
                .map(|c| (c.clone(), CellState::capture(c, result, non_unique)))
                .collect(),
        )
    }
    pub(crate) fn updates(&self, after: &Self) -> Vec<RecoveryCellUpdate> {
        self.0
            .iter()
            .filter_map(|(c, s)| s.update(c.clone(), &after.0[c]))
            .collect()
    }
    pub(crate) fn counts(&self) -> RecoveryPhaseCounts {
        let mut counts = RecoveryPhaseCounts::default();
        for state in self.0.values() {
            match state.domain {
                Some(UcpValueDomain::Exact(_)) => counts.exact_values += 1,
                Some(UcpValueDomain::FiniteSet(_)) => counts.domains += 1,
                None => {}
            }
            counts.unique_cells += usize::from(state.uniqueness == PrivateCellUniqueness::Unique);
            counts.non_unique_cells +=
                usize::from(state.uniqueness == PrivateCellUniqueness::NonUnique);
            counts.complete_domains += usize::from(state.complete);
        }
        counts
    }
}

pub(crate) fn record_smt_step(
    phases: &mut Vec<RecoveryPhase>,
    step: RecoverySmtStep,
    counts: RecoveryPhaseCounts,
) {
    // Az új UCP-t nem igénylő SMT-lépéseket egy blokkban tartja; nem talál ki köztes propagációt.
    if let Some(RecoveryPhase::Smt {
        elapsed,
        counts: current,
        steps,
    }) = phases.last_mut()
    {
        *elapsed += step.elapsed;
        *current = counts;
        steps.push(step);
    } else {
        phases.push(RecoveryPhase::Smt {
            elapsed: step.elapsed,
            counts,
            steps: vec![step],
        });
    }
}

pub(crate) fn measure_check<T>(
    checks: &mut Vec<RecoverySmtCalls>,
    kind: RecoverySmtCheckKind,
    check: impl FnOnce() -> anyhow::Result<T>,
) -> anyhow::Result<T> {
    let before = crate::smt_solver::process::invocation_count();
    let result = check();
    let calls = crate::smt_solver::process::invocation_count() - before;
    if let Some(entry) = checks.iter_mut().find(|entry| entry.kind == kind) {
        entry.calls += calls;
    } else {
        checks.push(RecoverySmtCalls { kind, calls });
    }
    result
}

fn domain_text(domain: &UcpValueDomain) -> String {
    match domain {
        UcpValueDomain::Exact(value) => value.to_string(),
        UcpValueDomain::FiniteSet(values) => {
            let preview = values
                .iter()
                .take(8)
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            if values.len() > 8 {
                format!("{{{preview}, ...}} ({} values)", values.len())
            } else {
                format!("{{{preview}}}")
            }
        }
    }
}

fn update_text(
    update: &RecoveryCellUpdate,
    names: &mut impl FnMut(&CellId) -> Option<String>,
) -> String {
    let label = names(&update.cell).unwrap_or_else(|| update.cell.to_string());
    let mut text = if update.domain_changed {
        match &update.domain {
            Some(UcpValueDomain::Exact(v)) => format!("{label} = {v} (exact)"),
            Some(domain) => format!("{label} in {} (covering domain)", domain_text(domain)),
            None => label,
        }
    } else {
        label
    };
    if update.uniqueness_changed && update.uniqueness == PrivateCellUniqueness::NonUnique {
        text.push_str("; non-unique proven");
    }
    if update.uniqueness_changed
        && update.uniqueness == PrivateCellUniqueness::Unique
        && !matches!(update.domain, Some(UcpValueDomain::Exact(_)))
    {
        text.push_str("; unique, value not recovered");
    }
    if update.completeness_changed
        && update.domain_is_complete
        && !matches!(update.domain, Some(UcpValueDomain::Exact(_)))
    {
        text.push_str("; complete domain");
        if !update.domain_changed {
            if let Some(domain) = &update.domain {
                text.push_str(&format!(" {}", domain_text(domain)));
            }
        }
    }
    text
}

fn new_target_domains<'a>(
    updates: impl IntoIterator<Item = &'a RecoveryCellUpdate>,
    targets: &HashSet<CellId>,
) -> (usize, usize) {
    // Egy cél többszöri szűkítését egyszer, az utolsó megváltozott domain szerint számolja.
    // A köztes cellákat és a puszta teljességi vagy egyértelműségi jelöléseket nem veszi ide.
    let changed: BTreeMap<_, _> = updates
        .into_iter()
        .filter(|u| u.domain_changed && targets.contains(&u.cell))
        .filter_map(|u| match &u.domain {
            Some(UcpValueDomain::Exact(_)) => Some((&u.cell, true)),
            Some(UcpValueDomain::FiniteSet(_)) => Some((&u.cell, false)),
            None => None,
        })
        .collect();
    let exact = changed.values().filter(|is_exact| **is_exact).count();
    (exact, changed.len() - exact)
}

impl super::PrivacyAnalysisReport {
    /// A kijelölt privát célokra vonatkozó, időrendi recovery-fázisokat jeleníti meg.
    pub fn phase_report(&self) -> String {
        self.phase_report_with_names(|_| None)
    }

    /// Opcionális példabeli nevekkel címkézi a cellákat; hiányzó névnél a cellaazonosítót használja.
    pub fn phase_report_with_names(
        &self,
        mut names: impl FnMut(&CellId) -> Option<String>,
    ) -> String {
        let recovery_calls: usize = self
            .phases
            .iter()
            .filter_map(|phase| match phase {
                RecoveryPhase::Smt { steps, .. } => Some(
                    steps
                        .iter()
                        .flat_map(|s| &s.checks)
                        .map(|c| c.calls)
                        .sum::<usize>(),
                ),
                _ => None,
            })
            .sum();
        let mut lines = vec![format!(
            "Initial SAT: {}; {} solver calls",
            self.satisfiability_evidence
                .map(|e| format!("{e:?}"))
                .unwrap_or_else(|| format!("{:?}", self.status)),
            self.solver_invocations.saturating_sub(recovery_calls)
        )];
        let targets = self.cells.iter().map(|c| c.cell.clone()).collect();
        let (mut ucp_number, mut smt_number) = (0, 0);
        for phase in &self.phases {
            lines.push(String::new());
            match phase {
                RecoveryPhase::Ucp {
                    elapsed,
                    counts,
                    updates,
                } => {
                    ucp_number += 1;
                    lines.push(format!(
                        "{ucp_number}. UCP ({:.2} s)",
                        elapsed.as_secs_f64()
                    ));
                    let (exact, domains) = new_target_domains(updates, &targets);
                    lines.push(format!("  Targets: {} exact values, {} domains. New: {exact} exact, {domains} new/refined domains.",counts.exact_values,counts.domains));
                    if updates.is_empty() {
                        lines.push("  No new target facts.".into());
                    }
                    for update in updates {
                        lines.push(format!("  {}", update_text(update, &mut names)));
                    }
                }
                RecoveryPhase::Smt {
                    elapsed,
                    counts,
                    steps,
                } => {
                    smt_number += 1;
                    let calls: usize = steps.iter().flat_map(|s| &s.checks).map(|c| c.calls).sum();
                    lines.push(format!(
                        "{smt_number}. SMT ({:.2} s; {calls} solver calls)",
                        elapsed.as_secs_f64()
                    ));
                    for step in steps {
                        let label = names(&step.cell).unwrap_or_else(|| step.cell.to_string());
                        let kinds = step
                            .checks
                            .iter()
                            .map(|c| format!("{:?}: {}", c.kind, c.calls))
                            .collect::<Vec<_>>()
                            .join(", ");
                        let calls: usize = step.checks.iter().map(|c| c.calls).sum();
                        lines.push(format!(
                            "  {:?}/{:?}: {label}{}; {calls} {}{}",
                            step.action,
                            step.strategy,
                            if step.is_target { "" } else { " (bridge)" },
                            if calls == 1 { "call" } else { "calls" },
                            if kinds.is_empty() {
                                String::new()
                            } else {
                                format!(" ({kinds})")
                            }
                        ));
                        if !step.feasible_samples.is_empty() {
                            let preview = step
                                .feasible_samples
                                .iter()
                                .take(8)
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join(", ");
                            lines.push(format!(
                                "    New feasible samples: {preview}{}",
                                if step.feasible_samples.len() > 8 {
                                    ", ..."
                                } else {
                                    ""
                                }
                            ));
                        }
                        for (cell, samples) in step.model_samples.iter().take(8) {
                            let label = names(cell).unwrap_or_else(|| cell.to_string());
                            let preview = samples
                                .iter()
                                .take(8)
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join(", ");
                            lines.push(format!(
                                "    Model samples: {label}: {preview}{}",
                                if samples.len() > 8 { ", ..." } else { "" }
                            ));
                        }
                        if step.model_samples.len() > 8 {
                            lines.push(format!(
                                "    Model samples: {} further cells",
                                step.model_samples.len() - 8
                            ));
                        }
                        for update in &step.updates {
                            lines.push(format!("    {}", update_text(update, &mut names)));
                        }
                        if step.updates.is_empty() {
                            lines.push("    No new target or queried-cell facts.".into());
                        }
                        if let Some(limitation) = &step.limitation {
                            lines.push(format!("    Limitation: {limitation:?}"));
                        }
                    }
                    let (exact, domains) =
                        new_target_domains(steps.iter().flat_map(|s| &s.updates), &targets);
                    lines.push(format!("  Targets: {} exact values, {} domains; {} complete domains, {} non-unique. New: {exact} exact, {domains} new/refined domains.",counts.exact_values,counts.domains,counts.complete_domains,counts.non_unique_cells));
                    lines.push(if steps.iter().any(|step| step.propagation_requested) {
                        "  UCP restart scheduled.".into()
                    } else {
                        "  No UCP restart: K/Delta contents unchanged.".into()
                    });
                }
            }
        }
        lines.push(String::new());
        let phase_time: Duration = self
            .phases
            .iter()
            .map(|phase| match phase {
                RecoveryPhase::Ucp { elapsed, .. } | RecoveryPhase::Smt { elapsed, .. } => *elapsed,
            })
            .sum();
        lines.push(format!(
            "Other work: {:.2} s (initial check, preparation, scheduling, optional control).",
            self.elapsed.saturating_sub(phase_time).as_secs_f64()
        ));
        lines.push(format!("Result: {:?}; {} exact values, {} domains; {} complete domains; {} non-unique, {} unresolved; {} solver calls; {:.2} s total.",self.status,self.summary.exact_values,self.summary.finite_domains,self.cells.iter().filter(|c|c.domain_is_complete).count(),self.summary.non_unique_cells,self.summary.unresolved_uniqueness,self.solver_invocations,self.elapsed.as_secs_f64()));
        if self.structural_baseline_computed {
            lines.push(
                "Structural baseline: separate post-recovery comparison included in total time."
                    .into(),
            );
        }
        if let Some(reason) = self.search_statistics.stop_reason {
            lines.push(format!("Search stop: {reason:?}"));
        }
        if self.domain_refinement_statistics.budget_exhausted {
            lines.push("Refinement budget exhausted.".into());
        }
        if self.domain_discovery_statistics.budget_exhausted {
            lines.push("Discovery budget exhausted.".into());
        }
        lines.join("\n")
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::super::{facts::UcpFacts, value::UcpValueFacts};
    use super::*;

    #[test]
    fn phase_counts_exclude_public_and_unselected_cells_and_keep_known_values_unique() {
        let targets = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let mut values = UcpValueFacts::new();
        values.mark_known(targets[0].clone(), 5.into());
        values.mark_domain(
            targets[1].clone(),
            UcpValueDomain::finite_set([1.into(), 2.into()]).unwrap(),
        );
        values.mark_known(CellId::instance(0, 0), 99.into());
        values.mark_known(CellId::advice(99, 0), 42.into());
        let state = UcpResult {
            facts: UcpFacts::new(),
            value_facts: values,
            checked_expressions: 0,
            unique_expressions: 0,
            unresolved_expressions: 0,
            expression_results: Vec::new(),
        };
        let counts = PhaseSnapshot::capture(&targets, &state, &HashSet::new()).counts();
        assert_eq!(counts.exact_values, 1);
        assert_eq!(counts.domains, 1);
        assert_eq!(counts.unique_cells, 1);
        assert_eq!(counts.non_unique_cells, 0);
    }

    #[test]
    fn phase_domain_preview_is_bounded_without_truncating_stored_values() {
        let domain = UcpValueDomain::finite_set((0..256).map(BigInt::from)).unwrap();
        let rendered = domain_text(&domain);
        assert!(rendered.contains("...") && rendered.contains("256 values"));
        assert!(rendered.len() < 100);
        assert_eq!(
            super::super::super::super::lookup::entries(&domain).len(),
            256
        );
    }

    #[test]
    fn phase_new_domains_count_distinct_targets_and_ignore_metadata_and_bridges() {
        let targets: HashSet<_> = (0..3).map(|col| CellId::advice(col, 0)).collect();
        let update = |column, domain, domain_changed| RecoveryCellUpdate {
            cell: CellId::advice(column, 0),
            domain: Some(domain),
            domain_changed,
            uniqueness: PrivateCellUniqueness::Unknown,
            uniqueness_changed: false,
            domain_is_complete: false,
            completeness_changed: false,
        };
        let finite = |values: &[i32]| {
            UcpValueDomain::finite_set(values.iter().copied().map(BigInt::from)).unwrap()
        };
        let mut updates = vec![
            update(0, UcpValueDomain::exact(7.into()), true),
            update(1, finite(&[1, 2, 3]), true),
            update(1, finite(&[1, 2]), true),
            update(2, finite(&[4, 5]), false),
            update(99, UcpValueDomain::exact(42.into()), true),
        ];
        assert_eq!(new_target_domains(&updates, &targets), (1, 1));
        updates.push(update(1, UcpValueDomain::exact(1.into()), true));
        let mut metadata = update(1, UcpValueDomain::exact(1.into()), false);
        metadata.domain_is_complete = true;
        metadata.completeness_changed = true;
        updates.push(metadata.clone());
        assert_eq!(new_target_domains(&updates, &targets), (2, 0));
        assert_eq!(new_target_domains([&metadata], &targets), (0, 0));
    }

    #[test]
    fn consecutive_solver_operations_form_one_phase_until_real_propagation() {
        let step = || RecoverySmtStep {
            cell: CellId::advice(0, 0),
            is_target: true,
            action: RecoverySmtAction::Refine,
            strategy: RecoverySmtStrategy::FastProbe,
            checks: vec![RecoverySmtCalls {
                kind: RecoverySmtCheckKind::FastProbe,
                calls: 2,
            }],
            elapsed: Duration::from_millis(1),
            propagation_requested: false,
            feasible_samples: vec![1.into(), 2.into()],
            model_samples: BTreeMap::new(),
            updates: vec![],
            limitation: None,
        };
        let mut phases = Vec::new();
        record_smt_step(&mut phases, step(), RecoveryPhaseCounts::default());
        record_smt_step(&mut phases, step(), RecoveryPhaseCounts::default());
        assert_eq!(phases.len(), 1);
        phases.push(RecoveryPhase::Ucp {
            elapsed: Duration::ZERO,
            counts: RecoveryPhaseCounts::default(),
            updates: vec![],
        });
        record_smt_step(&mut phases, step(), RecoveryPhaseCounts::default());
        assert_eq!(phases.len(), 3);
        let RecoveryPhase::Smt { steps, elapsed, .. } = &phases[0] else {
            panic!("SMT-fázist kell tárolnia");
        };
        assert_eq!(steps.len(), 2);
        assert_eq!(*elapsed, Duration::from_millis(2));
    }
}
