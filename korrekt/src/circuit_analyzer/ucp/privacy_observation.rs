#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

//! Az eredeti SMT-kényszerekkel ellenőrzi, hogy egy jelentett domainhez szükségesek-e a konkrét publikus megfigyelések.
//! Egy lefedési állítást vizsgál; entrópiát, minden adatszivárgást vagy protokollszintű zéró tudású tulajdonságot nem minősít.

use super::{
    cell::CellId,
    privacy::{
        limitation_from_solver_error, prepare_privacy_analysis, PrivacyAnalysisReport,
        RecoveryLimitation,
    },
    value::{normalize_field_value, UcpValueDomain, MAX_FINITE_DOMAIN_SIZE},
};
use crate::{
    circuit_analyzer::{
        analyzable::AnalyzableField, analyzer::Analyzer, halo2_proofs_libs::Circuit,
    },
    io::analyzer_io_type::AnalyzerInput,
    smt_solver::smt_parser::Satisfiability,
};
use anyhow::{ensure, Context, Result};
use num_bigint::BigInt;
use std::{
    collections::BTreeSet,
    fmt,
    time::{Duration, Instant},
};

pub(crate) const PRIVACY_OBSERVATION_POLICY: &str =
    "original-observed-coverage-unobserved-exclusion-v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PublicObservationEffectOptions {
    /// A tényleges solverhívásokat összesítve korlátozza, a kötelező eredeti SAT-próbával együtt.
    pub max_solver_checks: usize,
    /// None esetén a visszaállítási riport időkeretét, majd a környezeti alapértéket használja.
    pub solver_timeout_ms: Option<u64>,
}

impl Default for PublicObservationEffectOptions {
    fn default() -> Self {
        Self {
            max_solver_checks: 256,
            solver_timeout_ms: None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PublicObservationEffectStatus {
    Analyzed,
    NoDomainClaims,
    Refuted,
    QueryLimitReached,
    SolverUnknown,
    Inconsistent,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrivateDomainObservationEffect {
    /// C és P mellett igazolta a domaint, de C önmagában domainen kívüli értéket is megenged.
    ObservationDependent,
    /// A domaint már C-ből igazolta; a publikus adatok minden más hatásának hiányát ebből nem állapítja meg.
    AlreadyImplied,
    /// A megadott megfigyelések mellett a teljes eredeti modellből domainen kívüli értéket talált.
    Refuted,
    NoDomainClaim,
    Unresolved,
    Inconsistent,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrivateObservationEffect {
    pub cell: CellId,
    pub domain: Option<UcpValueDomain>,
    pub effect: PrivateDomainObservationEffect,
    /// A lefedést a konkrét megfigyelések mellett függetlenül igazolta, a kontrollvizsgálat hiányossága mellett is.
    pub observed_domain_verified: bool,
    /// P nélkül megvalósítható értéket tárol; P melletti megvalósíthatóságot vagy új titokvisszaállítást nem állít.
    pub unobserved_counterexample: Option<BigInt>,
    pub observed_counterexample: Option<BigInt>,
    pub limitation: Option<RecoveryLimitation>,
}

#[derive(Debug)]
pub struct PublicObservationEffectReport {
    pub status: PublicObservationEffectStatus,
    pub cells: Vec<PrivateObservationEffect>,
    pub public_values: Vec<(CellId, BigInt)>,
    /// A három alábbi számlálóra bontja az összes hívást; nem végez rejtett ismétlést vagy tartalékpróbát.
    pub solver_checks: usize,
    pub satisfiability_checks: usize,
    pub observed_domain_checks: usize,
    pub unobserved_domain_checks: usize,
    pub elapsed: Duration,
    pub options: PublicObservationEffectOptions,
}

/// Előbb C és P mellett függetlenül ellenőrzi a domaint, majd C önálló következményeként is vizsgálja.
/// Mindkét kontextust friss SMT-kódolásból rögzíti, UCP-tények és SAT-jelöltek beírása előtt.
/// A riportot, K-t és Deltát nem módosítja; a bizonytalan eredményt hiányos bizonyítékként kezeli.
pub fn analyze_public_observation_effect<F, ConcreteCircuit>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    recovery: &PrivacyAnalysisReport,
    options: PublicObservationEffectOptions,
) -> Result<PublicObservationEffectReport>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
{
    let started = Instant::now();
    let options = PublicObservationEffectOptions {
        solver_timeout_ms: Analyzer::<F>::resolve_smt_timeout_ms(
            options
                .solver_timeout_ms
                .or(recovery.options.solver_timeout_ms),
        )?,
        ..options
    };
    let mut context = prepare_privacy_analysis::<F, _, _>(
        circuit,
        k,
        analyzer_input,
        recovery.cells.iter().map(|cell| cell.cell.clone()),
    )?;
    ensure!(
        context.private_cells.len() == recovery.cells.len(),
        "Duplicate cells in recovery report"
    );
    ensure!(
        context.public_values == recovery.public_values,
        "Recovery report and observation control must use the same public observations"
    );
    // C-t a prepare_ucp_query_context P-t beíró lépése előtt rögzíti, szöveges szűrés nélkül.
    let unobserved = context
        .analyzer
        .original_private_query_context_without_observations(
            &context.analyzer_input,
            &context.private_cells,
        )?;
    let observed = context
        .analyzer
        .original_private_query_context(&context.analyzer_input, &context.private_cells)?;
    let mut control = classify_effects(
        recovery
            .cells
            .iter()
            .map(|cell| (cell.cell.clone(), cell.domain.clone()))
            .collect(),
        context.public_values,
        &context.problem.field_modulus,
        options,
        || observed.check_satisfiability::<F>(options.solver_timeout_ms),
        |cell, blocked, with_observations| {
            let original = if with_observations {
                &observed
            } else {
                &unobserved
            };
            original.query_unseen_value::<F>(cell, blocked, options.solver_timeout_ms)
        },
    )?;
    control.elapsed = started.elapsed();
    Ok(control)
}

// A valódi SMT-hívásokhoz és a determinisztikus hibatesztekhez ugyanazt a keret- és minősítéskezelést használja.
fn classify_effects(
    claims: Vec<(CellId, Option<UcpValueDomain>)>,
    public_values: Vec<(CellId, BigInt)>,
    modulus: &BigInt,
    options: PublicObservationEffectOptions,
    initial_sat: impl FnOnce() -> Result<Satisfiability>,
    mut query: impl FnMut(&CellId, &BTreeSet<BigInt>, bool) -> Result<Option<BigInt>>,
) -> Result<PublicObservationEffectReport> {
    let started = Instant::now();
    let mut cells: Vec<_> = claims
        .into_iter()
        .map(|(cell, domain)| PrivateObservationEffect {
            cell,
            effect: if domain.is_some() {
                PrivateDomainObservationEffect::Unresolved
            } else {
                PrivateDomainObservationEffect::NoDomainClaim
            },
            domain,
            observed_domain_verified: false,
            unobserved_counterexample: None,
            observed_counterexample: None,
            limitation: None,
        })
        .collect();
    let mut solver_checks = 0;
    let mut satisfiability_checks = 0;
    let mut observed_domain_checks = 0;
    let mut unobserved_domain_checks = 0;
    let initial_failure = if options.max_solver_checks == 0 {
        Some((
            PublicObservationEffectStatus::QueryLimitReached,
            RecoveryLimitation::QueryLimit,
        ))
    } else {
        solver_checks += 1;
        satisfiability_checks += 1;
        match initial_sat() {
            Ok(Satisfiability::Satisfiable) => None,
            Ok(Satisfiability::Unsatisfiable) => Some((
                PublicObservationEffectStatus::Inconsistent,
                RecoveryLimitation::InconsistentContext,
            )),
            Err(error) => Some((
                PublicObservationEffectStatus::SolverUnknown,
                limitation_from_solver_error(error)?,
            )),
        }
    };
    let status = if let Some((status, limitation)) = initial_failure {
        for cell in cells.iter_mut().filter(|cell| cell.domain.is_some()) {
            cell.limitation = Some(limitation.clone());
            if status == PublicObservationEffectStatus::Inconsistent {
                cell.effect = PrivateDomainObservationEffect::Inconsistent;
            }
        }
        status
    } else {
        for cell in &mut cells {
            let Some(domain) = &cell.domain else {
                continue;
            };
            let values: Vec<_> = match domain {
                UcpValueDomain::Exact(value) => vec![value.clone()],
                UcpValueDomain::FiniteSet(values) => values.iter().cloned().collect(),
            };
            ensure!(
                values.len() <= MAX_FINITE_DOMAIN_SIZE,
                "Observation control domain exceeds the finite size limit"
            );
            let blocked: BTreeSet<_> = values
                .into_iter()
                .map(|value| {
                    normalize_field_value(value, modulus)
                        .context("Unsupported observation-control domain value")
                })
                .collect::<Result<_>>()?;
            for with_observations in [true, false] {
                if solver_checks >= options.max_solver_checks {
                    cell.limitation = Some(RecoveryLimitation::QueryLimit);
                    break;
                }
                solver_checks += 1;
                observed_domain_checks += usize::from(with_observations);
                unobserved_domain_checks += usize::from(!with_observations);
                let answer = match query(&cell.cell, &blocked, with_observations) {
                    Ok(answer) => answer,
                    Err(error) => {
                        cell.limitation = Some(limitation_from_solver_error(error)?);
                        break;
                    }
                };
                let outside_value = answer
                    .map(|value| {
                        let value = normalize_field_value(value, modulus)
                            .context("Unsupported observation-control counterexample value")?;
                        ensure!(
                            !blocked.contains(&value),
                            "Observation control returned an excluded field value"
                        );
                        Ok(value)
                    })
                    .transpose()?;
                if with_observations {
                    if let Some(value) = outside_value {
                        cell.effect = PrivateDomainObservationEffect::Refuted;
                        cell.observed_counterexample = Some(value);
                        break;
                    }
                    cell.observed_domain_verified = true;
                } else {
                    cell.effect = if outside_value.is_some() {
                        PrivateDomainObservationEffect::ObservationDependent
                    } else {
                        PrivateDomainObservationEffect::AlreadyImplied
                    };
                    cell.unobserved_counterexample = outside_value;
                }
            }
        }
        if cells
            .iter()
            .any(|cell| cell.effect == PrivateDomainObservationEffect::Refuted)
        {
            PublicObservationEffectStatus::Refuted
        } else if cells
            .iter()
            .any(|cell| cell.limitation == Some(RecoveryLimitation::QueryLimit))
        {
            PublicObservationEffectStatus::QueryLimitReached
        } else if cells
            .iter()
            .any(|cell| cell.effect == PrivateDomainObservationEffect::Unresolved)
        {
            PublicObservationEffectStatus::SolverUnknown
        } else if cells
            .iter()
            .all(|cell| cell.effect == PrivateDomainObservationEffect::NoDomainClaim)
        {
            PublicObservationEffectStatus::NoDomainClaims
        } else {
            PublicObservationEffectStatus::Analyzed
        }
    };
    Ok(PublicObservationEffectReport {
        status,
        cells,
        public_values,
        solver_checks,
        satisfiability_checks,
        observed_domain_checks,
        unobserved_domain_checks,
        elapsed: started.elapsed(),
        options,
    })
}

impl fmt::Display for PublicObservationEffectReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Public observation control: {:?}; solver checks: {}; initial SAT: {}; observed exclusions: {}; unobserved exclusions: {}; elapsed: {:?}",
            self.status, self.solver_checks, self.satisfiability_checks, self.observed_domain_checks, self.unobserved_domain_checks, self.elapsed)?;
        writeln!(
            f,
            "Observation policy: {}; options: {:?}",
            PRIVACY_OBSERVATION_POLICY, self.options
        )?;
        for cell in &self.cells {
            writeln!(f, "{}: {:?}; domain: {:?}; observed coverage: {}; unobserved alternative: {:?}; observed refutation: {:?}; limitation: {:?}",
                cell.cell, cell.effect, cell.domain, cell.observed_domain_verified, cell.unobserved_counterexample, cell.observed_counterexample, cell.limitation)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_solver::smt_parser::{SolverUnknownDetails, UnknownSolverResult};

    fn claims() -> Vec<(CellId, Option<UcpValueDomain>)> {
        vec![(CellId::advice(0, 0), Some(UcpValueDomain::exact(7.into())))]
    }

    fn options(checks: usize) -> PublicObservationEffectOptions {
        PublicObservationEffectOptions {
            max_solver_checks: checks,
            solver_timeout_ms: Some(20),
        }
    }

    fn timeout() -> anyhow::Error {
        anyhow::anyhow!(UnknownSolverResult).context(SolverUnknownDetails {
            reason: Some("TIMEOUT".into()),
        })
    }

    #[test]
    fn control_distinguishes_intrinsic_and_observation_dependent_claims() {
        let mut claims = claims();
        claims.push((CellId::advice(1, 0), Some(UcpValueDomain::exact(7.into()))));
        let control = classify_effects(
            claims,
            vec![(CellId::instance(0, 0), 7.into())],
            &101.into(),
            options(5),
            || Ok(Satisfiability::Satisfiable),
            |cell, blocked, observed| {
                assert_eq!(blocked, &BTreeSet::from([7.into()]));
                Ok((!observed && cell.column == 1).then(|| 8.into()))
            },
        )
        .unwrap();
        assert_eq!(control.status, PublicObservationEffectStatus::Analyzed);
        assert_eq!(
            control.cells[0].effect,
            PrivateDomainObservationEffect::AlreadyImplied
        );
        assert_eq!(
            control.cells[1].effect,
            PrivateDomainObservationEffect::ObservationDependent
        );
        assert_eq!(control.cells[1].unobserved_counterexample, Some(8.into()));
        assert!(control
            .cells
            .iter()
            .all(|cell| cell.observed_domain_verified));
        assert_eq!(control.solver_checks, 5);
        assert_eq!(control.satisfiability_checks, 1);
        assert_eq!(control.observed_domain_checks, 2);
        assert_eq!(control.unobserved_domain_checks, 2);
    }

    #[test]
    fn every_check_including_initial_sat_consumes_the_hard_total() {
        for budget in 0..=3 {
            let actual = std::cell::Cell::new(0);
            let control = classify_effects(
                claims(),
                vec![],
                &101.into(),
                options(budget),
                || {
                    actual.set(actual.get() + 1);
                    Ok(Satisfiability::Satisfiable)
                },
                |_, _, observed| {
                    actual.set(actual.get() + 1);
                    Ok((!observed).then(|| 8.into()))
                },
            )
            .unwrap();
            assert_eq!(actual.get(), budget);
            assert_eq!(control.solver_checks, budget);
            assert_eq!(
                control.solver_checks,
                control.satisfiability_checks
                    + control.observed_domain_checks
                    + control.unobserved_domain_checks
            );
            if budget < 3 {
                assert_eq!(
                    control.status,
                    PublicObservationEffectStatus::QueryLimitReached
                );
                assert_eq!(
                    control.cells[0].effect,
                    PrivateDomainObservationEffect::Unresolved
                );
                assert_eq!(
                    control.cells[0].limitation,
                    Some(RecoveryLimitation::QueryLimit)
                );
                assert_eq!(control.cells[0].observed_domain_verified, budget == 2);
                assert!(control.cells[0].unobserved_counterexample.is_none());
            } else {
                assert_eq!(
                    control.cells[0].effect,
                    PrivateDomainObservationEffect::ObservationDependent
                );
            }
        }
    }

    #[test]
    fn initial_inconsistency_and_unknown_never_allow_exclusion_claims() {
        for inconsistent in [true, false] {
            let control = classify_effects(
                claims(),
                vec![],
                &101.into(),
                options(10),
                || {
                    if inconsistent {
                        Ok(Satisfiability::Unsatisfiable)
                    } else {
                        Err(timeout())
                    }
                },
                |_, _, _| unreachable!(),
            )
            .unwrap();
            assert_eq!(control.solver_checks, 1);
            assert_eq!(control.cells[0].observed_domain_verified, false);
            assert!(control.cells[0].unobserved_counterexample.is_none());
            assert_eq!(
                control.status,
                if inconsistent {
                    PublicObservationEffectStatus::Inconsistent
                } else {
                    PublicObservationEffectStatus::SolverUnknown
                }
            );
            assert_eq!(
                control.cells[0].effect,
                if inconsistent {
                    PrivateDomainObservationEffect::Inconsistent
                } else {
                    PrivateDomainObservationEffect::Unresolved
                }
            );
        }
    }

    #[test]
    fn unknown_at_either_exclusion_stage_stays_unresolved_and_does_not_block_other_cells() {
        for fail_observed in [true, false] {
            let mut claims = claims();
            claims.push((CellId::advice(1, 0), Some(UcpValueDomain::exact(7.into()))));
            let control = classify_effects(
                claims,
                vec![],
                &101.into(),
                options(5),
                || Ok(Satisfiability::Satisfiable),
                |cell, _, observed| {
                    if cell.column == 0 && observed == fail_observed {
                        Err(timeout())
                    } else {
                        Ok(None)
                    }
                },
            )
            .unwrap();
            assert_eq!(control.status, PublicObservationEffectStatus::SolverUnknown);
            assert_eq!(
                control.cells[0].effect,
                PrivateDomainObservationEffect::Unresolved
            );
            assert_eq!(control.cells[0].observed_domain_verified, !fail_observed);
            assert_eq!(
                control.cells[0].limitation,
                Some(RecoveryLimitation::SolverTimeout)
            );
            assert_eq!(
                control.cells[1].effect,
                PrivateDomainObservationEffect::AlreadyImplied
            );
            assert_eq!(control.solver_checks, if fail_observed { 4 } else { 5 });
        }
    }

    #[test]
    fn an_observed_refutation_skips_baseline_but_later_claims_are_still_checked() {
        let mut claims = claims();
        claims.push((CellId::advice(1, 0), Some(UcpValueDomain::exact(7.into()))));
        let mut calls = Vec::new();
        let control = classify_effects(
            claims,
            vec![],
            &101.into(),
            options(4),
            || Ok(Satisfiability::Satisfiable),
            |cell, _, observed| {
                calls.push((cell.column, observed));
                Ok((cell.column == 0).then(|| 8.into()))
            },
        )
        .unwrap();
        assert_eq!(calls, [(0, true), (1, true), (1, false)]);
        assert_eq!(control.status, PublicObservationEffectStatus::Refuted);
        assert_eq!(
            control.cells[0].effect,
            PrivateDomainObservationEffect::Refuted
        );
        assert_eq!(control.cells[0].observed_counterexample, Some(8.into()));
        assert!(!control.cells[0].observed_domain_verified);
        assert_eq!(
            control.cells[1].effect,
            PrivateDomainObservationEffect::AlreadyImplied
        );
        assert_eq!(control.solver_checks, 4);
    }

    #[test]
    fn absent_claims_do_not_turn_partial_samples_or_non_uniqueness_into_control_evidence() {
        let control = classify_effects(
            vec![(CellId::advice(0, 0), None)],
            vec![],
            &101.into(),
            options(10),
            || Ok(Satisfiability::Satisfiable),
            |_, _, _| unreachable!(),
        )
        .unwrap();
        assert_eq!(
            control.status,
            PublicObservationEffectStatus::NoDomainClaims
        );
        assert_eq!(
            control.cells[0].effect,
            PrivateDomainObservationEffect::NoDomainClaim
        );
        assert_eq!(control.solver_checks, 1);
    }

    #[test]
    fn malformed_solver_output_and_excluded_values_fail_closed() {
        for observed in [true, false] {
            assert!(classify_effects(
                claims(),
                vec![],
                &101.into(),
                options(3),
                || Ok(Satisfiability::Satisfiable),
                |_, _, stage| {
                    if stage == observed {
                        Err(anyhow::anyhow!("malformed solver output"))
                    } else {
                        Ok(None)
                    }
                }
            )
            .is_err());
        }
        assert!(classify_effects(
            claims(),
            vec![],
            &101.into(),
            options(3),
            || Err(anyhow::anyhow!("missing solver")),
            |_, _, _| unreachable!()
        )
        .is_err());
        assert!(classify_effects(
            claims(),
            vec![],
            &101.into(),
            options(3),
            || Ok(Satisfiability::Satisfiable),
            |_, _, _| Ok(Some(7.into()))
        )
        .is_err());
    }

    #[test]
    fn signed_domains_are_field_normalized_and_inherent_supersets_are_not_privacy_verdicts() {
        let control = classify_effects(
            vec![(
                CellId::advice(0, 0),
                Some(UcpValueDomain::exact(100.into())),
            )],
            vec![],
            &101.into(),
            options(3),
            || Ok(Satisfiability::Satisfiable),
            |_, blocked, observed| {
                assert_eq!(blocked, &BTreeSet::from([(-1).into()]));
                Ok((!observed).then(|| 98.into()))
            },
        )
        .unwrap();
        assert_eq!(
            control.cells[0].unobserved_counterexample,
            Some((-3).into())
        );
        assert_eq!(
            control.cells[0].effect,
            PrivateDomainObservationEffect::ObservationDependent
        );
        let broad = UcpValueDomain::finite_set([0, 1].map(BigInt::from)).unwrap();
        let control = classify_effects(
            vec![(CellId::advice(0, 0), Some(broad))],
            vec![],
            &101.into(),
            options(3),
            || Ok(Satisfiability::Satisfiable),
            |_, _, _| Ok(None),
        )
        .unwrap();
        // A teszt szerint P a {0,1} halmazon belül még szűkíthet; C-ből csak a vizsgált lefedési állítást igazolja.
        assert_eq!(
            control.cells[0].effect,
            PrivateDomainObservationEffect::AlreadyImplied
        );
    }

    #[test]
    fn oversized_domains_are_rejected_and_an_empty_domain_is_refutable() {
        let oversized = UcpValueDomain::FiniteSet((0..257).map(BigInt::from).collect());
        assert!(classify_effects(
            vec![(CellId::advice(0, 0), Some(oversized))],
            vec![],
            &1009.into(),
            options(3),
            || Ok(Satisfiability::Satisfiable),
            |_, _, _| unreachable!()
        )
        .is_err());
        let control = classify_effects(
            vec![(
                CellId::advice(0, 0),
                Some(UcpValueDomain::FiniteSet(BTreeSet::new())),
            )],
            vec![],
            &101.into(),
            options(3),
            || Ok(Satisfiability::Satisfiable),
            |_, blocked, _| {
                assert!(blocked.is_empty());
                Ok(Some(7.into()))
            },
        )
        .unwrap();
        assert_eq!(control.status, PublicObservationEffectStatus::Refuted);
        assert_eq!(control.solver_checks, 2);
    }
}
