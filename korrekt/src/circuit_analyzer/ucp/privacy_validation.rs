#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

//! Independent SMT checking of recovered values and candidate supersets.
//! This checks individual claims for the supplied circuit/public observations;
//! it is not a formal proof of the Rust implementation or the Halo2-to-SMT encoding.

use super::{
    cell::CellId,
    privacy::{check_sat, prepare_privacy_analysis, PrivacyAnalysisReport},
};
use crate::{
    circuit_analyzer::{
        analyzable::AnalyzableField, analyzer::DomainEntailmentResult, halo2_proofs_libs::Circuit,
    },
    io::analyzer_io_type::AnalyzerInput,
    smt_solver::smt_parser::Satisfiability,
};
use anyhow::{ensure, Result};
use num_bigint::BigInt;
use std::{
    fmt,
    time::{Duration, Instant},
};

pub(crate) const PRIVACY_VALIDATION_POLICY: &str = "original-subset-unsat-full-fallback";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DomainValidationStatus {
    Entailed,
    Refuted,
    NoDomainClaim,
    Inconsistent,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RecoveryValidationStatus {
    /// Every reported domain is entailed; cells without domains are not certified.
    VerifiedDomains,
    Refuted,
    NoDomainClaims,
    Inconsistent,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrivateDomainValidation {
    pub cell: CellId,
    pub status: DomainValidationStatus,
    /// A satisfying value outside the claimed domain, not a newly recovered secret.
    pub counterexample: Option<BigInt>,
}

#[derive(Debug)]
pub struct PrivateRecoveryValidationReport {
    pub status: RecoveryValidationStatus,
    pub cells: Vec<PrivateDomainValidation>,
    /// Checks absence of counterexamples after a shared original satisfiability check.
    pub domain_queries: usize,
    /// Actual initial SAT attempts plus subset/full exclusion checks.
    pub solver_checks: usize,
    /// Subset SAT/unknown is inconclusive; only subset UNSAT can certify exclusion.
    pub subset_checks: usize,
    pub elapsed: Duration,
}

/// Rebuilds SMT from the original circuit, using only concrete public observations.
/// No inferred domain, uniqueness fact, baseline or witness assignment is assumed.
/// Untrusted UCP candidates may guide original SAT only and are popped before exclusion.
/// A finite domain is checked as a superset: this does not certify each candidate
/// as feasible, nor certify the report's uniqueness or information-leakage labels.
/// Solver failures/unknown results propagate as errors, never as verification.
pub fn validate_private_recovery_report<F, ConcreteCircuit>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    report: &PrivacyAnalysisReport,
) -> Result<PrivateRecoveryValidationReport>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
{
    let started = Instant::now();
    let mut context = prepare_privacy_analysis::<F, _, _>(
        circuit,
        k,
        analyzer_input,
        report.cells.iter().map(|cell| cell.cell.clone()),
    )?;
    ensure!(
        context.private_cells.len() == report.cells.len(),
        "Duplicate cells in recovery report"
    );
    ensure!(
        context.public_values == report.public_values,
        "Recovery report and validation must use the same public observations"
    );
    //Fresh constraints, but the same per-check resource policy as the recovery run.
    context
        .analyzer
        .set_smt_timeout_ms(report.options.solver_timeout_ms)?;
    // Candidate-restricted SAT proves existence only; scopes are popped before checking any claim.
    let (satisfiable, mut solver_checks) = check_sat(&mut context);
    let satisfiable = satisfiable?;
    if satisfiable == Satisfiability::Unsatisfiable {
        return Ok(PrivateRecoveryValidationReport {
            status: RecoveryValidationStatus::Inconsistent,
            cells: report
                .cells
                .iter()
                .map(|cell| PrivateDomainValidation {
                    cell: cell.cell.clone(),
                    status: DomainValidationStatus::Inconsistent,
                    counterexample: None,
                })
                .collect(),
            domain_queries: 0,
            solver_checks,
            subset_checks: 0,
            elapsed: started.elapsed(),
        });
    }

    let mut cells = Vec::with_capacity(report.cells.len());
    let mut domain_queries = 0;
    let mut subset_checks = 0;
    for cell in &report.cells {
        let (status, counterexample) = if let Some(domain) = &cell.domain {
            domain_queries += 1;
            //Never call set_ucp_value_facts/set_ucp_unique_cells on this analyzer.
            let query = context.analyzer.query_private_domain_entailment_after_sat(
                &context.analyzer_input,
                &cell.cell,
                domain,
            )?;
            solver_checks += query.solver_checks;
            subset_checks += query.subset_checks;
            match query.result {
                DomainEntailmentResult::Entailed => (DomainValidationStatus::Entailed, None),
                DomainEntailmentResult::Counterexample(value) => {
                    (DomainValidationStatus::Refuted, Some(value))
                }
                DomainEntailmentResult::Inconsistent => {
                    anyhow::bail!("Validation context became inconsistent")
                }
            }
        } else {
            (DomainValidationStatus::NoDomainClaim, None)
        };
        cells.push(PrivateDomainValidation {
            cell: cell.cell.clone(),
            status,
            counterexample,
        });
    }
    let status = if cells
        .iter()
        .any(|cell| cell.status == DomainValidationStatus::Refuted)
    {
        RecoveryValidationStatus::Refuted
    } else if domain_queries == 0 {
        RecoveryValidationStatus::NoDomainClaims
    } else {
        RecoveryValidationStatus::VerifiedDomains
    };
    Ok(PrivateRecoveryValidationReport {
        status,
        cells,
        domain_queries,
        solver_checks,
        subset_checks,
        elapsed: started.elapsed(),
    })
}

impl fmt::Display for PrivateRecoveryValidationReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Independent domain validation: {:?}; domain queries: {}; solver checks: {}; subset checks: {}; elapsed: {:?}",
            self.status, self.domain_queries, self.solver_checks, self.subset_checks, self.elapsed)?;
        writeln!(f, "Validation policy: {}", PRIVACY_VALIDATION_POLICY)?;
        for cell in &self.cells {
            writeln!(
                f,
                "{}: {:?}; counterexample: {:?}",
                cell.cell, cell.status, cell.counterexample
            )?;
        }
        Ok(())
    }
}
