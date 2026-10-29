#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

//! A visszaállított értékeket és lefedő jelölthalmazokat független SMT-vizsgálattal ellenőrzi.
//! A megadott kapcsolás és publikus megfigyelések egyedi állításait ellenőrzi;
//! a Rust-megvalósítást vagy a Halo2-SMT-kódolást ezzel nem verifikálja formálisan.

use super::{
    cell::CellId,
    privacy::{check_sat, prepare_privacy_analysis, PrivacyAnalysisReport},
};
use crate::{
    circuit_analyzer::{
        analyzable::AnalyzableField,
        analyzer::{Analyzer, DomainEntailmentResult},
        halo2_proofs_libs::Circuit,
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
    /// Minden jelentett domain lefedését igazolta; domain nélküli cellát nem tanúsít.
    VerifiedDomains,
    Refuted,
    NoDomainClaims,
    Inconsistent,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrivateDomainValidation {
    pub cell: CellId,
    pub status: DomainValidationStatus,
    /// Az állított domainen kívüli kielégítő értéket tárolja, nem újonnan visszaállított titkot.
    pub counterexample: Option<BigInt>,
}

#[derive(Debug)]
pub struct PrivateRecoveryValidationReport {
    pub status: RecoveryValidationStatus,
    pub cells: Vec<PrivateDomainValidation>,
    /// Közös eredeti SAT-ellenőrzés után ellenpélda hiányát vizsgálja.
    pub domain_queries: usize,
    /// A kezdeti SAT-próbákat és a részhalmazos vagy teljes kizárási hívásokat számolja.
    pub solver_checks: usize,
    /// A részhalmaz SAT vagy bizonytalan eredményét nem tekinti döntésnek; kizárást csak UNSAT-ból igazol.
    pub subset_checks: usize,
    /// Hívásonkénti tényleges időkeretet tárol, a visszaállítási futás keretétől függetlenül.
    pub solver_timeout_ms: Option<u64>,
    pub elapsed: Duration,
}

/// Az eredeti kapcsolásból új SMT-kódolást épít, csak a konkrét publikus megfigyeléseket használva.
/// Kikövetkeztetett domaint, egyértelműségi tényt, alapállapotot vagy privát értékadást nem feltételez.
/// Az UCP-jelöltet csak az eredeti SAT-próbához használja, és kizárás előtt visszavonja.
/// A véges halmaz lefedését ellenőrzi; az egyes jelöltek megvalósíthatóságát,
/// a riport egyértelműségi címkéit és az információszivárgási minősítést ezzel nem tanúsítja.
/// A solverhibát és a bizonytalan választ hibaként adja tovább, nem sikeres ellenőrzésként.
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
    validate_private_recovery_report_with_timeout::<F, _>(circuit, k, analyzer_input, report, None)
}

/// Friss validálást végez opcionálisan felülírt, solverhívásonkénti időkerettel.
/// None esetén a visszaállítási időkeretet, majd az elemző környezeti alapértékét használja.
/// Az időkeret felülírásakor a premisszákat, állításokat és a visszaállítási riportot nem módosítja.
pub fn validate_private_recovery_report_with_timeout<F, ConcreteCircuit>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    report: &PrivacyAnalysisReport,
    solver_timeout_ms: Option<u64>,
) -> Result<PrivateRecoveryValidationReport>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
{
    let started = Instant::now();
    let solver_timeout_ms = Analyzer::<F>::resolve_smt_timeout_ms(
        solver_timeout_ms.or(report.options.solver_timeout_ms),
    )?;
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
    context.analyzer.set_smt_timeout_ms(solver_timeout_ms)?;
    // A jelölttel korlátozott SAT csak létezést igazol; minden állításvizsgálat előtt visszavonja a jelöltet.
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
            solver_timeout_ms,
            elapsed: started.elapsed(),
        });
    }

    let mut cells = Vec::with_capacity(report.cells.len());
    let mut domain_queries = 0;
    let mut subset_checks = 0;
    for cell in &report.cells {
        let (status, counterexample) = if let Some(domain) = &cell.domain {
            domain_queries += 1;
            // Ezen az analyzeren nem hívja a set_ucp_value_facts és set_ucp_unique_cells függvényt.
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
        solver_timeout_ms,
        elapsed: started.elapsed(),
    })
}

impl fmt::Display for PrivateRecoveryValidationReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Independent domain validation: {:?}; domain queries: {}; solver checks: {}; subset checks: {}; elapsed: {:?}",
            self.status, self.domain_queries, self.solver_checks, self.subset_checks, self.elapsed)?;
        writeln!(f, "Validation policy: {}", PRIVACY_VALIDATION_POLICY)?;
        writeln!(
            f,
            "Validation solver timeout ms/invocation: {:?}",
            self.solver_timeout_ms
        )?;
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
