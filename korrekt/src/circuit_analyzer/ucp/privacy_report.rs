//! Az elemzés eredményét típusokkal reprezentálja, összesíti és szövegesen megjeleníti.
//! Nem indít keresést és nem vezet le új tényt: a fő vezérléstől kapott
//! eredményből készít riportot. Hiányos eredményből nem állapít meg titkosságot.

use super::super::{
    cell::CellId,
    engine::UcpResult,
    privacy_discovery::{
        PrivacyDomainDiscoveryStatistics, PrivateDomainDiscovery, PRIVACY_DOMAIN_DISCOVERY_POLICY,
    },
    privacy_domain::{
        PrivacyDomainRefinementStatistics, PrivateDomainRefinement,
        PRIVACY_DOMAIN_REFINEMENT_POLICY,
    },
    privacy_subset::PRIVACY_TARGETED_SUBSET_POLICY,
    value::UcpValueDomain,
};
use super::{
    PrivacyAnalysisOptions, PRIVACY_SAT_HINT_POLICY, PRIVACY_SEARCH_POLICY,
    PRIVACY_SMT_DOMAIN_POLICY, PRIVACY_WITNESS_SAT_POLICY,
};
use num_bigint::BigInt;
use std::{fmt, time::Duration};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrivacyAnalysisStatus {
    /// Minden kiválasztott cellához értéket talált vagy próbát végzett; a visszaállítás ettől még hiányos lehet.
    Analyzed,
    QueryLimitReached,
    SolverUnknown,
    Inconsistent,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrivateCellUniqueness {
    Unique,
    /// Azonos megfigyelések mellett két, ebben a cellában eltérő kielégítő értékadást talált SMT-vel.
    NonUnique,
    /// Sem egyértelműséget, sem nemegyértelműséget nem igazolt; ebből nem állapít meg titkosságot.
    Unknown,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PrivacySearchStatistics {
    pub target_queries: usize,
    pub bridge_queries: usize,
    /// A köztes advice cellák tényleges domainkeresési hívásait számolja a köztes keret terhére.
    pub bridge_domain_checks: usize,
    /// A target_queries részeként számolja, nem további hívásszámként.
    pub retry_queries: usize,
    /// A visszaállítás UCP-futásait számolja, a szerkezeti alapállapotot és a kezdeti SAT-jelöltvizsgálatot nem.
    pub propagation_runs: usize,
    pub progress_rounds: usize,
    pub queries_without_progress: usize,
    /// Az érték és egyértelműségi vagy domainpróba nélkül maradt célokat számolja; ebből nem állapít meg titkosságot.
    pub unqueried_targets: usize,
    pub stop_reason: Option<PrivacySearchStopReason>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrivacySearchStopReason {
    TotalQueryLimit,
    NoProgressLimit,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrivateRecoveryStatus {
    Recovered,
    UniqueWithoutValue,
    NonUnique,
    Unresolved,
    UnsupportedValueRepresentation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RecoveryLimitation {
    QueryLimit,
    SolverTimeout,
    SolverUnknown { reason: Option<String> },
    ValueRepresentationLimit,
    DomainSizeLimit,
    NoConcreteValue,
    InconsistentContext,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrivateCellReport {
    pub cell: CellId,
    /// Csak az egyértelműségi próbákat számolja; a véges domain ellenőrzéseit külön vezeti.
    pub query_attempts: usize,
    pub uniqueness: PrivateCellUniqueness,
    pub domain: Option<UcpValueDomain>,
    /// A domain összes elemének megvalósíthatóságát igazolta az eredeti kielégíthető kontextusban.
    /// A független domainvalidátor csak a lefedést ellenőrzi, ezt a teljességi állítást nem.
    pub domain_is_complete: bool,
    /// Konkrét publikus megfigyelés nélkül kikövetkeztetett, szerkezeti korlátokat is tartalmazó domaint tárol.
    pub baseline_domain: Option<UcpValueDomain>,
    /// Az UCP-alapállapothoz mért szűkülést jelzi; azt SMT-következtetés is okozhatja.
    /// Ebből nem állapít meg mért entrópiaveszteséget vagy kizárólag publikus adat okozta szivárgást.
    /// A publikus függést az analyze_public_observation_effect külön eredeti SMT-kontrollja vizsgálja.
    pub domain_refined_from_baseline: bool,
    pub recovery_limitation: Option<RecoveryLimitation>,
    /// None esetén nem végzett végesdomain-szűkítést; ebből nem állapít meg teljességet.
    pub domain_refinement: Option<PrivateDomainRefinement>,
    /// A részleges értékfelsorolást modellmintaként tárolja, nem Delta-domaint állít elő belőle.
    pub domain_discovery: Option<PrivateDomainDiscovery>,
}

impl PrivateCellReport {
    /// A kategóriát az aktuális bizonyítékokból képezi, külön elavuló címke tárolása nélkül.
    pub fn recovery_status(&self) -> PrivateRecoveryStatus {
        if matches!(self.domain, Some(UcpValueDomain::Exact(_))) {
            PrivateRecoveryStatus::Recovered
        } else if self.recovery_limitation == Some(RecoveryLimitation::ValueRepresentationLimit) {
            PrivateRecoveryStatus::UnsupportedValueRepresentation
        } else {
            match self.uniqueness {
                PrivateCellUniqueness::Unique => PrivateRecoveryStatus::UniqueWithoutValue,
                PrivateCellUniqueness::NonUnique => PrivateRecoveryStatus::NonUnique,
                PrivateCellUniqueness::Unknown => PrivateRecoveryStatus::Unresolved,
            }
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PrivacyAnalysisSummary {
    pub private_cells: usize,
    pub exact_values: usize,
    pub finite_domains: usize,
    pub unique_cells: usize,
    pub non_unique_cells: usize,
    pub unresolved_uniqueness: usize,
    pub refined_domains: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SatisfiabilityEvidence {
    Smt,
    /// A teljes tanú Halo2-ellenőrzése sikeres volt az elemzés publikus megfigyeléseivel.
    VerifiedWitness,
}

#[derive(Debug)]
pub struct PrivacyAnalysisReport {
    pub status: PrivacyAnalysisStatus,
    pub cells: Vec<PrivateCellReport>,
    pub summary: PrivacyAnalysisSummary,
    pub public_values: Vec<(CellId, BigInt)>,
    pub semantic_queries: usize,
    pub search_statistics: PrivacySearchStatistics,
    pub domain_refinement_statistics: PrivacyDomainRefinementStatistics,
    pub domain_discovery_statistics: PrivacyDomainDiscoveryStatistics,
    /// A kezdeti SMT-s solverhívásokat számolja; sikeres MockProver-ellenőrzésnél nulla.
    pub satisfiability_checks: usize,
    /// A megoldás létezésének igazolását jelzi; a darabszám csak a kezdeti SMT-hívásokat számolja.
    pub satisfiability_evidence: Option<SatisfiabilityEvidence>,
    pub elapsed: Duration,
    /// A tényleges beállításokat a feloldott solveridőkerettel együtt tárolja az ismételhető mérésekhez.
    pub options: PrivacyAnalysisOptions,
    /// Következetlen kényszerrendszerhez nem jelent kikövetkeztetett tényeket.
    pub ucp_result: Option<UcpResult>,
}

// Az összesítésben külön kezeli az egyértelműséget és a konkrét érték visszaállítását.
pub(super) fn recovery_report(
    status: PrivacyAnalysisStatus,
    cells: Vec<PrivateCellReport>,
    public_values: Vec<(CellId, BigInt)>,
    mut search_statistics: PrivacySearchStatistics,
    elapsed: Duration,
    ucp_result: Option<UcpResult>,
    options: PrivacyAnalysisOptions,
) -> PrivacyAnalysisReport {
    let mut summary = PrivacyAnalysisSummary {
        private_cells: cells.len(),
        ..Default::default()
    };
    // A visszaállítás és az egyértelműség számlálóit nem adja össze, mert külön szempontokat mérnek.
    for cell in &cells {
        search_statistics.unqueried_targets += usize::from(
            cell.query_attempts == 0
                && cell.domain_refinement.is_none()
                && cell
                    .domain_discovery
                    .as_ref()
                    .is_none_or(|evidence| evidence.solver_checks == 0)
                && !matches!(cell.domain, Some(UcpValueDomain::Exact(_))),
        );
        match &cell.domain {
            Some(UcpValueDomain::Exact(_)) => summary.exact_values += 1,
            Some(UcpValueDomain::FiniteSet(_)) => summary.finite_domains += 1,
            None => {}
        }
        match cell.uniqueness {
            PrivateCellUniqueness::Unique => summary.unique_cells += 1,
            PrivateCellUniqueness::NonUnique => summary.non_unique_cells += 1,
            PrivateCellUniqueness::Unknown => summary.unresolved_uniqueness += 1,
        }
        summary.refined_domains += usize::from(cell.domain_refined_from_baseline);
    }
    PrivacyAnalysisReport {
        status,
        cells,
        summary,
        public_values,
        semantic_queries: search_statistics.target_queries + search_statistics.bridge_queries,
        search_statistics,
        domain_refinement_statistics: PrivacyDomainRefinementStatistics::default(),
        domain_discovery_statistics: PrivacyDomainDiscoveryStatistics::default(),
        satisfiability_checks: 1,
        satisfiability_evidence: None,
        elapsed,
        ucp_result,
        options,
    }
}

impl fmt::Display for PrivacyAnalysisReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Privacy analysis: {:?}", self.status)?;
        writeln!(f, "SMT domain export: {}", PRIVACY_SMT_DOMAIN_POLICY)?;
        let sat_policy =
            if self.satisfiability_evidence == Some(SatisfiabilityEvidence::VerifiedWitness) {
                PRIVACY_WITNESS_SAT_POLICY
            } else {
                PRIVACY_SAT_HINT_POLICY
            };
        writeln!(f, "Initial SAT policy: {}", sat_policy)?;
        if let Some(evidence) = &self.satisfiability_evidence {
            writeln!(f, "Satisfiability evidence: {:?}", evidence)?;
        }
        writeln!(f, "Search policy: {}", PRIVACY_SEARCH_POLICY)?;
        writeln!(
            f,
            "Limits: {} semantic queries; solver ms/check and process: {:?}",
            self.options.max_semantic_queries, self.options.solver_timeout_ms
        )?;
        writeln!(f, "Search limits: {:?}", self.options.search)?;
        if let Some(timeout) = self.options.initial_sat_timeout_ms {
            writeln!(f, "Initial SAT solver ms/check and process: {}", timeout)?;
        }
        writeln!(
            f,
            "Finite-domain refinement: {}; limits: {:?}; statistics: {:?}",
            PRIVACY_DOMAIN_REFINEMENT_POLICY,
            self.options.domain_refinement,
            self.domain_refinement_statistics
        )?;
        writeln!(
            f,
            "Domain discovery: {}; limits: {:?}; statistics: {:?}",
            PRIVACY_DOMAIN_DISCOVERY_POLICY,
            self.options.domain_discovery,
            self.domain_discovery_statistics
        )?;
        writeln!(
            f,
            "Targeted exclusion policy: {}",
            PRIVACY_TARGETED_SUBSET_POLICY
        )?;
        writeln!(f, "Search: targets={}; bridges={}; bridge domain checks={}; retries={}; propagation runs={}; progress rounds={}; queries since progress={}; unqueried targets={}; stop={:?}",
            self.search_statistics.target_queries, self.search_statistics.bridge_queries,
            self.search_statistics.bridge_domain_checks,
            self.search_statistics.retry_queries, self.search_statistics.propagation_runs,
            self.search_statistics.progress_rounds,
            self.search_statistics.queries_without_progress, self.search_statistics.unqueried_targets,
            self.search_statistics.stop_reason)?;
        writeln!(f, "Private cells: {}; exact: {}; finite domains: {}; unique: {}; non-unique: {}; unresolved: {}; refined domains: {}",
            self.summary.private_cells, self.summary.exact_values, self.summary.finite_domains,
            self.summary.unique_cells, self.summary.non_unique_cells, self.summary.unresolved_uniqueness,
            self.summary.refined_domains)?;
        writeln!(
            f,
            "Initial SAT checks: {}; SMT uniqueness queries: {}; refinement solver checks: {}; discovery solver checks: {}; elapsed: {:?}",
            self.satisfiability_checks, self.semantic_queries,
            self.domain_refinement_statistics.solver_checks, self.domain_discovery_statistics.solver_checks, self.elapsed
        )?;
        for cell in &self.cells {
            write!(
                f,
                "{}: {:?}; {:?}; attempts: {}; limitation: {:?}; ",
                cell.cell,
                cell.uniqueness,
                cell.recovery_status(),
                cell.query_attempts,
                cell.recovery_limitation
            )?;
            match &cell.domain {
                Some(UcpValueDomain::Exact(value)) => write!(f, "Exact({})", value)?,
                Some(UcpValueDomain::FiniteSet(values)) => write!(f, "Candidates({:?})", values)?,
                None => write!(f, "No recovered domain")?,
            }
            writeln!(
                f,
                "; domain complete: {}; inferred domain refinement: {}; finite-domain SMT evidence: {:?}; discovery evidence: {:?}",
                cell.domain_is_complete, cell.domain_refined_from_baseline, cell.domain_refinement, cell.domain_discovery
            )?;
        }
        Ok(())
    }
}
