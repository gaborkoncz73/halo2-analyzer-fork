#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

//! A megadott privát bemenetek visszaállíthatóságát vizsgálja rögzített publikus megfigyelések mellett.
//! A privát advice értékadást nem használja visszaállított értékként. A véges domainekkel
//! lefedő halmazokat tárol; opcionális SMT-kereséssel teljes értékhalmazt is igazolhat.
//! A domainek méretéből és a cellák számából nem állapít meg kriptográfiai biztonságot.
//! Az eredményt a megadott megfigyelésekre adja, nem az összes állításra vagy a protokoll zéró tudású tulajdonságára.

use super::{
    cell::{CellId, CellKind},
    engine::UcpResult,
    extractor::{extract_ucp_problem, UcpProblem},
    facts::UcpFacts,
    privacy_discovery::{
        full_discovery_response, DiscoveryProbe, DiscoveryResponse, DomainDiscoveryState,
        PrivacyDomainDiscoveryOptions,
    },
    privacy_domain::{DomainRefinementState, PrivacyDomainRefinementOptions},
    privacy_search::{
        choose_action, shortlist_actions, ProbePlan, RecoveryAction, RecoveryEvidence,
        RecoverySearchState, RecoveryStrategy,
    },
    value::{normalize_field_value, parse_cell_id, UcpValueDomain, UcpValueFacts},
};
use crate::{
    circuit_analyzer::{
        analyzable::{Analyzable, AnalyzableField},
        analyzer::{
            Analyzer, OriginalPrivateQueryContext, PrivateSearchExactFacts, SemanticQueryOutput,
            SemanticQueryResult, ValueRecoveryFailure,
        },
        halo2_proofs_libs::*,
    },
    io::analyzer_io_type::{AnalyzerInput, AnalyzerType, LookupMethod, VerificationMethod},
    smt_solver::smt_parser::{Satisfiability, SolverUnknownDetails, UnknownSolverResult},
};
use anyhow::{ensure, Context, Result};
use num_bigint::BigInt;
use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    fmt,
    time::{Duration, Instant},
};

// A riporttípusokat külön modulból exportálja újra a privacy::... elérési úton.
#[path = "privacy_report.rs"]
mod report;
use report::recovery_report;
pub use report::{
    PrivacyAnalysisReport, PrivacyAnalysisStatus, PrivacyAnalysisSummary, PrivacySearchStatistics,
    PrivacySearchStopReason, PrivateCellReport, PrivateCellUniqueness, PrivateRecoveryStatus,
    RecoveryLimitation, SatisfiabilityEvidence,
};

pub(crate) const PRIVACY_SMT_DOMAIN_POLICY: &str = "exact-and-new-or-refined-domains";
pub(crate) const PRIVACY_SAT_HINT_POLICY: &str =
    "target-exact-ucp-hints-positive-only-original-fallback";
pub(crate) const PRIVACY_WITNESS_SAT_POLICY: &str =
    "mock-prover-positive-only-original-smt-fallback";
pub(crate) const PRIVACY_SEARCH_POLICY: &str = "refine-discover-complete-domain-v4";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrivacyAnalysisOptions {
    /// A szemantikai próbák összesített korlátját adja, köztes cellákkal és újrapróbálkozásokkal együtt; nem nullázódik.
    pub max_semantic_queries: usize,
    /// A CVC5 egy solverhívására ellenőrzési időkorlátot és felügyelt futásidőkeretet állít be.
    /// None esetén a HALO2_ANALYZER_SMT_TIMEOUT_MS környezeti változót veszi alapul.
    /// A teljes elemzés, szintézis és UCP-futás idejét nem korlátozza ezzel.
    pub solver_timeout_ms: Option<u64>,
    /// Csak a kezdeti SAT-vizsgálat solverhívásainak ad külön időkeretet.
    /// None esetén az általános solveridőkeretet használja; a későbbi kereséseket nem módosítja.
    pub initial_sat_timeout_ms: Option<u64>,
    pub search: PrivacySearchOptions,
    /// A véges domainek ellenőrzését külön, összesített solverhíváskerettel engedélyezi.
    pub domain_refinement: PrivacyDomainRefinementOptions,
    /// Domain nélküli cellákra opcionális eredeti modellbeli értékfelsorolást engedélyez.
    pub domain_discovery: PrivacyDomainDiscoveryOptions,
}

impl Default for PrivacyAnalysisOptions {
    fn default() -> Self {
        Self {
            max_semantic_queries: 256,
            solver_timeout_ms: None,
            initial_sat_timeout_ms: None,
            search: PrivacySearchOptions::default(),
            domain_refinement: PrivacyDomainRefinementOptions::default(),
            domain_discovery: PrivacyDomainDiscoveryOptions::default(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrivacySearchOptions {
    /// A köztes cellák vizsgálatára szemantikai próbákat és domainkeresési solverhívásokat számol.
    /// Az első célcellapróbák keretét külön fenntartja; nem általános solverhíváskorlátot jelent.
    pub max_bridge_queries: usize,
    /// A köztes munkát és az újrapróbálkozást korlátozza, az első célcellapróbát nem tiltja le.
    pub max_queries_without_progress: usize,
    /// Bizonytalan célcellapróbát csak előrelépés vagy nagyobb időkeret mellett ismételhet.
    pub max_retries_per_target: usize,
    /// Az újrapróbálkozás időkeretének alsó határát adja; a kezdeti keretet nem csökkenti.
    pub retry_solver_timeout_ms: Option<u64>,
}

impl Default for PrivacySearchOptions {
    fn default() -> Self {
        Self {
            max_bridge_queries: 32,
            max_queries_without_progress: 32,
            max_retries_per_target: 1,
            retry_solver_timeout_ms: Some(10_000),
        }
    }
}

impl PrivacyAnalysisOptions {
    pub(super) fn retry_timeout_ms(&self) -> Option<u64> {
        self.solver_timeout_ms
            .map(|initial| initial.max(self.search.retry_solver_timeout_ms.unwrap_or(initial)))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnsupportedPrivacyFeature {
    InlineLookupsRequired,
    FixedUnrotatedTablesRequired,
}

impl fmt::Display for UnsupportedPrivacyFeature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InlineLookupsRequired => {
                "Privacy analysis requires inline lookup constraints for validated witnesses"
            }
            Self::FixedUnrotatedTablesRequired => {
                "Privacy analysis requires concrete, unrotated fixed lookup tables"
            }
        })
    }
}

impl std::error::Error for UnsupportedPrivacyFeature {}

// Az előkészítés UCP-problémát és SMT-analyzert ad ugyanahhoz a kapcsoláshoz.
// A tényleges visszaállítás eredményeit csak a recover_private_inputs SAT-ellenőrzése után jelenti.
pub(crate) struct PrivacyAnalysisContext<F: AnalyzableField> {
    pub problem: UcpProblem,
    pub analyzer: Analyzer<F>,
    pub analyzer_input: AnalyzerInput,
    pub public_values: Vec<(CellId, BigInt)>,
    pub private_cells: Vec<CellId>,
    // Csak sikeres, azonos publikus megfigyelésekkel végzett MockProver-ellenőrzés után lesz igaz.
    witness_verified: bool,
}

// Az instance-hézagokat csak a tanúellenőrzéshez tölti ki nullával.
// A kitöltést nem adja át a publikus SMT-premisszáknak vagy a visszaállítási állapotnak.
fn witness_instances<F: AnalyzableField>(
    context: &PrivacyAnalysisContext<F>,
    k: u32,
) -> Option<Vec<Vec<F>>> {
    let mut cs = context.analyzer.cs.clone();
    // A CS-másolat következő instance-indexéből olvassa az oszlopok számát; az eredetit nem módosítja.
    let columns = cs.instance_column().index();
    let rows = 1usize
        .checked_shl(k)?
        .checked_sub(cs.blinding_factors() + 1)?;
    let mut instances = vec![Vec::new(); columns];
    for (cell, value) in &context.public_values {
        let row = usize::try_from(cell.row).ok()?;
        if cell.kind != CellKind::Instance || row >= rows {
            return None;
        }
        let column = instances.get_mut(cell.column)?;
        column.resize(column.len().max(row + 1), F::ZERO);
        let magnitude = F::from_str_vartime(&value.magnitude().to_string())?;
        column[row] = if value.sign() == num_bigint::Sign::Minus {
            -magnitude
        } else {
            magnitude
        };
    }
    Some(instances)
}

fn check_sat_with_witness<F, ConcreteCircuit>(
    context: &mut PrivacyAnalysisContext<F>,
    circuit: &ConcreteCircuit,
    k: u32,
) -> (Result<Satisfiability>, usize)
where
    F: AnalyzableField + Ord,
    ConcreteCircuit: Circuit<F>,
{
    let verified = witness_instances(context, k)
        .and_then(|instances| MockProver::run(k, circuit, instances).ok())
        .is_some_and(|prover| prover.verify().is_ok());
    if verified {
        // Csak a létezés igazolását őrzi meg; a prover tanúértékeit és modelljét eldobja.
        context.witness_verified = true;
        (Ok(Satisfiability::Satisfiable), 0)
    } else {
        // Egy hibás vagy hiányos tanú nem bizonyít kielégíthetetlenséget.
        check_sat(context)
    }
}

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
#[path = "tests/privacy_witness_tests.rs"]
mod witness_tests;

// A jelölteket csak a létezési SAT-próba gyorsítására használja, nem visszaállítási premisszaként.
pub(crate) fn check_sat<F: AnalyzableField>(
    context: &mut PrivacyAnalysisContext<F>,
) -> (Result<Satisfiability>, usize) {
    context.witness_verified = false;
    let mut values = context.problem.initial_value_facts.clone();
    for (cell, value) in &context.public_values {
        values.mark_known(cell.clone(), value.clone());
    }
    let candidates = context
        .problem
        .analyze_with_values(context.problem.initial_facts.clone(), values);
    let hinted = if context
        .private_cells
        .iter()
        .any(|cell| candidates.value_facts.known_value(cell).is_some())
    {
        context
            .analyzer
            .check_ucp_satisfiability_with_hints(&context.analyzer_input, &candidates.value_facts)
    } else {
        // Ha csak szerkezeti konstansokat ismer, kihagyja az újabb, várhatóan haszontalan jelöltpróbát.
        Ok(None)
    };
    let hint_checks = usize::from(!matches!(&hinted, Ok(None)));
    match accept_sat_hint(hinted) {
        Ok(true) => (Ok(Satisfiability::Satisfiable), hint_checks),
        Ok(false) => (
            context
                .analyzer
                .check_ucp_satisfiability(&context.analyzer_input),
            hint_checks + 1,
        ),
        Err(error) => (Err(error), hint_checks),
    }
}

fn accept_sat_hint(result: Result<Option<Satisfiability>>) -> Result<bool> {
    match result {
        Ok(Some(Satisfiability::Satisfiable)) => Ok(true),
        Ok(None | Some(Satisfiability::Unsatisfiable)) => Ok(false),
        Err(error) if error.downcast_ref::<UnknownSolverResult>().is_some() => Ok(false),
        Err(error) => Err(error),
    }
}

// A visszaállításhoz és a független ellenőrzéshez ugyanazt a támogatott publikus felületet készíti elő.
pub(crate) fn prepare_privacy_analysis<F, ConcreteCircuit, I>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    private_cells: I,
) -> Result<PrivacyAnalysisContext<F>>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
    I: IntoIterator<Item = CellId>,
{
    prepare_privacy_analysis_with_capture(circuit, k, analyzer_input, private_cells, false)
}

pub(crate) fn prepare_privacy_analysis_with_capture<F, ConcreteCircuit, I>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    private_cells: I,
    capture_original: bool,
) -> Result<PrivacyAnalysisContext<F>>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
    I: IntoIterator<Item = CellId>,
{
    analyzer_input.verification_input.validate_public_values()?;
    let private_cells: Vec<_> = private_cells
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    ensure!(
        !private_cells.is_empty(),
        "Select at least one private advice cell"
    );
    let analyzable = Analyzable::config_and_synthesize(circuit, k)
        .context("Failed to synthesize circuit for privacy analysis")?;
    if !analyzable.cs.lookups.is_empty()
        && analyzer_input.lookup_method != LookupMethod::InlineConstraints
    {
        return Err(UnsupportedPrivacyFeature::InlineLookupsRequired.into());
    }
    // Az egyenletbe ágyazott lookup-kódoláshoz konkrét, rotáció nélküli táblázatoszlopokat követel meg.
    if !analyzable.cs.lookups.iter().all(|lookup| {
        lookup
            .table_expressions
            .iter()
            .all(|expr| matches!(expr, Expression::Fixed(query) if query.rotation.0 == 0))
    }) {
        return Err(UnsupportedPrivacyFeature::FixedUnrotatedTablesRequired.into());
    }
    let problem = extract_ucp_problem(&analyzable);
    let witnesses: HashSet<_> = problem.witness_cells.iter().collect();
    for cell in &private_cells {
        ensure!(
            cell.kind == CellKind::Advice && witnesses.contains(cell),
            "Private cell {} is not an assigned or referenced advice cell",
            cell
        );
    }

    let mut public_values = BTreeMap::new();
    for (name, value) in &analyzer_input.verification_input.instance_cells {
        let cell =
            parse_cell_id(name).with_context(|| format!("Invalid public cell name: {}", name))?;
        ensure!(
            cell.kind == CellKind::Instance && cell.to_string() == *name,
            "Public observations must name instance cells, not private witnesses: {}",
            name
        );
        let value = normalize_field_value(value.clone(), &problem.field_modulus)
            .context("Public observation is outside the supported value range")?;
        public_values.insert(cell, value);
    }
    ensure!(
        public_values.is_empty()
            || analyzer_input.verification_method == VerificationMethod::Specific,
        "Concrete public observations require Specific verification"
    );
    // A publikus értékeket az Analyzer::new előtt ellenőrzi, hogy elkerülje az interaktív bekérést.
    for cell in problem.initial_facts.unique_cells() {
        if cell.kind == CellKind::Instance {
            ensure!(
                public_values.contains_key(cell),
                "Missing concrete public observation for {}",
                cell
            );
        }
    }
    // Üres Specific értéktérképnél letiltja az interaktív adatbekérési útvonalat.
    let mut effective_input = analyzer_input.clone();
    if effective_input.verification_input.instance_cells.is_empty() {
        effective_input.verification_method = VerificationMethod::None;
    }
    let analyzer_input = &effective_input;
    let analyzer = Analyzer::<F>::new_with_original_subset_capture(
        circuit,
        k,
        AnalyzerType::UnderconstrainedCircuit,
        Some(analyzer_input),
        capture_original,
    )
    .context("Failed to initialize privacy SMT analyzer")?;
    // A lookupokból származó, kapukifejezésekben nem szereplő publikus lekérdezéseket is ellenőrzi.
    for name in &analyzer.all_variables {
        if name.starts_with("I-") {
            ensure!(
                analyzer_input
                    .verification_input
                    .instance_cells
                    .contains_key(name),
                "Missing concrete public observation for {}",
                name
            );
        }
    }
    let public_values: Vec<_> = public_values.into_iter().collect();
    Ok(PrivacyAnalysisContext {
        problem,
        analyzer,
        analyzer_input: effective_input,
        public_values,
        private_cells,
        witness_verified: false,
    })
}

/// A publikus megfigyeléseket az instance_cells leképezésből olvassa, az instance oszlopon
/// közölt kimeneteket is beleértve. A privát célokat explicit advice cellákból választja ki;
/// több lehetséges privát értékadásból önmagában nem állapít meg alulkényszerezett kimenetet.
pub fn analyze_private_recoverability<F, ConcreteCircuit, I>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    private_cells: I,
    options: PrivacyAnalysisOptions,
) -> Result<PrivacyAnalysisReport>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
    I: IntoIterator<Item = CellId>,
{
    analyze_private_recoverability_with_initial_check(
        circuit,
        k,
        analyzer_input,
        private_cells,
        options,
        check_sat,
    )
}

/// A tényleges tanút azonos publikus megfigyelések mellett ellenőrzi MockProverrel.
/// Siker esetén csak a létezést igazolja; a tanúértékeket nem használja a visszaállításhoz.
/// Sikertelen vagy nem elvégezhető ellenőrzésnél az eredeti SMT-s SAT-vizsgálatra tér át.
pub fn analyze_private_recoverability_with_witness<F, ConcreteCircuit, I>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    private_cells: I,
    options: PrivacyAnalysisOptions,
) -> Result<PrivacyAnalysisReport>
where
    F: AnalyzableField + Ord,
    ConcreteCircuit: Circuit<F>,
    I: IntoIterator<Item = CellId>,
{
    analyze_private_recoverability_with_initial_check(
        circuit,
        k,
        analyzer_input,
        private_cells,
        options,
        |context| check_sat_with_witness(context, circuit, k),
    )
}

fn analyze_private_recoverability_with_initial_check<F, ConcreteCircuit, I>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    private_cells: I,
    options: PrivacyAnalysisOptions,
    initial_check: impl FnOnce(&mut PrivacyAnalysisContext<F>) -> (Result<Satisfiability>, usize),
) -> Result<PrivacyAnalysisReport>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
    I: IntoIterator<Item = CellId>,
{
    let started = Instant::now();
    // A beállításokat szintézis előtt ellenőrzi; az explicit opciókat a környezeti alapérték elé helyezi.
    ensure!(
        options.initial_sat_timeout_ms != Some(0),
        "Initial SAT solver timeout must be greater than zero"
    );
    let effective_timeout = Analyzer::<F>::resolve_smt_timeout_ms(options.solver_timeout_ms)?;
    let options = PrivacyAnalysisOptions {
        solver_timeout_ms: effective_timeout,
        ..options
    };
    ensure!(
        options.search.retry_solver_timeout_ms != Some(0),
        "Retry solver timeout must be greater than zero"
    );
    options.domain_refinement.validate()?;
    options.domain_discovery.validate()?;
    let mut context = prepare_privacy_analysis_with_capture::<F, _, _>(
        circuit,
        k,
        analyzer_input,
        private_cells,
        options.domain_discovery.max_solver_checks > 0
            && options.domain_discovery.use_targeted_subsets,
    )?;
    context
        .analyzer
        .set_smt_timeout_ms(options.solver_timeout_ms)?;
    recover_private_inputs(
        context,
        options,
        started,
        initial_check,
        |analyzer, input, cell| analyzer.query_ucp_cell_uniqueness_with_value(input, cell),
    )
}

// Az eredeti SMT-premisszák pillanatképe külön marad a később megtanult keresési tényektől.
fn original_context<F: AnalyzableField>(
    analyzer: &mut Analyzer<F>,
    analyzer_input: &AnalyzerInput,
    problem: &UcpProblem,
    private_cells: &[CellId],
    options: &PrivacyAnalysisOptions,
) -> Result<(Vec<CellId>, Option<OriginalPrivateQueryContext>)> {
    // Az eredeti premisszák pillanatképét nem módosítja a kereséshez hozzáadott pontos tényekkel.
    let snapshot_cells: Vec<_> = private_cells
        .iter()
        .chain(problem.witness_cells.iter())
        .filter(|cell| cell.kind == CellKind::Advice)
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let snapshot = if options.domain_refinement.max_solver_checks > 0
        || options.domain_discovery.max_solver_checks > 0
    {
        Some(analyzer.original_private_query_context(analyzer_input, &snapshot_cells)?)
    } else {
        None
    };
    Ok((snapshot_cells, snapshot))
}

fn initialize_knowledge(
    problem: &UcpProblem,
    public_values: &[(CellId, BigInt)],
) -> (UcpResult, UcpFacts, UcpValueFacts) {
    // Szerkezeti UCP-alapállapotot számít; a publikus hatást külön SMT-kontrollal vizsgálja.
    let baseline = problem.analyze_with_values(
        problem.initial_facts.clone(),
        problem.initial_value_facts.clone(),
    );
    let facts = baseline.facts.clone();
    let mut values = baseline.value_facts.clone();
    for (cell, value) in public_values {
        values.mark_known(cell.clone(), value.clone());
    }
    (baseline, facts, values)
}

fn propagate_to_fixpoint(
    problem: &UcpProblem,
    facts: UcpFacts,
    values: UcpValueFacts,
    search: &mut RecoverySearchState,
) -> UcpResult {
    let result = problem.analyze_with_values(facts, values);
    search.statistics.propagation_runs += 1;
    result
}

fn established_exact_facts<F: AnalyzableField>(
    original: Option<&OriginalPrivateQueryContext>,
    analyzer: &Analyzer<F>,
    values: &UcpValueFacts,
) -> Result<PrivateSearchExactFacts> {
    original
        .map(|snapshot| snapshot.search_exact_facts(analyzer, values))
        .transpose()
        .map(Option::unwrap_or_default)
}

fn diagnostic_report(
    private_cells: Vec<CellId>,
    public_values: Vec<(CellId, BigInt)>,
    status: PrivacyAnalysisStatus,
    limitation: RecoveryLimitation,
    elapsed: Duration,
    options: PrivacyAnalysisOptions,
) -> PrivacyAnalysisReport {
    let cells = private_cells
        .into_iter()
        .map(|cell| PrivateCellReport {
            cell,
            query_attempts: 0,
            uniqueness: PrivateCellUniqueness::Unknown,
            domain: None,
            domain_is_complete: false,
            baseline_domain: None,
            domain_refined_from_baseline: false,
            recovery_limitation: Some(limitation.clone()),
            domain_refinement: None,
            domain_discovery: None,
        })
        .collect();
    recovery_report(
        status,
        cells,
        public_values,
        PrivacySearchStatistics::default(),
        elapsed,
        None,
        options,
    )
}

// A solverhívásokat paraméterként kapja, így a teszt és az éles futás ugyanazt a vezérlést használja.
// Fő vezérlés: SAT -> UCP-fixpont -> műveletválasztás -> SMT -> beolvasztás.
// Csak új K/Delta-tény indít rendes propagációt; az ütemezés részletei a privacy_search.rs-ben vannak.
fn recover_private_inputs<F: AnalyzableField>(
    mut context: PrivacyAnalysisContext<F>,
    options: PrivacyAnalysisOptions,
    started: Instant,
    check_sat: impl FnOnce(&mut PrivacyAnalysisContext<F>) -> (Result<Satisfiability>, usize),
    mut query: impl FnMut(&mut Analyzer<F>, &AnalyzerInput, &CellId) -> Result<SemanticQueryOutput>,
) -> Result<PrivacyAnalysisReport> {
    let recovery_timeout = context.analyzer.smt_timeout_ms();
    if let Some(timeout) = options.initial_sat_timeout_ms {
        context.analyzer.set_smt_timeout_ms(Some(timeout))?;
    }
    let (initial_check, satisfiability_checks) = check_sat(&mut context);
    // A SAT-próba eredményétől függetlenül visszaállítja a későbbi keresések időkeretét.
    context.analyzer.set_smt_timeout_ms(recovery_timeout)?;
    let PrivacyAnalysisContext {
        problem,
        mut analyzer,
        analyzer_input,
        public_values,
        private_cells,
        witness_verified,
    } = context;
    let analyzer_input = &analyzer_input;
    let initial_failure = match initial_check {
        Ok(Satisfiability::Satisfiable) => None,
        Ok(Satisfiability::Unsatisfiable) => Some((
            PrivacyAnalysisStatus::Inconsistent,
            RecoveryLimitation::InconsistentContext,
        )),
        Err(error) => Some((
            PrivacyAnalysisStatus::SolverUnknown,
            limitation_from_solver_error(error)?,
        )),
    };
    if let Some((status, limitation)) = initial_failure {
        let mut report = diagnostic_report(
            private_cells,
            public_values,
            status,
            limitation,
            started.elapsed(),
            options,
        );
        report.satisfiability_checks = satisfiability_checks;
        return Ok(report);
    }

    let (snapshot_cells, original_context) = original_context(
        &mut analyzer,
        analyzer_input,
        &problem,
        &private_cells,
        &options,
    )?;
    let mut domain_search = DomainRefinementState::new(options.domain_refinement);
    let mut discovery = DomainDiscoveryState::new(options.domain_discovery);

    let (baseline, facts, values) = initialize_knowledge(&problem, &public_values);
    let private_set: HashSet<_> = private_cells.iter().cloned().collect();
    let mut non_unique = HashSet::new();
    let mut limitations = BTreeMap::new();
    let mut search = RecoverySearchState::initialize_search(&facts, &values);
    let mut evidence = RecoveryEvidence::default();
    let mut exact_search_facts = PrivateSearchExactFacts::default();
    let mut result = UcpResult {
        facts,
        value_facts: values,
        ..baseline.clone()
    };
    let mut propagation_needed = true;
    let (status, result) = loop {
        // Az új megvalósítható minták önmagukban nem érvénytelenítik a propagációs fixpontot.
        if propagation_needed {
            result = propagate_to_fixpoint(&problem, result.facts, result.value_facts, &mut search);
            // A puszta teljességi jelölés nem indít új kört; az új konkrét értékre kanonizált domain igen.
            while evidence.certify_complete_domains(&mut result, &problem.field_modulus)? {
                result =
                    propagate_to_fixpoint(&problem, result.facts, result.value_facts, &mut search);
            }
            search.observe_progress(&result, &problem.field_modulus);
            // E-t kizárólag az aktuális Delta igazolt pontos értékeiből állítja elő az SMT-kereséshez.
            exact_search_facts =
                established_exact_facts(original_context.as_ref(), &analyzer, &result.value_facts)?;
            propagation_needed = false;
        }
        let (actions, probe_plan) = shortlist_actions(
            &problem,
            &private_cells,
            &snapshot_cells,
            &private_set,
            &result,
            &search,
            &mut domain_search,
            &mut discovery,
            &evidence,
            &non_unique,
            original_context.is_some(),
            &options,
        )?;
        let Some(action) = choose_action(actions, &private_cells, &problem, &result, &evidence)
        else {
            let ProbePlan::Stop(status, reason, pending) = probe_plan else {
                anyhow::bail!("Selectable recovery probe was lost by the scheduler");
            };
            search.statistics.stop_reason = reason;
            if status == PrivacyAnalysisStatus::QueryLimitReached {
                for cell in pending {
                    limitations
                        .entry(cell)
                        .or_insert(RecoveryLimitation::QueryLimit);
                }
            }
            break (status, result);
        };
        let recovered = {
            let mut operations = RecoveryOperations {
                analyzer: &mut analyzer,
                analyzer_input,
                original: original_context.as_ref(),
                exact_facts: &exact_search_facts,
                modulus: &problem.field_modulus,
                knowledge: &result,
                baseline: &baseline,
                options: &options,
                search: &mut search,
                private_set: &private_set,
                query: &mut query,
            };
            match action {
                RecoveryAction::Refine(cell, strategy) => {
                    operations.refine_domain(&cell, strategy, &mut domain_search, &evidence)
                }
                RecoveryAction::Discover(cell, strategy) => {
                    operations.discover_domain(&cell, strategy, &mut discovery)
                }
            }
        }?;
        evidence.remember_feasible_samples(
            &recovered.cell,
            recovered.samples.iter().cloned(),
            &problem.field_modulus,
        )?;
        propagation_needed |= facts_changed(merge_established_results(
            &mut result,
            recovered,
            &mut search,
            &mut non_unique,
            &mut limitations,
        )?);
        propagation_needed |=
            evidence.certify_complete_domains(&mut result, &problem.field_modulus)?;
    };

    ensure!(
        non_unique
            .iter()
            .all(|cell| result.value_facts.known_value(cell).is_none()
                && !result.facts.is_unique(cell)),
        "Recovered facts contradict original non-uniqueness witnesses"
    );

    let cells = private_cells
        .into_iter()
        .map(|cell| {
            let domain = result.value_facts.domain(&cell).cloned();
            let baseline_domain = baseline.value_facts.domain(&cell).cloned();
            let uniqueness = if result.facts.is_unique(&cell) {
                PrivateCellUniqueness::Unique
            } else if non_unique.contains(&cell) || result.value_facts.domain_is_complete(&cell) {
                PrivateCellUniqueness::NonUnique
            } else {
                PrivateCellUniqueness::Unknown
            };
            let refined = domain_refined(
                baseline_domain.as_ref(),
                domain.as_ref(),
                &problem.field_modulus,
            );
            let recovery_limitation = if matches!(domain, Some(UcpValueDomain::Exact(_)))
                || uniqueness == PrivateCellUniqueness::NonUnique
            {
                None
            } else {
                limitations.remove(&cell)
            };
            PrivateCellReport {
                query_attempts: search.cells.get(&cell).map_or(0, |state| state.attempts),
                domain_refinement: domain_search.cells.remove(&cell),
                domain_discovery: discovery.cells.remove(&cell),
                domain_is_complete: result.value_facts.domain_is_complete(&cell),
                cell,
                uniqueness,
                domain,
                baseline_domain,
                domain_refined_from_baseline: refined,
                recovery_limitation,
            }
        })
        .collect();
    let mut report = recovery_report(
        status,
        cells,
        public_values,
        search.statistics,
        started.elapsed(),
        Some(result),
        options,
    );
    report.satisfiability_checks = satisfiability_checks;
    report.satisfiability_evidence = Some(if witness_verified {
        SatisfiabilityEvidence::VerifiedWitness
    } else {
        SatisfiabilityEvidence::Smt
    });
    report.domain_refinement_statistics = domain_search.statistics;
    report.domain_discovery_statistics = discovery.statistics;
    Ok(report)
}

#[derive(Debug)]
struct RecoveryStepResult {
    cell: CellId,
    samples: Vec<BigInt>,
    domain: Option<UcpValueDomain>,
    unique: bool,
    non_unique: bool,
    limitation: Option<RecoveryLimitation>,
    retryable: bool,
}

impl RecoveryStepResult {
    fn new(cell: &CellId) -> Self {
        Self {
            cell: cell.clone(),
            samples: Vec::new(),
            domain: None,
            unique: false,
            non_unique: false,
            limitation: None,
            retryable: false,
        }
    }
}

// A végrehajtási környezetből kölcsönzött állapoton műveletet futtat, és bizonyítékot ad vissza K/Delta módosítása nélkül.
// A kiválasztott műveletet kapcsolja az SMT-backendhez. Nem választ következő cellát.
// A domainalgoritmusok saját moduljaikban kezelik a jelölteket és a keresési kereteket.
struct RecoveryOperations<'a, F: AnalyzableField, Q> {
    analyzer: &'a mut Analyzer<F>,
    analyzer_input: &'a AnalyzerInput,
    original: Option<&'a OriginalPrivateQueryContext>,
    exact_facts: &'a PrivateSearchExactFacts,
    modulus: &'a BigInt,
    knowledge: &'a UcpResult,
    baseline: &'a UcpResult,
    options: &'a PrivacyAnalysisOptions,
    search: &'a mut RecoverySearchState,
    private_set: &'a HashSet<CellId>,
    query: &'a mut Q,
}

impl<F: AnalyzableField, Q> RecoveryOperations<'_, F, Q>
where
    Q: FnMut(&mut Analyzer<F>, &AnalyzerInput, &CellId) -> Result<SemanticQueryOutput>,
{
    fn refine_domain(
        &mut self,
        cell: &CellId,
        strategy: RecoveryStrategy,
        state: &mut DomainRefinementState,
        evidence: &RecoveryEvidence,
    ) -> Result<RecoveryStepResult> {
        ensure!(
            !self.knowledge.value_facts.domain_is_complete(cell),
            "Cannot refine a complete domain"
        );
        if strategy == RecoveryStrategy::FastProbe {
            return self.fast_probe(cell);
        }
        let before_checks = state.statistics.solver_checks;
        let original = self.original.context("Missing refinement snapshot")?;
        let samples = evidence.samples(cell);
        let mut learned = Vec::new();
        let (cell, domain, proven_non_unique) = state
            .refine_domain(
                cell,
                self.knowledge,
                self.modulus,
                &samples,
                |cell, domain, exclude| {
                    let answer = if exclude {
                        // A lefedést minden visszaállított állítástól függetlenül ellenőrzi.
                        original.check_membership::<F>(
                            cell,
                            domain,
                            true,
                            self.options.solver_timeout_ms,
                        )
                    } else {
                        original.check_candidate_with_exact_facts::<F>(
                            cell,
                            domain,
                            self.options.solver_timeout_ms,
                            self.exact_facts,
                        )
                    }?;
                    if !exclude && answer == Satisfiability::Satisfiable {
                        if let Some(value) = domain.exact_value() {
                            learned.push(value.clone());
                        }
                    }
                    Ok(answer)
                },
            )?
            .context("Scheduled refinement became ineligible")?;
        if !self.private_set.contains(&cell) {
            let checks = state.statistics.solver_checks - before_checks;
            self.search.statistics.bridge_domain_checks += checks;
            self.search.statistics.queries_without_progress += checks;
        }
        let mut recovered = RecoveryStepResult::new(&cell);
        recovered.samples = learned;
        recovered.domain = Some(domain);
        recovered.non_unique = proven_non_unique;
        Ok(recovered)
    }

    fn discover_domain(
        &mut self,
        cell: &CellId,
        strategy: RecoveryStrategy,
        state: &mut DomainDiscoveryState,
    ) -> Result<RecoveryStepResult> {
        ensure!(
            !self.knowledge.value_facts.domain_is_complete(cell),
            "Cannot discover a complete domain again"
        );
        if strategy == RecoveryStrategy::FastProbe {
            return self.fast_probe(cell);
        }
        let original = self.original.context("Missing discovery snapshot")?;
        let (cell, domain, proven_non_unique) = state
            .discover_domain(
                cell,
                self.modulus,
                self.options.solver_timeout_ms,
                |cell, blocked, timeout, probe| {
                    if probe == DiscoveryProbe::SubsetExclusion
                        && original.has_targeted_subset(cell)
                    {
                        match original.check_unseen_subset::<F>(cell, blocked, timeout) {
                            Ok(Satisfiability::Unsatisfiable) => Ok(DiscoveryResponse::SubsetUnsat),
                            Ok(Satisfiability::Satisfiable) => {
                                Ok(DiscoveryResponse::SubsetFallback { unknown: false })
                            }
                            Err(error) if error.downcast_ref::<UnknownSolverResult>().is_some() => {
                                Ok(DiscoveryResponse::SubsetFallback { unknown: true })
                            }
                            Err(error) => Err(error),
                        }
                    } else {
                        full_discovery_response(original.query_unseen_value_with_exact_facts::<F>(
                            cell,
                            blocked,
                            timeout,
                            self.exact_facts,
                        ))
                    }
                },
            )?
            .context("Scheduled discovery became ineligible")?;
        if !self.private_set.contains(&cell) {
            self.search.statistics.bridge_domain_checks += 1;
            self.search.statistics.queries_without_progress += 1;
        }
        let mut recovered = RecoveryStepResult::new(&cell);
        recovered.samples = state.cells[&cell].observed_values.iter().cloned().collect();
        recovered.domain = domain;
        recovered.non_unique = proven_non_unique;
        Ok(recovered)
    }

    fn fast_probe(&mut self, cell: &CellId) -> Result<RecoveryStepResult> {
        let timeout_ms = if self.search.cells.contains_key(cell) {
            self.options.retry_timeout_ms()
        } else {
            self.options.solver_timeout_ms
        };
        self.analyzer.set_smt_timeout_ms(timeout_ms)?;
        self.analyzer
            .set_ucp_unique_cells(self.knowledge.facts.unique_cells().iter().cloned());
        self.analyzer.set_ucp_value_facts(&smt_query_value_facts(
            &self.knowledge.value_facts,
            &self.baseline.value_facts,
        ));
        self.search
            .record_query(cell, self.private_set.contains(cell), timeout_ms);
        let mut recovered = RecoveryStepResult::new(cell);
        let answer = match (self.query)(self.analyzer, self.analyzer_input, cell) {
            Ok(answer) => answer,
            Err(error) => {
                recovered.limitation = Some(limitation_from_solver_error(error)?);
                recovered.retryable = true;
                return Ok(recovered);
            }
        };
        recovered.samples = answer.samples;
        match answer.result {
            SemanticQueryResult::ProvenUnique => {
                recovered.unique = true;
                recovered.domain = answer.value.map(UcpValueDomain::exact);
                if recovered.domain.is_none() {
                    recovered.limitation = Some(match answer.value_unavailable_reason {
                        Some(ValueRecoveryFailure::RepresentationLimit) => {
                            RecoveryLimitation::ValueRepresentationLimit
                        }
                        _ => RecoveryLimitation::NoConcreteValue,
                    });
                }
            }
            SemanticQueryResult::NotUnique => {
                recovered.non_unique = self.private_set.contains(cell);
            }
            SemanticQueryResult::Unknown => {
                recovered.retryable = true;
                recovered.limitation = Some(RecoveryLimitation::SolverUnknown { reason: None });
            }
            SemanticQueryResult::Overconstrained => {
                anyhow::bail!("Inferred facts conflict with the initially satisfiable circuit");
            }
        }
        Ok(recovered)
    }
}

// Csak igazolt következtetést olvaszt be. A megvalósítható mintákat külön W-ben őrzi meg;
// önmagában egy modellérték nem jogosít lefedő domain vagy egyértelműség bejegyzésére.
fn merge_established_results(
    result: &mut UcpResult,
    recovered: RecoveryStepResult,
    search: &mut RecoverySearchState,
    non_unique: &mut HashSet<CellId>,
    limitations: &mut BTreeMap<CellId, RecoveryLimitation>,
) -> Result<(bool, bool)> {
    let cell = recovered.cell;
    let uniqueness_added = recovered.unique && result.facts.mark_unique(cell.clone());
    let domain_changed = recovered
        .domain
        .is_some_and(|domain| result.value_facts.mark_domain(cell.clone(), domain));
    if recovered.non_unique {
        non_unique.insert(cell.clone());
    }
    if recovered.retryable {
        search
            .cells
            .get_mut(&cell)
            .context("Missing fast-probe attempt")?
            .retryable = true;
    }
    if let Some(limitation) = recovered.limitation {
        limitations.insert(cell, limitation);
    }
    Ok((uniqueness_added, domain_changed))
}

fn facts_changed((uniqueness_added, domain_changed): (bool, bool)) -> bool {
    uniqueness_added || domain_changed
}

fn smt_query_value_facts(current: &UcpValueFacts, baseline: &UcpValueFacts) -> UcpValueFacts {
    let mut exported = UcpValueFacts::new();
    for (cell, domain) in current.domains() {
        if domain.is_singleton() || baseline.domain(cell) != Some(domain) {
            exported.mark_domain(cell.clone(), domain.clone());
        }
    }
    exported
}

pub(crate) fn limitation_from_solver_error(error: anyhow::Error) -> Result<RecoveryLimitation> {
    if error.downcast_ref::<UnknownSolverResult>().is_none() {
        return Err(error);
    }
    let reason = error
        .downcast_ref::<SolverUnknownDetails>()
        .and_then(|detail| detail.reason.clone());
    Ok(
        if matches!(
            reason.as_deref(),
            Some("TIMEOUT" | crate::smt_solver::process::WALLCLOCK_TIMEOUT_REASON)
        ) {
            RecoveryLimitation::SolverTimeout
        } else {
            RecoveryLimitation::SolverUnknown { reason }
        },
    )
}

pub(crate) fn domain_refined(
    baseline: Option<&UcpValueDomain>,
    current: Option<&UcpValueDomain>,
    modulus: &BigInt,
) -> bool {
    fn field_values(domain: &UcpValueDomain, modulus: &BigInt) -> BTreeSet<BigInt> {
        let values = match domain {
            UcpValueDomain::Exact(value) => vec![value.clone()],
            UcpValueDomain::FiniteSet(values) => values.iter().cloned().collect(),
        };
        values
            .into_iter()
            .map(|value| ((value % modulus) + modulus) % modulus)
            .collect()
    }
    let Some(current) = current else {
        return false;
    };
    let current = field_values(current, modulus);
    match baseline {
        Some(baseline) => {
            let baseline = field_values(baseline, modulus);
            current.len() < baseline.len() && current.is_subset(&baseline)
        }
        None => BigInt::from(current.len()) < *modulus,
    }
}

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod tests {
    use super::super::privacy_validation::{
        validate_private_recovery_report, DomainValidationStatus, RecoveryValidationStatus,
    };
    use super::*;
    use crate::io::analyzer_io_type::VerificationInput;
    use std::collections::HashMap;

    const LINEAR: u8 = 0;
    const MASKED: u8 = 1;
    const CANDIDATES: u8 = 2;
    const BOOLEAN: u8 = 3;
    const EXPANDED: u8 = 4;
    const HUGE: u8 = 5;
    const INCONSISTENT: u8 = 6;
    const MIXED: u8 = 7;
    const PUBLISHED: u8 = 8;
    const COPIED_CONSTANT: u8 = 9;
    const NONLINEAR_WITH_AFFINE: u8 = 10;
    const NONLINEAR_INCONSISTENT: u8 = 11;
    const TWO_EXPANDED: u8 = 12;
    const SQUARED_DERIVED: u8 = 13;
    const MANY_EXPANDED: u8 = 14;
    const TWO_BOOLEANS: u8 = 15;

    // A teszt két advice cellával különíti el a visszaállítást, a nemegyértelműséget és a szerkezeti korlátot.
    #[derive(Clone, Default)]
    struct ExampleCircuit<const CASE: u8> {
        secret: u64,
        nonce: u64,
    }

    #[derive(Clone)]
    struct ExampleConfig {
        secret: Column<Advice>,
        nonce: Column<Advice>,
        selector: Selector,
        published: Option<Column<Instance>>,
    }

    impl<const CASE: u8> Circuit<Fr> for ExampleCircuit<CASE> {
        type Config = ExampleConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let secret = meta.advice_column();
            let nonce = meta.advice_column();
            let selector = meta.selector();
            let public = if matches!(CASE, LINEAR | MASKED | CANDIDATES | MIXED | PUBLISHED) {
                Some(meta.instance_column())
            } else {
                None
            };
            if CASE == PUBLISHED {
                meta.enable_equality(secret);
                meta.enable_equality(public.unwrap());
            }
            if CASE == COPIED_CONSTANT {
                let fixed = meta.fixed_column();
                meta.enable_constant(fixed);
                meta.enable_equality(secret);
            }
            meta.create_gate("private recovery example", |meta| {
                let s = meta.query_advice(secret, Rotation::cur());
                let n = meta.query_advice(nonce, Rotation::cur());
                let q = meta.query_selector(selector);
                let one = Expression::Constant(Fr::from(1));
                let boolean = |value: Expression<Fr>| value.clone() * (value - one.clone());
                let public = public.map(|column| meta.query_instance(column, Rotation::cur()));
                let equations = match CASE {
                    LINEAR => vec![s + Expression::Constant(Fr::from(5)) - public.unwrap()],
                    MASKED => vec![s + n - public.unwrap()],
                    CANDIDATES => vec![
                        // A teszt publikus érték rögzítése nélkül secret in {0,1,2} és nonce in {0,1} domaineket enged meg.
                        s.clone()
                            * (s.clone() - one.clone())
                            * (s.clone() - Expression::Constant(Fr::from(2))),
                        boolean(n.clone()),
                        s + n - public.unwrap(),
                    ],
                    BOOLEAN => vec![boolean(s)],
                    TWO_BOOLEANS => vec![boolean(s), boolean(n)],
                    EXPANDED | MANY_EXPANDED => {
                        vec![s.clone() * s.clone() - Expression::Constant(Fr::from(2)) * s + one]
                    }
                    NONLINEAR_WITH_AFFINE => vec![
                        s.clone() * s.clone() - Expression::Constant(Fr::from(2)) * s + one,
                        n - Expression::Constant(Fr::from(7)),
                    ],
                    NONLINEAR_INCONSISTENT => vec![s.clone() * s.clone(), s - one],
                    TWO_EXPANDED => vec![
                        s.clone() * s.clone() - Expression::Constant(Fr::from(2)) * s + one,
                        n.clone() * n.clone() - Expression::Constant(Fr::from(4)) * n
                            + Expression::Constant(Fr::from(4)),
                    ],
                    SQUARED_DERIVED => vec![
                        s.clone() * s.clone() - Expression::Constant(Fr::from(2)) * s.clone() + one,
                        n - s.clone() * s,
                    ],
                    HUGE => vec![s - Expression::Constant(Fr::from(1_u64 << 63))],
                    INCONSISTENT => vec![s.clone(), s - one],
                    MIXED => vec![
                        s + Expression::Constant(Fr::from(5)) - public.unwrap(),
                        boolean(n),
                    ],
                    PUBLISHED => vec![s - n - Expression::Constant(Fr::from(5))],
                    COPIED_CONSTANT => vec![s - n - Expression::Constant(Fr::from(5))],
                    _ => unreachable!(),
                };
                equations
                    .into_iter()
                    .map(|expr| q.clone() * expr)
                    .collect::<Vec<_>>()
            });
            ExampleConfig {
                secret,
                nonce,
                selector,
                published: if CASE == PUBLISHED { public } else { None },
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> std::result::Result<(), Error> {
            if CASE == MANY_EXPANDED {
                return layouter.assign_region(
                    || "forty independent recoverable private inputs",
                    |mut region| {
                        for row in 0..40 {
                            config.selector.enable(&mut region, row)?;
                            region.assign_advice(
                                || "private input",
                                config.secret,
                                row,
                                || Value::known(Fr::from(1)),
                            )?;
                            region.assign_advice(
                                || "unused queried nonce",
                                config.nonce,
                                row,
                                || Value::known(Fr::from(0)),
                            )?;
                        }
                        Ok(())
                    },
                );
            }
            let published = layouter.assign_region(
                || "private inputs",
                |mut region| {
                    config.selector.enable(&mut region, 0)?;
                    let secret = region.assign_advice(
                        || "secret",
                        config.secret,
                        0,
                        || Value::known(Fr::from(self.secret)),
                    )?;
                    if CASE == COPIED_CONSTANT {
                        region.constrain_constant(secret.cell(), Fr::from(7))?;
                    }
                    region.assign_advice(
                        || "nonce",
                        config.nonce,
                        0,
                        || Value::known(Fr::from(self.nonce)),
                    )?;
                    Ok(secret.cell())
                },
            )?;
            if let Some(column) = config.published {
                layouter.constrain_instance(published, column, 0)?;
            }
            Ok(())
        }
    }

    #[test]
    fn operation_fast_probes_return_evidence_until_the_common_merge() {
        fn check<const CASE: u8>(refine: bool, timeout: bool) {
            let cell = CellId::advice(0, 0);
            let mut context = prepare_privacy_analysis::<Fr, _, _>(
                &ExampleCircuit::<CASE>::default(),
                4,
                &input(None),
                [cell.clone()],
            )
            .unwrap();
            assert_eq!(
                check_sat(&mut context).0.unwrap(),
                Satisfiability::Satisfiable
            );
            let (baseline, facts, values) =
                initialize_knowledge(&context.problem, &context.public_values);
            let mut search = RecoverySearchState::initialize_search(&facts, &values);
            let mut knowledge = propagate_to_fixpoint(&context.problem, facts, values, &mut search);
            let before = knowledge.clone();
            let mut domains = DomainRefinementState::new(Default::default());
            let mut discovery = DomainDiscoveryState::new(Default::default());
            let mut evidence = RecoveryEvidence::default();
            let exact = PrivateSearchExactFacts::default();
            let targets = HashSet::from([cell.clone()]);
            let options = PrivacyAnalysisOptions::default();
            let mut calls = 0;
            let mut query = |analyzer: &mut Analyzer<Fr>, input: &AnalyzerInput, cell: &CellId| {
                calls += 1;
                if timeout {
                    Err(unknown_error(Some("TIMEOUT")))
                } else {
                    analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
                }
            };
            let recovered = {
                let mut operations = RecoveryOperations {
                    analyzer: &mut context.analyzer,
                    analyzer_input: &context.analyzer_input,
                    original: None,
                    exact_facts: &exact,
                    modulus: &context.problem.field_modulus,
                    knowledge: &knowledge,
                    baseline: &baseline,
                    options: &options,
                    search: &mut search,
                    private_set: &targets,
                    query: &mut query,
                };
                if refine {
                    operations.refine_domain(
                        &cell,
                        RecoveryStrategy::FastProbe,
                        &mut domains,
                        &evidence,
                    )
                } else {
                    operations.discover_domain(&cell, RecoveryStrategy::FastProbe, &mut discovery)
                }
            }
            .unwrap();
            assert_eq!(calls, 1);
            assert_eq!(search.total_queries(), 1);
            assert_eq!(domains.statistics.solver_checks, 0);
            assert_eq!(discovery.statistics.solver_checks, 0);
            assert_eq!(knowledge, before);
            assert!(!search.cells[&cell].retryable);
            assert!(evidence.samples(&cell).is_empty());
            evidence
                .remember_feasible_samples(
                    &cell,
                    recovered.samples.iter().cloned(),
                    &context.problem.field_modulus,
                )
                .unwrap();
            let mut non_unique = HashSet::new();
            let mut limitations = BTreeMap::new();
            let changed = facts_changed(
                merge_established_results(
                    &mut knowledge,
                    recovered,
                    &mut search,
                    &mut non_unique,
                    &mut limitations,
                )
                .unwrap(),
            );
            if timeout {
                assert!(!changed);
                assert_eq!(knowledge, before);
                assert!(search.cells[&cell].retryable);
                assert_eq!(
                    limitations.get(&cell),
                    Some(&RecoveryLimitation::SolverTimeout)
                );
            } else if refine {
                assert!(!changed);
                assert_eq!(knowledge, before);
                assert!(non_unique.contains(&cell));
                assert_eq!(evidence.samples(&cell).len(), 2);
            } else {
                assert!(changed);
                assert!(knowledge.facts.is_unique(&cell));
                assert_eq!(
                    knowledge.value_facts.known_value(&cell),
                    Some(&BigInt::from(1))
                );
            }
        }
        for timeout in [false, true] {
            check::<BOOLEAN>(true, timeout);
            check::<EXPANDED>(false, timeout);
        }
    }

    fn input(public: Option<i64>) -> AnalyzerInput {
        AnalyzerInput {
            verification_method: if public.is_some() {
                VerificationMethod::Specific
            } else {
                VerificationMethod::None
            },
            verification_input: VerificationInput {
                instance_cells: public
                    .map(|value| HashMap::from([("I-0-0".into(), value.into())]))
                    .unwrap_or_default(),
                iterations: 1,
            },
            lookup_method: LookupMethod::InlineConstraints,
        }
    }

    #[test]
    fn temporary_sat_candidate_never_becomes_a_uniqueness_premise() {
        let secret = CellId::advice(0, 0);
        let mut context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<BOOLEAN>::default(),
            4,
            &input(None),
            [secret.clone()],
        )
        .unwrap();
        for (value, expected) in [
            (2, Satisfiability::Unsatisfiable),
            (0, Satisfiability::Satisfiable),
        ] {
            let mut hints = UcpValueFacts::new();
            hints.mark_known(secret.clone(), BigInt::from(value));
            assert_eq!(
                context
                    .analyzer
                    .check_ucp_satisfiability_with_hints(&context.analyzer_input, &hints,)
                    .unwrap(),
                Some(expected)
            );
            assert!(context.analyzer.ucp_value_domains().is_empty());
            assert!(context.analyzer.ucp_unique_variables().is_empty());
            assert_eq!(
                context
                    .analyzer
                    .query_ucp_cell_uniqueness(&context.analyzer_input, &secret,)
                    .unwrap(),
                SemanticQueryResult::NotUnique
            );
        }
    }

    #[test]
    fn rejected_sat_hint_falls_back_to_original_context() {
        let secret = CellId::advice(0, 0);
        let mut context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<BOOLEAN>::default(),
            4,
            &input(None),
            [secret.clone()],
        )
        .unwrap();
        // A teszt hibás jelöltet ad át, és ellenőrzi, hogy ettől nem minősíti UNSAT-nak a kielégíthető kapcsolást.
        context
            .problem
            .initial_value_facts
            .mark_known(secret, BigInt::from(2));
        let (result, checks) = check_sat(&mut context);
        assert_eq!(result.unwrap(), Satisfiability::Satisfiable);
        assert_eq!(checks, 2);
        assert!(context.analyzer.ucp_value_domains().is_empty());
    }

    #[test]
    fn sat_hint_unknown_allows_fallback_but_execution_errors_remain_errors() {
        assert!(
            !accept_sat_hint(Err(anyhow::anyhow!(UnknownSolverResult).context(
                SolverUnknownDetails {
                    reason: Some("TIMEOUT".into())
                }
            )))
            .unwrap()
        );
        assert!(!accept_sat_hint(Ok(None)).unwrap());
        assert!(!accept_sat_hint(Ok(Some(Satisfiability::Unsatisfiable))).unwrap());
        assert!(accept_sat_hint(Ok(Some(Satisfiability::Satisfiable))).unwrap());
        assert!(accept_sat_hint(Err(anyhow::anyhow!("malformed solver output"))).is_err());
    }

    fn analyze<const CASE: u8>(
        public: Option<i64>,
        targets: Vec<CellId>,
        budget: usize,
    ) -> PrivacyAnalysisReport {
        analyze_private_recoverability::<Fr, _, _>(
            &ExampleCircuit::<CASE>::default(),
            4,
            &input(public),
            targets,
            PrivacyAnalysisOptions {
                max_semantic_queries: budget,
                ..PrivacyAnalysisOptions::default()
            },
        )
        .unwrap()
    }

    #[test]
    fn smt_export_keeps_exact_and_changed_domains_without_mutating_delta() {
        let cells: Vec<_> = (0..4).map(|column| CellId::advice(column, 0)).collect();
        let range = UcpValueDomain::finite_set((0..4).map(BigInt::from)).unwrap();
        let narrowed = UcpValueDomain::finite_set([1, 2].into_iter().map(BigInt::from)).unwrap();
        let new_domain = UcpValueDomain::finite_set([-1, 0].into_iter().map(BigInt::from)).unwrap();
        let mut baseline = UcpValueFacts::new();
        baseline.mark_domain(cells[0].clone(), range.clone());
        baseline.mark_domain(cells[1].clone(), range);
        baseline.mark_known(cells[2].clone(), BigInt::from(7));
        let mut current = baseline.clone();
        current.mark_domain(cells[1].clone(), narrowed.clone());
        current.mark_domain(cells[3].clone(), new_domain.clone());
        let original = current.clone();
        let exported = smt_query_value_facts(&current, &baseline);
        assert!(exported.domain(&cells[0]).is_none());
        assert_eq!(exported.domain(&cells[1]), Some(&narrowed));
        assert_eq!(exported.known_value(&cells[2]), Some(&BigInt::from(7)));
        assert_eq!(exported.domain(&cells[3]), Some(&new_domain));
        assert_eq!(current, original);
        assert_eq!(exported.domains().len(), 3);
    }

    #[test]
    fn skipped_structural_domain_remains_in_the_report_and_is_validated() {
        let secret = CellId::advice(0, 0);
        let circuit = ExampleCircuit::<BOOLEAN>::default();
        let input = input(None);
        let context =
            prepare_privacy_analysis::<Fr, _, _>(&circuit, 4, &input, [secret.clone()]).unwrap();
        let mut calls = 0;
        let report = recover_private_inputs(
            context,
            PrivacyAnalysisOptions::default(),
            Instant::now(),
            check_sat,
            |analyzer, input, cell| {
                calls += 1;
                assert!(analyzer
                    .ucp_value_domains()
                    .iter()
                    .all(|(_, domain)| domain.is_singleton()));
                analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
            },
        )
        .unwrap();
        assert_eq!(calls, 1);
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
        let boolean = UcpValueDomain::finite_set([0, 1].into_iter().map(BigInt::from));
        assert_eq!(report.cells[0].domain, boolean);
        assert_eq!(report.cells[0].baseline_domain, boolean);
        assert!(!report.cells[0].domain_refined_from_baseline);
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
    }

    // A teszt a valódi vezérlést és solvert használja; csak az exportálási szabályt írja felül.
    fn range_export_report<const LOOKUP: bool>(
        total: i64,
        full_export: bool,
    ) -> PrivacyAnalysisReport {
        use super::super::{
            external_circuit_tests::observations,
            external_range_tests::{range_private_inputs, RangeAggregateCircuit, RANGE_K},
        };
        let circuit = if total == 15 {
            RangeAggregateCircuit::<LOOKUP>::new(3, 12)
        } else {
            RangeAggregateCircuit::<LOOKUP>::new(7, 9)
        };
        let input = observations(&[total]);
        let mut context = prepare_privacy_analysis::<Fr, _, _>(
            &circuit,
            RANGE_K,
            &input,
            range_private_inputs(&circuit),
        )
        .unwrap();
        let options = PrivacyAnalysisOptions {
            solver_timeout_ms: Some(2_000),
            ..Default::default()
        };
        context
            .analyzer
            .set_smt_timeout_ms(options.solver_timeout_ms)
            .unwrap();
        let mut values = context.problem.initial_value_facts.clone();
        for (cell, value) in &context.public_values {
            values.mark_known(cell.clone(), value.clone());
        }
        let full_values = context
            .problem
            .analyze_with_values(context.problem.initial_facts.clone(), values)
            .value_facts;
        let mut calls = 0;
        let report = recover_private_inputs(
            context,
            options,
            Instant::now(),
            check_sat,
            |analyzer, input, cell| {
                calls += 1;
                if full_export {
                    analyzer.set_ucp_value_facts(&full_values);
                } else if total == 15 {
                    assert!(analyzer
                        .ucp_value_domains()
                        .iter()
                        .all(|(_, domain)| domain.is_singleton()));
                } else {
                    let narrowed = UcpValueDomain::finite_set((1..16).map(BigInt::from)).unwrap();
                    assert!(analyzer
                        .ucp_value_domains()
                        .iter()
                        .any(|(_, domain)| domain == &narrowed));
                }
                analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
            },
        )
        .unwrap();
        assert!(calls > 0);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.non_unique_cells, 2);
        assert_eq!(report.summary.finite_domains, 2);
        let expected =
            UcpValueDomain::finite_set((if total == 15 { 0 } else { 1 }..16).map(BigInt::from));
        for cell in &report.cells {
            assert_eq!(cell.domain, expected);
        }
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, RANGE_K, &input, &report)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        report
    }

    #[test]
    fn selective_domain_export_matches_full_export_on_imported_lookup() {
        // A teszt ellenőrzi, hogy a redundáns diszjunkciók elhagyása nem módosítja a domaineket és a minősítést.
        let selective = range_export_report::<true>(15, false);
        let full = range_export_report::<true>(15, true);
        assert_eq!(selective.cells, full.cells);
        assert_eq!(selective.summary, full.summary);
        assert_eq!(selective.ucp_result, full.ucp_result);
    }

    #[test]
    fn refined_finite_domains_are_still_exported_to_real_smt_queries() {
        let selective = range_export_report::<true>(16, false);
        let full = range_export_report::<true>(16, true);
        assert_eq!(selective.cells, full.cells);
        assert_eq!(selective.summary.refined_domains, 2);
    }

    #[test]
    fn recovers_selected_secret_and_deduplicates_targets() {
        let secret = CellId::advice(0, 0);
        let report = analyze::<LINEAR>(Some(100), vec![secret.clone(), secret], 32);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.private_cells, 1);
        assert_eq!(report.summary.exact_values, 1);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(95)))
        );
        assert!(report.cells[0].baseline_domain.is_none());
        assert!(report.cells[0].domain_refined_from_baseline);
        assert_eq!(report.semantic_queries, 0);
        assert_eq!(report.satisfiability_checks, 1);
        assert_eq!(report.search_statistics.propagation_runs, 1);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::Recovered
        );
    }

    #[test]
    fn never_copies_secret_assignments_from_the_witness() {
        let circuit = ExampleCircuit::<MASKED> {
            secret: 42,
            nonce: 58,
        };
        let targets = vec![CellId::advice(0, 0), CellId::advice(1, 0)];
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(100)),
            targets.clone(),
            PrivacyAnalysisOptions::default(),
        )
        .unwrap();
        assert_eq!(report.summary.non_unique_cells, 2);
        assert_eq!(report.summary.exact_values, 0);
        assert!(report.cells.iter().all(|cell| cell.domain.is_none()));
        // A teszt ellenőrzi, hogy a privát szintézisérték módosítása sem változtatja meg a kikövetkeztetett tényeket.
        let other = analyze_private_recoverability::<Fr, _, _>(
            &ExampleCircuit::<MASKED> {
                secret: 17,
                nonce: 83,
            },
            4,
            &input(Some(100)),
            targets,
            PrivacyAnalysisOptions::default(),
        )
        .unwrap();
        assert_eq!(report.cells, other.cells);
    }

    #[test]
    fn distinguishes_candidate_narrowing_from_exact_recovery() {
        let report = analyze::<CANDIDATES>(Some(2), vec![CellId::advice(0, 0)], 32);
        let cell = &report.cells[0];
        assert_eq!(cell.uniqueness, PrivateCellUniqueness::NonUnique);
        assert_eq!(
            cell.baseline_domain,
            UcpValueDomain::finite_set([0, 1, 2].map(BigInt::from))
        );
        assert_eq!(
            cell.domain,
            UcpValueDomain::finite_set([1, 2].map(BigInt::from))
        );
        assert!(cell.domain_refined_from_baseline);
        assert_eq!(report.summary.exact_values, 0);
        assert_eq!(report.summary.finite_domains, 1);
    }

    #[test]
    fn intrinsic_boolean_range_is_not_reported_as_new_refinement() {
        let report = analyze::<BOOLEAN>(None, vec![CellId::advice(0, 0)], 32);
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
        assert_eq!(report.cells[0].domain, report.cells[0].baseline_domain);
        assert!(!report.cells[0].domain_refined_from_baseline);
        assert!(report.cells[0].domain_is_complete);
        assert!(report
            .ucp_result
            .as_ref()
            .unwrap()
            .value_facts
            .domain_is_complete(&report.cells[0].cell));
        assert_eq!(report.search_statistics.propagation_runs, 1);
    }

    #[test]
    fn completeness_certificates_are_not_reused_for_different_public_observations() {
        let target = CellId::advice(0, 0);
        let first = analyze::<CANDIDATES>(Some(2), vec![target.clone()], 32);
        assert!(first.cells[0].domain_is_complete);
        let next = analyze::<CANDIDATES>(Some(1), vec![target.clone()], 0);
        assert_eq!(
            next.cells[0].domain,
            UcpValueDomain::finite_set([0.into(), 1.into()])
        );
        assert!(!next.cells[0].domain_is_complete);
        assert!(!next
            .ucp_result
            .unwrap()
            .value_facts
            .domain_is_complete(&target));
    }

    #[test]
    fn smt_proves_exact_value_instead_of_returning_an_arbitrary_model() {
        let report = analyze::<EXPANDED>(None, vec![CellId::advice(0, 0)], 32);
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(1)))
        );
        assert_eq!(report.semantic_queries, 1);
    }

    #[test]
    fn query_budget_exhaustion_is_unknown_not_evidence_of_secrecy() {
        let report = analyze::<EXPANDED>(None, vec![CellId::advice(0, 0)], 0);
        assert_eq!(report.status, PrivacyAnalysisStatus::QueryLimitReached);
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unknown);
        assert!(report.cells[0].domain.is_none());
        assert_eq!(report.semantic_queries, 0);
        assert_eq!(report.satisfiability_checks, 1);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::Unresolved
        );
        assert_eq!(
            report.cells[0].recovery_limitation,
            Some(RecoveryLimitation::QueryLimit)
        );
    }

    #[test]
    fn rejects_vacuous_recovery_from_inconsistent_constraints() {
        let report = analyze::<INCONSISTENT>(None, vec![CellId::advice(0, 0)], 32);
        assert_eq!(report.status, PrivacyAnalysisStatus::Inconsistent);
        assert!(report.ucp_result.is_none());
        assert!(report.cells[0].domain.is_none());
        assert_eq!(report.summary.unique_cells, 0);
        assert_eq!(report.summary.exact_values, 0);
        assert!(report.satisfiability_checks > 0);
        assert_eq!(report.semantic_queries, 0);
        assert_eq!(report.search_statistics.propagation_runs, 0);
    }

    #[test]
    fn values_beyond_i64_are_recovered_without_a_representation_failure() {
        let report = analyze::<HUGE>(None, vec![CellId::advice(0, 0)], 32);
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(1_u64 << 63)))
        );
        assert_eq!(report.summary.exact_values, 1);
        assert_eq!(report.summary.unique_cells, 1);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::Recovered
        );
        assert_eq!(report.cells[0].recovery_limitation, None);
    }

    #[test]
    fn reports_all_selected_secrets_even_when_some_are_non_unique() {
        let report = analyze::<MIXED>(
            Some(100),
            vec![CellId::advice(0, 0), CellId::advice(1, 0)],
            32,
        );
        assert_eq!(report.summary.exact_values, 1);
        assert_eq!(report.summary.non_unique_cells, 1);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    }

    #[test]
    fn supports_negative_public_field_representatives() {
        let report = analyze::<LINEAR>(Some(-1), vec![CellId::advice(0, 0)], 32);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(-6)))
        );
    }

    #[test]
    fn published_outputs_are_observations_through_instance_bindings() {
        // A teszt a publikus kimenetet ugyanúgy megfigyelésként kezeli, mint a publikus bemenetet.
        let report = analyze::<PUBLISHED>(Some(100), vec![CellId::advice(1, 0)], 32);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(95)))
        );
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
    }

    #[test]
    fn independent_validation_checks_ucp_and_smt_recovered_values() {
        let report = analyze::<LINEAR>(Some(100), vec![CellId::advice(0, 0)], 32);
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<LINEAR>::default(),
            4,
            &input(Some(100)),
            &report,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::VerifiedDomains);
        assert_eq!(checked.domain_queries, 1);
        assert_eq!(checked.cells[0].status, DomainValidationStatus::Entailed);
        let smt_report = analyze::<EXPANDED>(None, vec![CellId::advice(0, 0)], 32);
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            &smt_report,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::VerifiedDomains);
    }

    #[test]
    fn independent_validation_refutes_a_fabricated_exact_value() {
        let mut report = analyze::<LINEAR>(Some(100), vec![CellId::advice(0, 0)], 32);
        // A teszt ellenőrzi, hogy a validátor nem feltételezi a vizsgált Delta-állítást, mert az körkörös bizonyítás lenne.
        report.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(0)));
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<LINEAR>::default(),
            4,
            &input(Some(100)),
            &report,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::Refuted);
        assert_eq!(checked.cells[0].counterexample, Some(BigInt::from(95)));
    }

    #[test]
    fn finite_domain_validation_checks_coverage_not_candidate_feasibility() {
        let mut report = analyze::<CANDIDATES>(Some(2), vec![CellId::advice(0, 0)], 32);
        let circuit = ExampleCircuit::<CANDIDATES>::default();
        // A tesztben a 0 nem megvalósítható, de a {0,1,2} halmaz továbbra is lefed minden megoldást.
        report.cells[0].domain = UcpValueDomain::finite_set([0, 1, 2].map(BigInt::from));
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(2)), &report,)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        // A teszt ellenőrzi, hogy a megvalósítható 2 elhagyásakor konkrét ellenpéldát ad.
        report.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(1)));
        let checked =
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(2)), &report)
                .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::Refuted);
        assert_eq!(checked.cells[0].counterexample, Some(BigInt::from(2)));
        report.cells[0].domain = Some(UcpValueDomain::FiniteSet(BTreeSet::new()));
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(2)), &report,)
                .unwrap()
                .status,
            RecoveryValidationStatus::Refuted
        );
    }

    #[test]
    fn validation_does_not_assume_other_claims_or_leak_query_scopes() {
        let mut report = analyze::<MIXED>(
            Some(100),
            vec![CellId::advice(0, 0), CellId::advice(1, 0)],
            32,
        );
        report.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(0)));
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<MIXED>::default(),
            4,
            &input(Some(100)),
            &report,
        )
        .unwrap();
        assert_eq!(checked.cells[0].status, DomainValidationStatus::Refuted);
        assert_eq!(checked.cells[1].status, DomainValidationStatus::Entailed);
        assert_eq!(checked.domain_queries, 2);
    }

    #[test]
    fn validation_never_certifies_absent_claims_or_unsatisfiable_contexts() {
        let unknown = analyze::<EXPANDED>(None, vec![CellId::advice(0, 0)], 0);
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            &unknown,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::NoDomainClaims);
        assert_eq!(
            checked.cells[0].status,
            DomainValidationStatus::NoDomainClaim
        );
        let mut impossible = analyze::<INCONSISTENT>(None, vec![CellId::advice(0, 0)], 32);
        impossible.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(5)));
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<INCONSISTENT>::default(),
            4,
            &input(None),
            &impossible,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::Inconsistent);
        assert_eq!(checked.domain_queries, 0);
    }

    #[test]
    fn validation_respects_field_equivalence_and_copy_constants() {
        let mut signed = analyze::<LINEAR>(Some(-1), vec![CellId::advice(0, 0)], 32);
        let field_modulus = super::super::extractor::field_modulus::<Fr>();
        signed.cells[0].domain = Some(UcpValueDomain::exact(field_modulus - BigInt::from(6)));
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(
                &ExampleCircuit::<LINEAR>::default(),
                4,
                &input(Some(-1)),
                &signed,
            )
            .unwrap()
            .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        let mut copied = analyze::<COPIED_CONSTANT>(None, vec![CellId::advice(0, 0)], 32);
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(
                &ExampleCircuit::<COPIED_CONSTANT>::default(),
                4,
                &input(None),
                &copied,
            )
            .unwrap()
            .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        copied.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(8)));
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<COPIED_CONSTANT>::default(),
            4,
            &input(None),
            &copied,
        )
        .unwrap();
        assert_eq!(checked.cells[0].counterexample, Some(BigInt::from(7)));
    }

    #[test]
    fn validation_rejects_changed_public_observations_and_invalid_cells() {
        let mut report = analyze::<LINEAR>(Some(100), vec![CellId::advice(0, 0)], 32);
        let circuit = ExampleCircuit::<LINEAR>::default();
        assert!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(101)), &report)
                .is_err()
        );
        report.cells.push(report.cells[0].clone());
        assert!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(100)), &report)
                .is_err()
        );
        report.cells.pop();
        report.cells[0].cell = CellId::advice(99, 0);
        assert!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(100)), &report)
                .is_err()
        );
    }

    #[test]
    fn validation_keeps_large_counterexamples_without_i64_truncation() {
        let mut report = analyze::<HUGE>(None, vec![CellId::advice(0, 0)], 32);
        report.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(0)));
        let checked = validate_private_recovery_report::<Fr, _>(
            &ExampleCircuit::<HUGE>::default(),
            4,
            &input(None),
            &report,
        )
        .unwrap();
        assert_eq!(checked.status, RecoveryValidationStatus::Refuted);
        assert_eq!(
            checked.cells[0].counterexample,
            Some(BigInt::from(1_u64 << 63))
        );
        assert_eq!(checked.solver_checks, 3);
    }

    #[test]
    fn validation_subset_sat_is_not_a_counterexample_to_a_nonlinear_claim() {
        let circuit = ExampleCircuit::<NONLINEAR_WITH_AFFINE>::default();
        let report = analyze::<NONLINEAR_WITH_AFFINE>(None, vec![CellId::advice(0, 0)], 32);
        let validation =
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(None), &report).unwrap();
        // A teszt affin részhalmaza csak nonce=7-et rögzít, és a teljes másodfokú kényszerrel szemben secret!=1-et is megenged.
        assert_eq!(validation.status, RecoveryValidationStatus::VerifiedDomains);
        assert_eq!(validation.subset_checks, 1);
        assert_eq!(validation.solver_checks, 3);
        assert_eq!(validation.cells[0].status, DomainValidationStatus::Entailed);
    }

    #[test]
    fn validation_subset_rejection_uses_an_actual_full_circuit_counterexample() {
        let circuit = ExampleCircuit::<NONLINEAR_WITH_AFFINE>::default();
        let mut report = analyze::<NONLINEAR_WITH_AFFINE>(None, vec![CellId::advice(0, 0)], 32);
        report.cells[0].domain = Some(UcpValueDomain::exact(BigInt::from(0)));
        let validation =
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(None), &report).unwrap();
        assert_eq!(validation.status, RecoveryValidationStatus::Refuted);
        assert_eq!(validation.subset_checks, 1);
        assert_eq!(validation.solver_checks, 3);
        assert_eq!(validation.cells[0].counterexample, Some(BigInt::from(1)));
    }

    #[test]
    fn validation_never_accepts_a_subset_proof_without_original_satisfiability() {
        let circuit = ExampleCircuit::<NONLINEAR_INCONSISTENT>::default();
        let report = analyze::<NONLINEAR_WITH_AFFINE>(None, vec![CellId::advice(0, 0)], 32);
        // A teszt affin részhalmaza secret=1-et követel, de a kihagyott secret^2=0 a teljes rendszert következetlenné teszi.
        let validation =
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(None), &report).unwrap();
        assert_eq!(validation.status, RecoveryValidationStatus::Inconsistent);
        assert_eq!(validation.domain_queries, 0);
        assert_eq!(validation.subset_checks, 0);
        assert_eq!(
            validation.cells[0].status,
            DomainValidationStatus::Inconsistent
        );
    }

    #[test]
    fn low_level_validation_rejects_inferred_premises() {
        let public = input(Some(100));
        let circuit = ExampleCircuit::<LINEAR>::default();
        let secret = CellId::advice(0, 0);
        let domain = UcpValueDomain::exact(BigInt::from(0));
        let mut analyzer = Analyzer::<Fr>::new(
            &circuit,
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&public),
        )
        .unwrap();
        let mut inferred = super::super::value::UcpValueFacts::new();
        inferred.mark_known(secret.clone(), BigInt::from(0));
        analyzer.set_ucp_value_facts(&inferred);
        assert!(analyzer
            .query_private_domain_entailment_after_sat(&public, &secret, &domain)
            .is_err());
        assert!(analyzer
            .query_private_domain_entailment(&public, &secret, &domain)
            .is_err());
        analyzer.set_ucp_value_facts(&super::super::value::UcpValueFacts::new());
        analyzer.set_ucp_unique_cells([secret.clone()]);
        assert!(analyzer
            .query_private_domain_entailment_after_sat(&public, &secret, &domain)
            .is_err());
        assert!(analyzer
            .query_private_domain_entailment(&public, &secret, &domain)
            .is_err());
    }

    #[test]
    fn inline_lookup_ranges_support_recovery_on_existing_sample_circuit() {
        use crate::sample_circuits::zcash::bit_decomposition::two_bit_decomp_lookup::TwoBitDecompCircuit;
        let circuit = TwoBitDecompCircuit::<Fr>::default();
        let targets = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(3)),
            targets.clone(),
            PrivacyAnalysisOptions::default(),
        )
        .unwrap();
        assert_eq!(report.summary.exact_values, 2);
        assert_eq!(report.semantic_queries, 0);
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(3)), &report,)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        for cell in &report.cells {
            assert_eq!(
                cell.baseline_domain,
                UcpValueDomain::finite_set([0, 1].map(BigInt::from))
            );
            assert_eq!(cell.domain, Some(UcpValueDomain::exact(BigInt::from(1))));
        }
        // A teszt ellenőrzi, hogy a pontatlan lookup-modellezést nem használja nemegyértelműség igazolására.
        for method in [
            LookupMethod::Uninterpreted,
            LookupMethod::Interpreted,
            LookupMethod::None,
        ] {
            let mut unsupported = input(Some(3));
            unsupported.lookup_method = method;
            let error = analyze_private_recoverability::<Fr, _, _>(
                &circuit,
                4,
                &unsupported,
                targets.clone(),
                PrivacyAnalysisOptions::default(),
            )
            .unwrap_err();
            assert_eq!(
                error.downcast_ref::<UnsupportedPrivacyFeature>(),
                Some(&UnsupportedPrivacyFeature::InlineLookupsRequired)
            );
        }
    }

    fn unknown_error(reason: Option<&str>) -> anyhow::Error {
        anyhow::Error::new(UnknownSolverResult).context(SolverUnknownDetails {
            reason: reason.map(str::to_owned),
        })
    }

    fn search_report<const CASE: u8>(
        targets: Vec<CellId>,
        options: PrivacyAnalysisOptions,
        query: impl FnMut(&mut Analyzer<Fr>, &AnalyzerInput, &CellId) -> Result<SemanticQueryOutput>,
    ) -> PrivacyAnalysisReport {
        let context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<CASE>::default(),
            4,
            &input(None),
            targets,
        )
        .unwrap();
        recover_private_inputs(context, options, Instant::now(), check_sat, query).unwrap()
    }

    #[test]
    fn search_reserves_target_attempt_after_an_unknown_bridge() {
        // A teszt először az s=1 köztes cellát próbálja SMT-vel megoldani, mert abból az n=s*s továbbkövetkezik.
        let target = CellId::advice(1, 0);
        let mut visited = Vec::new();
        let report = search_report::<SQUARED_DERIVED>(
            vec![target.clone()],
            PrivacyAnalysisOptions {
                max_semantic_queries: 2,
                search: PrivacySearchOptions {
                    max_queries_without_progress: 1,
                    ..Default::default()
                },
                ..Default::default()
            },
            |analyzer, input, cell| {
                visited.push(cell.clone());
                if cell != &target {
                    Err(unknown_error(Some("TIMEOUT")))
                } else {
                    analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
                }
            },
        );
        assert_eq!(visited, [CellId::advice(0, 0), target]);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.semantic_queries, 2);
        assert_eq!(report.search_statistics.bridge_queries, 1);
        assert_eq!(report.search_statistics.target_queries, 1);
        assert_eq!(report.search_statistics.unqueried_targets, 0);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(1.into()))
        );
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(
                &ExampleCircuit::<SQUARED_DERIVED>::default(),
                4,
                &input(None),
                &report,
            )
            .unwrap()
            .status,
            RecoveryValidationStatus::VerifiedDomains
        );
    }

    #[test]
    fn search_excludes_bridges_when_only_reserved_target_budget_remains() {
        let target = CellId::advice(1, 0);
        let report = search_report::<SQUARED_DERIVED>(
            vec![target.clone()],
            PrivacyAnalysisOptions {
                max_semantic_queries: 1,
                ..Default::default()
            },
            |analyzer, input, cell| {
                assert_eq!(cell, &target);
                analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
            },
        );
        assert_eq!(report.summary.exact_values, 1);
        assert_eq!(report.search_statistics.bridge_queries, 0);
        assert_eq!(report.semantic_queries, 1);
    }

    #[test]
    fn uniqueness_without_a_value_restarts_propagation_only_when_new() {
        let secret = CellId::advice(0, 0);
        let target = CellId::advice(1, 0);
        let mut visited = Vec::new();
        let report = search_report::<SQUARED_DERIVED>(
            vec![target.clone()],
            PrivacyAnalysisOptions {
                max_semantic_queries: 2,
                ..Default::default()
            },
            |_, _, cell| {
                visited.push(cell.clone());
                Ok(SemanticQueryResult::ProvenUnique.into())
            },
        );
        assert_eq!(visited, [secret.clone(), target.clone()]);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.search_statistics.propagation_runs, 2);
        assert_eq!(report.search_statistics.progress_rounds, 1);
        assert_eq!(report.semantic_queries, 2);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::UniqueWithoutValue
        );
        let result = report.ucp_result.unwrap();
        assert!(result.facts.is_unique(&secret));
        assert!(result.facts.is_unique(&target));
        assert!(result.all_expressions_unique());
        assert!(result.value_facts.known_value(&target).is_none());
    }

    #[test]
    fn refinement_reuses_exact_ucp_values_of_non_target_cells() {
        let circuit = ExampleCircuit::<MIXED>::default();
        let input = input(Some(100));
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input,
            [CellId::advice(1, 0)],
            PrivacyAnalysisOptions {
                max_semantic_queries: 0,
                solver_timeout_ms: Some(2_000),
                domain_refinement: PrivacyDomainRefinementOptions {
                    max_solver_checks: 3,
                    max_candidates_per_cell: 2,
                },
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.domain_refinement_statistics.solver_checks, 3);
        assert_eq!(report.summary.non_unique_cells, 1);
        assert_eq!(report.search_statistics.propagation_runs, 1);
        let query = std::fs::read_to_string("src/output/private_domain_refinement.smt2").unwrap();
        assert!(query.contains("( = A-0-0 (as ff95 F))"));
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input, &report)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
    }

    #[test]
    fn inconclusive_internal_refinement_probe_falls_back_without_repeating_it() {
        let mut attempts = 0;
        let report = search_report::<BOOLEAN>(
            vec![CellId::advice(0, 0)],
            PrivacyAnalysisOptions {
                max_semantic_queries: 100,
                solver_timeout_ms: Some(1_000),
                search: PrivacySearchOptions {
                    max_retries_per_target: 100,
                    retry_solver_timeout_ms: None,
                    ..Default::default()
                },
                domain_refinement: PrivacyDomainRefinementOptions {
                    max_solver_checks: 3,
                    max_candidates_per_cell: 2,
                },
                ..Default::default()
            },
            |_, _, _| {
                attempts += 1;
                assert_eq!(attempts, 1);
                Err(unknown_error(Some("TIMEOUT")))
            },
        );
        assert_eq!(attempts, 1);
        assert_eq!(report.semantic_queries, 1);
        assert_eq!(report.domain_refinement_statistics.solver_checks, 3);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.non_unique_cells, 1);
        assert_eq!(report.search_statistics.propagation_runs, 1);
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(
                &ExampleCircuit::<BOOLEAN>::default(),
                4,
                &input(None),
                &report,
            )
            .unwrap()
            .status,
            RecoveryValidationStatus::VerifiedDomains
        );
    }

    #[test]
    fn unchanged_refinements_advance_to_other_cells_without_repeating_propagation() {
        for checks in [4, 6] {
            let report = search_report::<TWO_BOOLEANS>(
                vec![CellId::advice(0, 0), CellId::advice(1, 0)],
                PrivacyAnalysisOptions {
                    max_semantic_queries: 0,
                    solver_timeout_ms: Some(2_000),
                    domain_refinement: PrivacyDomainRefinementOptions {
                        max_solver_checks: checks,
                        max_candidates_per_cell: 2,
                    },
                    ..Default::default()
                },
                |_, _, _| panic!("Refinement must not consume semantic queries"),
            );
            assert_eq!(report.search_statistics.propagation_runs, 1);
            assert_eq!(report.search_statistics.progress_rounds, 0);
            assert_eq!(report.domain_refinement_statistics.attempted_cells, 2);
            assert_eq!(report.domain_refinement_statistics.solver_checks, checks);
            assert_eq!(report.semantic_queries, 0);
            assert_eq!(
                report.summary.non_unique_cells,
                if checks == 6 { 2 } else { 1 }
            );
            assert_eq!(
                report.status,
                if checks == 6 {
                    PrivacyAnalysisStatus::Analyzed
                } else {
                    PrivacyAnalysisStatus::QueryLimitReached
                }
            );
            for cell in &report.cells {
                assert_eq!(
                    cell.domain,
                    UcpValueDomain::finite_set([0.into(), 1.into()])
                );
                assert!(cell.domain_refinement.is_some());
            }
        }
    }

    #[test]
    fn search_progress_renews_optional_budget_but_never_total_count() {
        let targets = vec![CellId::advice(0, 0), CellId::advice(1, 0)];
        for (hard_limit, expected, queries) in [
            (1, PrivacyAnalysisStatus::QueryLimitReached, 1),
            (2, PrivacyAnalysisStatus::Analyzed, 2),
        ] {
            let report = search_report::<TWO_EXPANDED>(
                targets.clone(),
                PrivacyAnalysisOptions {
                    max_semantic_queries: hard_limit,
                    search: PrivacySearchOptions {
                        max_queries_without_progress: 1,
                        ..Default::default()
                    },
                    ..Default::default()
                },
                |analyzer, input, cell| analyzer.query_ucp_cell_uniqueness_with_value(input, cell),
            );
            assert_eq!(report.status, expected);
            assert_eq!(report.semantic_queries, queries);
            assert_eq!(report.search_statistics.target_queries, queries);
            assert_eq!(report.search_statistics.progress_rounds, queries);
            assert_eq!(report.search_statistics.propagation_runs, queries + 1);
            assert_eq!(report.search_statistics.queries_without_progress, 0);
            assert_eq!(report.summary.exact_values, queries);
            assert_eq!(report.search_statistics.unqueried_targets, 2 - queries);
            if hard_limit == 1 {
                assert_eq!(
                    report.search_statistics.stop_reason,
                    Some(PrivacySearchStopReason::TotalQueryLimit)
                );
            }
        }
    }

    #[test]
    fn search_retries_unknown_target_after_other_target_progress() {
        // A teszt egy bizonytalan próbát szimulál két olyan cél között, amelyet az SMT megold, de az UCP nem faktorizál.
        let secret = CellId::advice(0, 0);
        let nonce = CellId::advice(1, 0);
        let mut visited = Vec::new();
        let report = search_report::<TWO_EXPANDED>(
            vec![secret.clone(), nonce.clone()],
            PrivacyAnalysisOptions::default(),
            |analyzer, input, cell| {
                visited.push(cell.clone());
                if visited.len() == 1 {
                    Err(unknown_error(Some("TIMEOUT")))
                } else {
                    analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
                }
            },
        );
        assert_eq!(visited, [secret, nonce, CellId::advice(0, 0)]);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.exact_values, 2);
        assert_eq!(report.semantic_queries, 3);
        assert_eq!(report.search_statistics.retry_queries, 1);
        assert_eq!(report.search_statistics.propagation_runs, 3);
        assert_eq!(report.cells[0].query_attempts, 2);
        assert!(report
            .cells
            .iter()
            .all(|cell| cell.recovery_limitation.is_none()));
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(
                &ExampleCircuit::<TWO_EXPANDED>::default(),
                4,
                &input(None),
                &report,
            )
            .unwrap()
            .status,
            RecoveryValidationStatus::VerifiedDomains
        );
    }

    #[test]
    fn search_retries_with_larger_timeout_without_assuming_the_candidate() {
        let mut timeouts = Vec::new();
        let report = search_report::<EXPANDED>(
            vec![CellId::advice(0, 0)],
            PrivacyAnalysisOptions {
                solver_timeout_ms: Some(1_000),
                search: PrivacySearchOptions {
                    retry_solver_timeout_ms: Some(2_000),
                    ..Default::default()
                },
                ..Default::default()
            },
            |analyzer, input, cell| {
                timeouts.push(analyzer.smt_timeout_ms());
                assert!(analyzer.ucp_value_domains().is_empty());
                if timeouts.len() == 1 {
                    Err(unknown_error(Some("TIMEOUT")))
                } else {
                    analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
                }
            },
        );
        assert_eq!(timeouts, [Some(1_000), Some(2_000)]);
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.exact_values, 1);
        assert_eq!(report.search_statistics.retry_queries, 1);
        assert_eq!(report.cells[0].query_attempts, 2);
    }

    #[test]
    fn search_no_progress_does_not_loop_or_repeat_a_decisive_result() {
        for result in [SemanticQueryResult::Unknown, SemanticQueryResult::NotUnique] {
            let report = search_report::<BOOLEAN>(
                vec![CellId::advice(0, 0)],
                PrivacyAnalysisOptions {
                    solver_timeout_ms: Some(1_000),
                    search: PrivacySearchOptions {
                        max_retries_per_target: 100,
                        retry_solver_timeout_ms: Some(2_000),
                        ..Default::default()
                    },
                    ..Default::default()
                },
                |_, _, _| Ok(result.into()),
            );
            // A teszt nagyobb kerete egyetlen újrapróbálkozást enged; új tudás nélkül nem indít harmadik próbát.
            let queries = if result == SemanticQueryResult::Unknown {
                2
            } else {
                1
            };
            assert_eq!(report.semantic_queries, queries);
            assert_eq!(report.cells[0].query_attempts, queries);
            assert_eq!(report.search_statistics.propagation_runs, 1);
            assert_eq!(
                report.status,
                if result == SemanticQueryResult::Unknown {
                    PrivacyAnalysisStatus::SolverUnknown
                } else {
                    PrivacyAnalysisStatus::Analyzed
                }
            );
        }
    }

    #[test]
    fn search_stagnation_limit_preserves_unknown_without_skipping_first_targets() {
        let report = search_report::<TWO_EXPANDED>(
            vec![CellId::advice(0, 0), CellId::advice(1, 0)],
            PrivacyAnalysisOptions {
                solver_timeout_ms: Some(1_000),
                search: PrivacySearchOptions {
                    max_queries_without_progress: 0,
                    ..Default::default()
                },
                ..Default::default()
            },
            |_, _, _| Err(unknown_error(Some("TIMEOUT"))),
        );
        assert_eq!(report.semantic_queries, 2);
        assert_eq!(report.search_statistics.propagation_runs, 1);
        assert_eq!(report.search_statistics.unqueried_targets, 0);
        assert_eq!(
            report.search_statistics.stop_reason,
            Some(PrivacySearchStopReason::NoProgressLimit)
        );
        assert_eq!(report.status, PrivacyAnalysisStatus::QueryLimitReached);
        assert!(report.cells.iter().all(|cell| cell.query_attempts == 1
            && cell.domain.is_none()
            && cell.uniqueness == PrivateCellUniqueness::Unknown));
    }

    #[test]
    fn refinement_shortlist_reopens_partial_work_only_after_global_progress() {
        let target = CellId::advice(0, 0);
        let helper = CellId::advice(1, 0);
        let targets = [target.clone()];
        let context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<TWO_EXPANDED>::default(),
            4,
            &input(None),
            targets.clone(),
        )
        .unwrap();
        let (_, facts, mut values) = initialize_knowledge(&context.problem, &context.public_values);
        values.mark_domain(
            target.clone(),
            UcpValueDomain::finite_set([0.into(), 1.into()]).unwrap(),
        );
        let mut search = RecoverySearchState::initialize_search(&facts, &values);
        let mut result = propagate_to_fixpoint(&context.problem, facts, values, &mut search);
        search.observe_progress(&result, &context.problem.field_modulus);
        let options = PrivacyAnalysisOptions {
            max_semantic_queries: 0,
            search: PrivacySearchOptions {
                max_bridge_queries: 0,
                ..Default::default()
            },
            domain_refinement: PrivacyDomainRefinementOptions {
                max_solver_checks: 10,
                max_candidates_per_cell: 2,
            },
            ..Default::default()
        };
        let private_set = HashSet::from([target.clone()]);
        let mut domains = DomainRefinementState::new(options.domain_refinement);
        let mut discovery = DomainDiscoveryState::new(options.domain_discovery);
        let evidence = RecoveryEvidence::default();
        let non_unique = HashSet::new();
        let mut actions = |result: &UcpResult,
                           search: &RecoverySearchState,
                           domains: &mut DomainRefinementState| {
            shortlist_actions(
                &context.problem,
                &targets,
                &context.problem.witness_cells,
                &private_set,
                result,
                search,
                domains,
                &mut discovery,
                &evidence,
                &non_unique,
                true,
                &options,
            )
            .unwrap()
            .0
        };
        assert_eq!(
            actions(&result, &search, &mut domains),
            [RecoveryAction::Refine(
                target.clone(),
                RecoveryStrategy::DomainSearch
            )]
        );
        domains
            .refine_domain(
                &target,
                &result,
                &context.problem.field_modulus,
                &BTreeSet::new(),
                |_, _, exclude| {
                    if exclude {
                        Ok(Satisfiability::Unsatisfiable)
                    } else {
                        Err(unknown_error(Some("TIMEOUT")))
                    }
                },
            )
            .unwrap()
            .unwrap();
        let generation = search.generation;
        search.statistics.queries_without_progress += 1;
        search.observe_progress(&result, &context.problem.field_modulus);
        assert_eq!(search.generation, generation);
        assert!(actions(&result, &search, &mut domains).is_empty());

        // A teszt a másik kifejtett egyenlet újonnan igazolt egyértelműségét szimulálja.
        assert!(result.facts.mark_unique(helper));
        search.observe_progress(&result, &context.problem.field_modulus);
        assert_eq!(search.generation, generation + 1);
        assert_eq!(
            actions(&result, &search, &mut domains),
            [RecoveryAction::Refine(
                target.clone(),
                RecoveryStrategy::DomainSearch
            )]
        );
        domains
            .refine_domain(
                &target,
                &result,
                &context.problem.field_modulus,
                &BTreeSet::new(),
                |_, _, exclude| {
                    assert!(!exclude);
                    Err(unknown_error(Some("TIMEOUT")))
                },
            )
            .unwrap()
            .unwrap();
        assert!(actions(&result, &search, &mut domains).is_empty());
        assert_eq!(domains.statistics.solver_checks, 5);
        assert_eq!(domains.statistics.attempted_cells, 1);
    }

    #[test]
    fn search_detects_actual_domain_progress_not_repeated_or_equivalent_facts() {
        let context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<MASKED>::default(),
            4,
            &input(Some(10)),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        let facts = context.problem.initial_facts.clone();
        let mut values = UcpValueFacts::new();
        let cell = CellId::advice(0, 0);
        let mut state = RecoverySearchState::initialize_search(&facts, &values);
        state.statistics.queries_without_progress = 3;
        values.mark_domain(
            cell.clone(),
            UcpValueDomain::finite_set([0.into(), 1.into()]).unwrap(),
        );
        let first = context
            .problem
            .analyze_with_values(facts.clone(), values.clone());
        state.observe_progress(&first, &context.problem.field_modulus);
        assert_eq!(state.statistics.queries_without_progress, 0);
        state.statistics.queries_without_progress = 2;
        state.observe_progress(&first, &context.problem.field_modulus);
        assert_eq!(state.statistics.queries_without_progress, 2);
        values.mark_known(cell.clone(), 1.into());
        let mut exact = context.problem.analyze_with_values(facts, values);
        state.observe_progress(&exact, &context.problem.field_modulus);
        assert_eq!(state.statistics.progress_rounds, 2);
        state.statistics.queries_without_progress = 1;
        exact.value_facts = UcpValueFacts::new();
        exact
            .value_facts
            .mark_known(cell, &context.problem.field_modulus + 1);
        state.observe_progress(&exact, &context.problem.field_modulus);
        assert_eq!(state.statistics.progress_rounds, 2);
        assert_eq!(state.statistics.queries_without_progress, 1);
    }

    #[test]
    fn search_zero_retry_budget_is_rejected_before_synthesis() {
        let error = analyze_private_recoverability::<Fr, _, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            [CellId::advice(0, 0)],
            PrivacyAnalysisOptions {
                search: PrivacySearchOptions {
                    retry_solver_timeout_ms: Some(0),
                    ..Default::default()
                },
                ..Default::default()
            },
        )
        .unwrap_err();
        assert!(error.to_string().contains("Retry solver timeout"));
        assert_eq!(PrivacyAnalysisOptions::default().max_semantic_queries, 256);
        assert_eq!(PrivacyAnalysisOptions::default().retry_timeout_ms(), None);
    }

    #[test]
    fn search_default_budget_recovers_more_than_thirty_two_private_inputs() {
        let circuit = ExampleCircuit::<MANY_EXPANDED>::default();
        MockProver::run(6, &circuit, vec![])
            .unwrap()
            .assert_satisfied();
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            6,
            &input(None),
            (0..40).map(|row| CellId::advice(0, row)),
            PrivacyAnalysisOptions::default(),
        )
        .unwrap();
        assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
        assert_eq!(report.summary.exact_values, 40);
        assert_eq!(report.semantic_queries, 40);
        assert_eq!(report.search_statistics.target_queries, 40);
        assert_eq!(report.search_statistics.unqueried_targets, 0);
        assert!(report
            .cells
            .iter()
            .all(|cell| cell.query_attempts == 1
                && cell.domain == Some(UcpValueDomain::exact(1.into()))));
    }

    #[test]
    fn explicit_solver_budget_is_instance_local_and_recorded() {
        let circuit = ExampleCircuit::<LINEAR>::default();
        let options = PrivacyAnalysisOptions {
            solver_timeout_ms: Some(10_000),
            ..Default::default()
        };
        let report = analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(100)),
            [CellId::advice(0, 0)],
            options,
        )
        .unwrap();
        assert_eq!(report.options, options);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::Recovered
        );
        assert_eq!(
            validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(Some(100)), &report)
                .unwrap()
                .status,
            RecoveryValidationStatus::VerifiedDomains
        );
        let mut first = prepare_privacy_analysis::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(100)),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        let second = prepare_privacy_analysis::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(100)),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        first.analyzer.set_smt_timeout_ms(Some(123)).unwrap();
        assert_eq!(first.analyzer.smt_timeout_ms(), Some(123));
        assert_eq!(second.analyzer.smt_timeout_ms(), None);
        assert!(first.analyzer.set_smt_timeout_ms(Some(0)).is_err());
        assert_eq!(first.analyzer.smt_timeout_ms(), Some(123));
    }

    #[test]
    fn initial_sat_timeout_is_separate_and_recorded_on_all_exit_paths() {
        for outcome in 0..3 {
            let mut context = prepare_privacy_analysis::<Fr, _, _>(
                &ExampleCircuit::<EXPANDED>::default(),
                4,
                &input(None),
                [CellId::advice(0, 0)],
            )
            .unwrap();
            context.analyzer.set_smt_timeout_ms(Some(2_000)).unwrap();
            let options = PrivacyAnalysisOptions {
                initial_sat_timeout_ms: Some(60_000),
                solver_timeout_ms: Some(2_000),
                ..Default::default()
            };
            let mut queried = false;
            let report = recover_private_inputs(
                context,
                options,
                Instant::now(),
                |context| {
                    assert_eq!(context.analyzer.smt_timeout_ms(), Some(60_000));
                    let answer = match outcome {
                        0 => Ok(Satisfiability::Satisfiable),
                        1 => Ok(Satisfiability::Unsatisfiable),
                        _ => Err(unknown_error(Some("TIMEOUT"))),
                    };
                    (answer, 1)
                },
                |analyzer, input, cell| {
                    queried = true;
                    assert_eq!(analyzer.smt_timeout_ms(), Some(2_000));
                    analyzer.query_ucp_cell_uniqueness_with_value(input, cell)
                },
            )
            .unwrap();
            assert_eq!(report.options, options);
            assert_eq!(report.satisfiability_checks, 1);
            assert_eq!(queried, outcome == 0);
            assert_eq!(
                report.status,
                match outcome {
                    0 => PrivacyAnalysisStatus::Analyzed,
                    1 => PrivacyAnalysisStatus::Inconsistent,
                    _ => PrivacyAnalysisStatus::SolverUnknown,
                }
            );
            assert!(report
                .to_string()
                .contains("Initial SAT solver ms/check and process: 60000"));
        }
        assert_eq!(
            PrivacyAnalysisOptions::default().initial_sat_timeout_ms,
            None
        );
    }

    #[test]
    fn zero_initial_sat_timeout_is_rejected_before_analysis() {
        let error = analyze_private_recoverability::<Fr, _, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            [CellId::advice(0, 0)],
            PrivacyAnalysisOptions {
                initial_sat_timeout_ms: Some(0),
                ..Default::default()
            },
        )
        .unwrap_err();
        assert!(error.to_string().contains("Initial SAT solver timeout"));
    }

    #[test]
    fn driver_preserves_sat_check_counts_on_both_exit_paths() {
        for status in [Satisfiability::Satisfiable, Satisfiability::Unsatisfiable] {
            let satisfiable = status == Satisfiability::Satisfiable;
            let context = prepare_privacy_analysis::<Fr, _, _>(
                &ExampleCircuit::<LINEAR>::default(),
                4,
                &input(Some(100)),
                [CellId::advice(0, 0)],
            )
            .unwrap();
            let mut checks = 0;
            let report = recover_private_inputs(
                context,
                PrivacyAnalysisOptions::default(),
                Instant::now(),
                |_| {
                    checks += 1;
                    // A teszt egy jelöltpróbát és egy eredeti kontextusú ellenőrzést igénylő SAT-vizsgálatot szimulál.
                    (Ok(status), 2)
                },
                |_, _, _| panic!("Initial diagnostics or linear propagation need no cell queries"),
            )
            .unwrap();
            assert_eq!(checks, 1);
            assert_eq!(report.satisfiability_checks, 2);
            assert_eq!(report.semantic_queries, 0);
            if satisfiable {
                assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
                assert_eq!(report.summary.exact_values, 1);
                assert_eq!(report.search_statistics.propagation_runs, 1);
            } else {
                assert_eq!(report.status, PrivacyAnalysisStatus::Inconsistent);
                assert!(report.ucp_result.is_none());
                assert_eq!(report.summary.exact_values, 0);
                assert_eq!(report.search_statistics.propagation_runs, 0);
            }
        }
    }

    #[test]
    fn initial_unknown_never_exports_vacuous_ucp_facts() {
        for (reason, expected) in [
            (Some("TIMEOUT"), RecoveryLimitation::SolverTimeout),
            (
                Some(crate::smt_solver::process::WALLCLOCK_TIMEOUT_REASON),
                RecoveryLimitation::SolverTimeout,
            ),
            (
                Some("RESOURCEOUT"),
                RecoveryLimitation::SolverUnknown {
                    reason: Some("RESOURCEOUT".into()),
                },
            ),
            (None, RecoveryLimitation::SolverUnknown { reason: None }),
        ] {
            let context = prepare_privacy_analysis::<Fr, _, _>(
                &ExampleCircuit::<LINEAR>::default(),
                4,
                &input(Some(100)),
                [CellId::advice(0, 0)],
            )
            .unwrap();
            let report = recover_private_inputs(
                context,
                PrivacyAnalysisOptions {
                    domain_discovery: PrivacyDomainDiscoveryOptions {
                        max_solver_checks: 3,
                        max_values_per_cell: 2,
                        ..Default::default()
                    },
                    domain_refinement: PrivacyDomainRefinementOptions {
                        max_solver_checks: 3,
                        max_candidates_per_cell: 2,
                    },
                    ..Default::default()
                },
                Instant::now(),
                |_| (Err(unknown_error(reason)), 2),
                |_, _, _| panic!("No cell queries before SAT proof"),
            )
            .unwrap();
            assert_eq!(report.status, PrivacyAnalysisStatus::SolverUnknown);
            assert!(report.ucp_result.is_none());
            assert!(report.cells.iter().all(|cell| !cell.domain_is_complete));
            assert_eq!(report.summary.exact_values, 0);
            assert_eq!(report.semantic_queries, 0);
            assert_eq!(report.satisfiability_checks, 2);
            assert_eq!(report.search_statistics.propagation_runs, 0);
            assert_eq!(report.domain_discovery_statistics.solver_checks, 0);
            assert_eq!(report.domain_refinement_statistics.solver_checks, 0);
            assert!(report.cells[0].domain_discovery.is_none());
            assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unknown);
            assert_eq!(
                report.cells[0].recovery_status(),
                PrivateRecoveryStatus::Unresolved
            );
            assert_eq!(report.cells[0].recovery_limitation, Some(expected));
        }
    }

    #[test]
    fn semantic_timeout_preserves_recovery_of_other_cells() {
        let circuit = ExampleCircuit::<MIXED>::default();
        let context = prepare_privacy_analysis::<Fr, _, _>(
            &circuit,
            4,
            &input(Some(100)),
            [CellId::advice(0, 0), CellId::advice(1, 0)],
        )
        .unwrap();
        let report = recover_private_inputs(
            context,
            PrivacyAnalysisOptions::default(),
            Instant::now(),
            check_sat,
            |_, _, _| Err(unknown_error(Some("TIMEOUT"))),
        )
        .unwrap();
        assert_eq!(report.status, PrivacyAnalysisStatus::SolverUnknown);
        assert_eq!(report.semantic_queries, 1);
        assert_eq!(
            report.cells[0].domain,
            Some(UcpValueDomain::exact(BigInt::from(95)))
        );
        assert_eq!(report.cells[0].recovery_limitation, None);
        assert_eq!(
            report.cells[1].recovery_status(),
            PrivateRecoveryStatus::Unresolved
        );
        assert_eq!(
            report.cells[1].recovery_limitation,
            Some(RecoveryLimitation::SolverTimeout)
        );
        assert_eq!(report.cells[1].uniqueness, PrivateCellUniqueness::Unknown);
    }

    #[test]
    fn timeout_does_not_erase_prior_uniqueness_or_invent_a_representation_failure() {
        let mut context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        // A teszt az (s-1)^2=0 egyértelműségi tényét adja át, konkrét számérték nélkül.
        context
            .problem
            .initial_facts
            .mark_unique(CellId::advice(0, 0));
        let report = recover_private_inputs(
            context,
            PrivacyAnalysisOptions::default(),
            Instant::now(),
            check_sat,
            |_, _, _| Err(unknown_error(Some("TIMEOUT"))),
        )
        .unwrap();
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::UniqueWithoutValue
        );
        assert_eq!(
            report.cells[0].recovery_limitation,
            Some(RecoveryLimitation::SolverTimeout)
        );
        assert!(report.cells[0].domain.is_none());
    }

    #[test]
    fn query_limit_keeps_structurally_unique_cells_distinct_from_recovered_values() {
        let mut context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        context
            .problem
            .initial_facts
            .mark_unique(CellId::advice(0, 0));
        let report = recover_private_inputs(
            context,
            PrivacyAnalysisOptions {
                max_semantic_queries: 0,
                ..PrivacyAnalysisOptions::default()
            },
            Instant::now(),
            check_sat,
            |_, _, _| panic!("Zero query quota must not call SMT"),
        )
        .unwrap();
        assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::Unique);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::UniqueWithoutValue
        );
        // A teszt ellenőrzi, hogy modell lekérése nélkül nem feltételez reprezentációs méretkorlátot.
        assert_eq!(
            report.cells[0].recovery_limitation,
            Some(RecoveryLimitation::QueryLimit)
        );
    }

    #[test]
    fn malformed_solver_output_is_an_error_not_an_unknown_report() {
        assert!(limitation_from_solver_error(anyhow::anyhow!("invalid solver response")).is_err());
        let context = prepare_privacy_analysis::<Fr, _, _>(
            &ExampleCircuit::<EXPANDED>::default(),
            4,
            &input(None),
            [CellId::advice(0, 0)],
        )
        .unwrap();
        assert!(recover_private_inputs(
            context,
            PrivacyAnalysisOptions::default(),
            Instant::now(),
            check_sat,
            |_, _, _| Err(anyhow::anyhow!("invalid solver response")),
        )
        .is_err());
    }

    #[test]
    fn non_unique_status_can_still_have_a_finite_candidate_domain() {
        let report = analyze::<CANDIDATES>(Some(2), vec![CellId::advice(0, 0)], 32);
        assert_eq!(
            report.cells[0].recovery_status(),
            PrivateRecoveryStatus::NonUnique
        );
        assert!(matches!(
            report.cells[0].domain,
            Some(UcpValueDomain::FiniteSet(_))
        ));
        assert_eq!(report.cells[0].recovery_limitation, None);
    }

    #[test]
    fn zero_solver_budget_is_rejected_before_synthesis() {
        assert!(analyze_private_recoverability::<Fr, _, _>(
            &ExampleCircuit::<LINEAR>::default(),
            4,
            &input(Some(100)),
            [CellId::advice(0, 0)],
            PrivacyAnalysisOptions {
                solver_timeout_ms: Some(0),
                ..Default::default()
            },
        )
        .is_err());
    }

    #[test]
    fn validates_private_selection_and_public_observation_boundary() {
        let circuit = ExampleCircuit::<LINEAR>::default();
        for targets in [
            vec![],
            vec![CellId::instance(0, 0)],
            vec![CellId::fixed(0, 0)],
            vec![CellId::advice(99, 0)],
        ] {
            assert!(analyze_private_recoverability::<Fr, _, _>(
                &circuit,
                4,
                &input(Some(100)),
                targets,
                PrivacyAnalysisOptions::default(),
            )
            .is_err());
        }
        let mut private_seed = input(Some(100));
        private_seed
            .verification_input
            .instance_cells
            .insert("A-0-0".into(), 95.into());
        assert!(analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &private_seed,
            [CellId::advice(0, 0)],
            PrivacyAnalysisOptions::default(),
        )
        .is_err());
        let mut random = input(Some(100));
        random.verification_method = VerificationMethod::Random;
        assert!(analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &random,
            [CellId::advice(0, 0)],
            PrivacyAnalysisOptions::default(),
        )
        .is_err());
        assert!(analyze_private_recoverability::<Fr, _, _>(
            &circuit,
            4,
            &input(None),
            [CellId::advice(0, 0)],
            PrivacyAnalysisOptions::default(),
        )
        .is_err());
    }
}
