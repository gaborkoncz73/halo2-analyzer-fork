use super::{
    analyzable::{Analyzable, AnalyzableField},
    halo2_proofs_libs::*,
    ucp::{
        cell::{CellId, CellKind},
        plonkish::query_row,
        privacy_subset::OriginalAssertionStore,
        value::{normalize_field_value, UcpValueDomain, UcpValueFacts},
    },
};
use anyhow::{anyhow, Context, Result};
use log::info;
use num::{BigInt, Num};
use num_bigint::Sign;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fs::{self, File, OpenOptions},
    io::Write,
    path::Path,
    process::Command,
};

use lazy_static::lazy_static;

use crate::io::analyzer_io::{output_result, retrieve_user_input_for_underconstrained};
use crate::io::analyzer_io_type::{
    AnalyzerInput, AnalyzerOutput, AnalyzerOutputStatus, AnalyzerType, VerificationMethod,
};
use crate::smt_solver::{
    smt,
    smt::Printer,
    smt_parser::{self, ModelResult, Satisfiability},
};
use crate::{
    circuit_analyzer::abstract_expr::{self, AbsResult},
    io::analyzer_io_type::LookupMethod,
};

#[derive(Debug)]
pub struct Analyzer<F: AnalyzableField> {
    pub cs: ConstraintSystem<F>,
    /// The regions in the circuit.
    pub regions: Vec<Region>,
    pub usable_rows: std::ops::Range<usize>,
    // The fixed cells in the circuit, arranged as [column][row].
    pub fixed: Vec<Vec<BigInt>>,
    pub selectors: Vec<Vec<bool>>,
    pub log: Vec<String>,
    pub permutation: HashMap<String, String>,
    pub instance_cells: HashMap<String, BigInt>,
    pub cell_to_cycle_head: HashMap<String, String>,
    pub counter: u32,
    pub lookup_mappings: Vec<HashMap<String, usize>>,
    pub lookup_tables: Vec<LookupTable>,
    pub analysis_type: AnalyzerType,
    pub prime: String,
    pub all_variables: HashSet<String>,
    pub smt_file: Option<File>,
    pub cycle_abs_value: HashMap<String, AbsResult>,
    pub cycle_bigint_value: HashMap<String, BigInt>,
    pub selector_indices: HashSet<usize>,
    pub ucp_unique_variables: HashSet<String>,
    pub ucp_value_domains: Vec<(String, UcpValueDomain)>,
    //Instance-local UCP solver budget; None retains the legacy environment fallback.
    smt_timeout_ms: Option<u64>,
    // Literal original assertions only; a bounded subset may prove domain exclusion cheaply.
    validation_subset_assertions: Vec<String>,
    // Opt-in recovery metadata; every body is a literal assertion also emitted to the original file.
    original_recovery_assertions: Option<OriginalAssertionStore>,
    // Clearing the exported facts cannot undo assertions already written to the SMT file.
    ucp_assertions_written: bool,
    // Changing verification options cannot release observations or legacy restrictions already written.
    query_context_written: bool,
}

#[derive(Debug)]
pub enum NodeCategory {
    Variable,
    Constant,
    Polynomial,
    Invalid,
}

#[derive(Debug, Clone)]
pub enum NodeType {
    Constant,
    Advice,
    Instance,
    Fixed,
    Negated,
    Mult,
    Add,
    Scaled,
    Poly,
    Invalid,
}

impl NodeType {
    pub fn category(&self) -> NodeCategory {
        match self {
            NodeType::Advice | NodeType::Instance => NodeCategory::Variable,
            NodeType::Fixed | NodeType::Constant => NodeCategory::Constant,
            NodeType::Mult
            | NodeType::Add
            | NodeType::Negated
            | NodeType::Scaled
            | NodeType::Poly => NodeCategory::Polynomial,
            _ => NodeCategory::Invalid,
        }
    }
}

#[derive(Debug)]
pub enum Operation {
    Equal,
    NotEqual,
    And,
    Or,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum SemanticQueryResult {
    ProvenUnique,
    NotUnique,
    Overconstrained,
    Unknown,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SemanticQueryOutput {
    pub result: SemanticQueryResult,
    //Csak rogzitett public adatok es bizonyitott egyertelmuseg mellett adunk konkret erteket.
    pub value: Option<BigInt>,
    pub value_unavailable_reason: Option<ValueRecoveryFailure>,
    /// Feasible target projections from concrete-public, full-model SAT checks only.
    pub samples: Vec<BigInt>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ValueRecoveryFailure {
    RepresentationLimit,
    PublicContextNotConcrete,
    UnavailableConstant,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum DomainEntailmentResult {
    Entailed,
    /// A satisfying assignment whose cell value lies outside the claimed domain.
    Counterexample(BigInt),
    Inconsistent,
}

pub(crate) struct DomainEntailmentQuery {
    pub result: DomainEntailmentResult,
    pub solver_checks: usize,
    pub subset_checks: usize,
}

/// Immutable original constraints and public observations, captured before any UCP assertions.
pub(crate) struct OriginalPrivateQueryContext {
    smt: String,
    variables: HashSet<String>,
    expressions: BTreeMap<CellId, String>,
    constants: BTreeMap<CellId, BigInt>,
    prime: BigInt,
    targeted_subsets: BTreeMap<CellId, (String, usize)>,
}

const MAX_SEARCH_DOMAIN_SIZE: usize = 16;
const MAX_SEARCH_DOMAIN_VALUES: usize = 512;

/// A recovery állapotából igazolt pontos értékeket és kis lefedő domaineket tárol, modellmintákat nem.
#[derive(Default)]
pub(crate) struct PrivateSearchFacts {
    domains: BTreeMap<String, BTreeSet<BigInt>>,
}

pub(crate) struct PrivateModelQuery {
    pub sat: Satisfiability,
    /// Egyetlen teljes kielégítő modell cellánkénti vetületeit adja át, nem pontosérték-tényeket.
    pub samples: BTreeMap<CellId, BigInt>,
}

impl OriginalPrivateQueryContext {
    /// A hívó az eredeti megfigyelések mellett levezetett, helyes Delta-domaineket adja át.
    pub(crate) fn search_facts<F: AnalyzableField>(
        &self,
        analyzer: &Analyzer<F>,
        values: &UcpValueFacts,
    ) -> Result<PrivateSearchFacts> {
        let mut domains = BTreeMap::<String, BTreeSet<BigInt>>::new();
        for (cell, domain) in values.domains() {
            if cell.kind != CellKind::Advice {
                continue;
            }
            let Some(variable) = analyzer.ucp_cell_to_smt_variable_name(cell) else {
                continue;
            };
            if !self.variables.contains(&variable) {
                continue;
            }
            let canonical = match domain {
                UcpValueDomain::Exact(value) => {
                    BTreeSet::from([normalize_field_value(value.clone(), &self.prime)
                        .context("Exact search fact exceeds field representation limits")?])
                }
                UcpValueDomain::FiniteSet(entries) => {
                    if entries.len() > MAX_SEARCH_DOMAIN_SIZE {
                        continue;
                    }
                    entries
                        .iter()
                        .map(|value| normalize_field_value(value.clone(), &self.prime))
                        .collect::<Option<BTreeSet<_>>>()
                        .context("Search domain exceeds field representation limits")?
                }
            };
            if canonical.is_empty() {
                return Err(anyhow!("Empty established search domain"));
            }
            // A másolt cellák domainjeit mezőbeli normalizálás után, közös SMT-név alatt metszi.
            if let Some(previous) = domains.get_mut(&variable) {
                previous.retain(|value| canonical.contains(value));
                if previous.is_empty() {
                    return Err(anyhow!("Conflicting search facts for copied SMT cells"));
                }
            } else {
                domains.insert(variable, canonical);
            }
        }
        let (exact, mut finite): (Vec<_>, Vec<_>) = domains
            .into_iter()
            .partition(|(_, entries)| entries.len() == 1);
        finite.sort_by(|(left, a), (right, b)| a.len().cmp(&b.len()).then_with(|| left.cmp(right)));
        let mut facts = PrivateSearchFacts {
            domains: exact.into_iter().collect(),
        };
        let mut remaining = MAX_SEARCH_DOMAIN_VALUES;
        for (variable, entries) in finite {
            // Az egész többértékű domaint hagyja ki, ha nem fér a többletállítások keretébe.
            if entries.len() <= remaining {
                remaining -= entries.len();
                facts.domains.insert(variable, entries);
            }
        }
        Ok(facts)
    }

    fn write_search_facts<F: AnalyzableField, W: Write>(
        &self,
        printer: &mut Printer<'_, W>,
        target: &str,
        facts: &PrivateSearchFacts,
    ) {
        for (variable, entries) in &facts.domains {
            // A cél saját domainjét és másolati aliasait nem használja a célra vonatkozó kérdés premisszájaként.
            if variable != target {
                let equalities: Vec<_> = entries
                    .iter()
                    .map(|value| Analyzer::<F>::smt_field_equality(variable, value, &self.prime))
                    .collect();
                printer.write_assert_bool(
                    if equalities.len() == 1 {
                        equalities[0].clone()
                    } else {
                        format!("(or {})", equalities.join(" "))
                    },
                    Operation::And,
                );
            }
        }
    }

    pub(crate) fn check_satisfiability<F: AnalyzableField>(
        &self,
        timeout_ms: Option<u64>,
    ) -> Result<Satisfiability> {
        let path = "src/output/private_original_satisfiability.smt2";
        let mut file = File::create(path).context("Failed to create original SAT query")?;
        file.write_all(self.smt.as_bytes())?;
        Ok(Analyzer::<F>::solve_and_get_model_with_timeout(
            path.to_owned(),
            &HashSet::new(),
            timeout_ms,
        )?
        .sat)
    }

    pub(crate) fn has_targeted_subset(&self, cell: &CellId) -> bool {
        self.targeted_subsets.contains_key(cell)
    }

    /// No subset SAT model is exposed: it need not satisfy omitted gates or lookup tuples.
    pub(crate) fn check_unseen_subset<F: AnalyzableField>(
        &self,
        cell: &CellId,
        blocked_values: &BTreeSet<BigInt>,
        timeout_ms: Option<u64>,
    ) -> Result<Satisfiability> {
        let (smt, _) = self
            .targeted_subsets
            .get(cell)
            .context("Missing targeted original subset")?;
        let expression = self
            .expressions
            .get(cell)
            .context("Missing subset target expression")?;
        let path = "src/output/private_recovery_subset.smt2";
        let mut file = File::create(path).context("Failed to create recovery subset query")?;
        file.write_all(smt.as_bytes())?;
        let mut printer = Printer::new(&mut file);
        for value in blocked_values {
            printer.write_assert_bool(
                format!(
                    "(not {})",
                    Analyzer::<F>::smt_field_equality(expression, value, &self.prime)
                ),
                Operation::And,
            );
        }
        Ok(Analyzer::<F>::solve_and_get_model_with_timeout(
            path.to_owned(),
            &HashSet::new(),
            timeout_ms,
        )?
        .sat)
    }

    /// Blocks target values only. Other witness cells remain free in the original context.
    pub(crate) fn query_unseen_value<F: AnalyzableField>(
        &self,
        cell: &CellId,
        blocked_values: &BTreeSet<BigInt>,
        timeout_ms: Option<u64>,
    ) -> Result<Option<BigInt>> {
        self.query_unseen_value_with_search_facts::<F>(
            cell,
            blocked_values,
            timeout_ms,
            &PrivateSearchFacts::default(),
        )
    }

    /// Csak az eredeti C és P következményeit használja fel keresési gyorsításként.
    pub(crate) fn query_unseen_value_with_search_facts<F: AnalyzableField>(
        &self,
        cell: &CellId,
        blocked_values: &BTreeSet<BigInt>,
        timeout_ms: Option<u64>,
        facts: &PrivateSearchFacts,
    ) -> Result<Option<BigInt>> {
        let expression = self
            .expressions
            .get(cell)
            .context("Cell absent from original SMT snapshot")?;
        let path = "src/output/private_domain_discovery.smt2";
        let mut file = File::create(path).context("Failed to create domain discovery file")?;
        file.write_all(self.smt.as_bytes())?;
        let mut printer = Printer::new(&mut file);
        self.write_search_facts::<F, _>(&mut printer, expression, facts);
        for value in blocked_values {
            printer.write_assert_bool(
                format!(
                    "(not {})",
                    Analyzer::<F>::smt_field_equality(expression, value, &self.prime)
                ),
                Operation::And,
            );
        }
        let variables = if self.constants.contains_key(cell) {
            HashSet::new()
        } else {
            HashSet::from([expression.clone()])
        };
        let model = Analyzer::<F>::solve_and_get_model_with_timeout(
            path.to_owned(),
            &variables,
            timeout_ms,
        )?;
        if model.sat == Satisfiability::Unsatisfiable {
            return Ok(None);
        }
        let value = if let Some(value) = self.constants.get(cell) {
            value.clone()
        } else {
            let value = &model
                .result
                .get(expression)
                .context("Missing discovered SMT cell value")?
                .value;
            if BigInt::from_str_radix(&value.order, 10)? != self.prime {
                return Err(anyhow!("Discovered SMT value belongs to a different field"));
            }
            BigInt::from_str_radix(&value.element, 10)
                .context("Invalid discovered SMT field value")?
        };
        // This is a model sample, not an Exact fact. Only exhaustion can establish a complete domain.
        Ok(Some(value))
    }

    /// A separate file per check prevents candidate assumptions from accumulating.
    #[cfg(test)]
    pub(crate) fn check_membership<F: AnalyzableField>(
        &self,
        cell: &CellId,
        domain: &UcpValueDomain,
        exclude: bool,
        timeout_ms: Option<u64>,
    ) -> Result<Satisfiability> {
        self.check_membership_with_search_facts::<F>(
            cell,
            domain,
            exclude,
            timeout_ms,
            &PrivateSearchFacts::default(),
        )
    }

    #[cfg(test)]
    pub(crate) fn check_candidate_with_search_facts<F: AnalyzableField>(
        &self,
        cell: &CellId,
        candidate: &UcpValueDomain,
        timeout_ms: Option<u64>,
        facts: &PrivateSearchFacts,
    ) -> Result<Satisfiability> {
        self.check_membership_with_search_facts::<F>(cell, candidate, false, timeout_ms, facts)
    }

    pub(crate) fn query_candidate_with_search_facts<F: AnalyzableField>(
        &self,
        cell: &CellId,
        candidate: &UcpValueDomain,
        timeout_ms: Option<u64>,
        facts: &PrivateSearchFacts,
        sample_cells: &BTreeSet<CellId>,
    ) -> Result<PrivateModelQuery> {
        self.membership_query_with_samples::<F>(
            cell,
            candidate,
            false,
            timeout_ms,
            facts,
            sample_cells,
        )
    }

    /// Ismert megvalósítható értéknél közvetlenül annak kizárását vizsgálja; nélküle teljes modellt keres.
    pub(crate) fn query_probe_model_with_search_facts<F: AnalyzableField>(
        &self,
        cell: &CellId,
        excluded: Option<&BigInt>,
        timeout_ms: Option<u64>,
        facts: &PrivateSearchFacts,
        sample_cells: &BTreeSet<CellId>,
    ) -> Result<PrivateModelQuery> {
        // Az üres halmaz kizárása nem szűkíti a kontextust, csak a kezdő modell lekérését szolgálja.
        let blocked = excluded.map_or_else(
            || UcpValueDomain::FiniteSet(BTreeSet::new()),
            |value| UcpValueDomain::exact(value.clone()),
        );
        self.membership_query_with_samples::<F>(
            cell,
            &blocked,
            true,
            timeout_ms,
            facts,
            sample_cells,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn membership_query_with_samples<F: AnalyzableField>(
        &self,
        cell: &CellId,
        domain: &UcpValueDomain,
        exclude: bool,
        timeout_ms: Option<u64>,
        facts: &PrivateSearchFacts,
        sample_cells: &BTreeSet<CellId>,
    ) -> Result<PrivateModelQuery> {
        let variables = sample_cells
            .iter()
            .filter(|cell| !self.constants.contains_key(*cell))
            .map(|cell| {
                self.expressions
                    .get(cell)
                    .cloned()
                    .context("Sample cell absent from original SMT snapshot")
            })
            .collect::<Result<HashSet<_>>>()?;
        let model = self.membership_model_with_search_facts::<F>(
            cell, domain, exclude, timeout_ms, facts, &variables,
        )?;
        let samples = self.project_feasible_model(&model, sample_cells)?;
        Ok(PrivateModelQuery {
            sat: model.sat,
            samples,
        })
    }

    fn project_feasible_model(
        &self,
        model: &ModelResult,
        cells: &BTreeSet<CellId>,
    ) -> Result<BTreeMap<CellId, BigInt>> {
        if model.sat != Satisfiability::Satisfiable {
            return Ok(BTreeMap::new());
        }
        cells
            .iter()
            .map(|cell| {
                let value = if let Some(value) = self.constants.get(cell) {
                    value.clone()
                } else {
                    let expression = self
                        .expressions
                        .get(cell)
                        .context("Sample cell absent from original SMT snapshot")?;
                    let value = &model
                        .result
                        .get(expression)
                        .context("Missing requested feasible SMT sample")?
                        .value;
                    if BigInt::from_str_radix(&value.order, 10)? != self.prime {
                        return Err(anyhow!("Feasible SMT sample belongs to a different field"));
                    }
                    BigInt::from_str_radix(&value.element, 10)
                        .context("Invalid feasible SMT sample")?
                };
                let value = normalize_field_value(value, &self.prime)
                    .context("Unsupported feasible SMT sample")?;
                Ok((cell.clone(), value))
            })
            .collect()
    }

    /// A keresési lefedésvizsgálat a többi cella igazolt domainjeit redundáns premisszaként használja.
    #[cfg(test)]
    pub(crate) fn check_coverage_with_search_facts<F: AnalyzableField>(
        &self,
        cell: &CellId,
        domain: &UcpValueDomain,
        timeout_ms: Option<u64>,
        facts: &PrivateSearchFacts,
    ) -> Result<Satisfiability> {
        self.check_membership_with_search_facts::<F>(cell, domain, true, timeout_ms, facts)
    }

    #[cfg(test)]
    fn check_membership_with_search_facts<F: AnalyzableField>(
        &self,
        cell: &CellId,
        domain: &UcpValueDomain,
        exclude: bool,
        timeout_ms: Option<u64>,
        facts: &PrivateSearchFacts,
    ) -> Result<Satisfiability> {
        Ok(self
            .membership_model_with_search_facts::<F>(
                cell,
                domain,
                exclude,
                timeout_ms,
                facts,
                &HashSet::new(),
            )?
            .sat)
    }

    #[allow(clippy::too_many_arguments)]
    fn membership_model_with_search_facts<F: AnalyzableField>(
        &self,
        cell: &CellId,
        domain: &UcpValueDomain,
        exclude: bool,
        timeout_ms: Option<u64>,
        facts: &PrivateSearchFacts,
        variables: &HashSet<String>,
    ) -> Result<ModelResult> {
        let expression = self
            .expressions
            .get(cell)
            .context("Cell absent from original SMT snapshot")?;
        let membership = match domain {
            UcpValueDomain::Exact(value) => {
                Analyzer::<F>::smt_field_equality(expression, value, &self.prime)
            }
            UcpValueDomain::FiniteSet(values) if values.is_empty() => "false".to_owned(),
            UcpValueDomain::FiniteSet(values) => format!(
                "(or {})",
                values
                    .iter()
                    .map(|value| Analyzer::<F>::smt_field_equality(expression, value, &self.prime))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        };
        let path = "src/output/private_domain_refinement.smt2";
        let mut file = File::create(path).context("Failed to create domain refinement file")?;
        file.write_all(self.smt.as_bytes())?;
        let mut printer = Printer::new(&mut file);
        self.write_search_facts::<F, _>(&mut printer, expression, facts);
        printer.write_assert_bool(
            if exclude {
                format!("(not {})", membership)
            } else {
                membership
            },
            Operation::And,
        );
        Analyzer::<F>::solve_and_get_model_with_timeout(path.to_owned(), variables, timeout_ms)
    }
}

const MAX_VALIDATION_SUBSET_ASSERTIONS: usize = 256;

impl From<SemanticQueryResult> for SemanticQueryOutput {
    fn from(result: SemanticQueryResult) -> Self {
        Self {
            result,
            value: None,
            value_unavailable_reason: None,
            samples: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub enum IsZeroExpression {
    ZeroSelector,
    Zero,
    One,
    NonZero,
}

#[derive(Debug)]
pub struct LookupTable {
    pub function_name: String,
    pub function_body: String,
    pub column_indices: Vec<usize>,
    pub row_set: HashSet<Vec<BigInt>>,
    pub match_index: usize,
    pub matched_lookup_exists: bool,
}

lazy_static! {
    pub static ref SMT_FILE_PATH: &'static str = "src/output/out.smt2";
}

impl<'b, F: AnalyzableField> Analyzer<F> {
    pub fn new<ConcreteCircuit: Circuit<F>>(
        circuit: &ConcreteCircuit,
        k: u32,
        analysis_type: AnalyzerType,
        analyzer_input: Option<&AnalyzerInput>,
    ) -> Result<Self, anyhow::Error> {
        Self::new_with_original_subset_capture(circuit, k, analysis_type, analyzer_input, false)
    }

    pub(crate) fn new_with_original_subset_capture<ConcreteCircuit: Circuit<F>>(
        circuit: &ConcreteCircuit,
        k: u32,
        analysis_type: AnalyzerType,
        analyzer_input: Option<&AnalyzerInput>,
        capture_original: bool,
    ) -> Result<Self, anyhow::Error> {
        if let Some(input) = analyzer_input {
            input.verification_input.validate_public_values()?;
        }
        let prime = Self::analyzer_field_modulus()?.to_string();
        let analyzable = Analyzable::config_and_synthesize(circuit, k)?;

        // Convert fixed to an equivalent matrix with BigInt type instead of CellValue
        let mut fixed = Vec::new();
        for col in analyzable.fixed.iter() {
            let mut new_col = Vec::new();

            for cell in col.iter() {
                match cell {
                    CellValue::Assigned(fixed_val) => {
                        let t = BigInt::from_str_radix(
                            format!("{:?}", fixed_val).strip_prefix("0x").unwrap(),
                            16,
                        )
                        .unwrap();
                        new_col.push(t);
                    }
                    CellValue::Unassigned => {
                        new_col.push(BigInt::from(0));
                    }
                    CellValue::Poison(_) => {
                        new_col.push(BigInt::from(0));
                    }
                }
            }

            fixed.push(new_col);
        }

        let mut selector_indices = HashSet::new();
        for selector in &analyzable.cs.selector_map {
            selector_indices.insert(selector.index);
        }
        let (permutation, instance_cells, cell_to_cycle_head, cycle_abs_value, cycle_bigint_value) =
            Analyzer::<F>::extract_permutations(&analyzable.permutation, &fixed);
        let mut analyzer = Analyzer {
            cs: analyzable.cs,
            regions: analyzable.regions,
            usable_rows: analyzable.usable_rows,
            fixed: fixed,
            selectors: analyzable.selectors,
            log: Vec::new(),
            permutation,
            instance_cells,
            cell_to_cycle_head,
            counter: 0,
            lookup_mappings: Vec::new(),
            lookup_tables: Vec::new(),
            analysis_type,
            prime,
            all_variables: HashSet::new(),
            smt_file: None,
            cycle_abs_value: cycle_abs_value,
            cycle_bigint_value,
            selector_indices,
            ucp_unique_variables: HashSet::new(),
            ucp_value_domains: Vec::new(),
            smt_timeout_ms: None,
            validation_subset_assertions: Vec::new(),
            original_recovery_assertions: capture_original.then(OriginalAssertionStore::default),
            ucp_assertions_written: false,
            query_context_written: false,
        };

        fs::create_dir_all("src/output/").unwrap();
        let mut smt_file =
            std::fs::File::create(&*SMT_FILE_PATH).context("Failed to create file!")?;
        let mut printer = Printer::new(&mut smt_file);

        if matches!(
            analyzer.analysis_type,
            AnalyzerType::UnderconstrainedCircuit
        ) {
            let input = analyzer_input.unwrap();
            if input.verification_method == VerificationMethod::Specific
                && input.verification_input.instance_cells.len() == 0
            {
                let instance =
                    retrieve_user_input_for_underconstrained::<Fr>(input, &analyzer.instance_cells)
                        .context("Failed to retrieve user input!")?;
                let specified = crate::io::analyzer_io_type::VerificationInput::new(instance, 1);
                specified.validate_public_values()?;
                analyzer.instance_cells = specified.instance_cells;
            } else if input.verification_method == VerificationMethod::Specific {
                analyzer.instance_cells = analyzer_input
                    .unwrap()
                    .verification_input
                    .instance_cells
                    .clone();
            }

            printer.write_start(analyzer.prime.to_owned());

            analyzer
                .decompose_polynomial(&mut printer, analyzer_input.unwrap())
                .context("Failed to encode circuit constraints for SMT analysis")?;

            for permutation in &analyzer.permutation {
                let mut permutation_r = permutation.0.to_owned();
                let mut permutation_l = permutation.1.to_owned();
                let mut r_is_fixed = false;
                let mut l_is_fixed = false;
                if analyzer
                    .cell_to_cycle_head
                    .contains_key(&permutation.0.to_owned())
                {
                    if analyzer
                        .cycle_abs_value
                        .contains_key(&analyzer.cell_to_cycle_head[&permutation.0.to_owned()])
                    {
                        r_is_fixed = true;
                        permutation_r = format!(
                            "(as ff{:?} F)",
                            analyzer.cycle_bigint_value
                                [&analyzer.cell_to_cycle_head[permutation.0]]
                                .to_owned()
                        );
                    } else {
                        permutation_r = analyzer.cell_to_cycle_head[permutation.0].to_owned();
                    }
                }

                if !analyzer.all_variables.contains(&permutation_r) && !r_is_fixed {
                    analyzer.all_variables.insert(permutation_r.clone());

                    printer.write_var(permutation_r.to_owned());
                }
                if analyzer
                    .cell_to_cycle_head
                    .contains_key(&permutation.1.to_owned())
                {
                    if analyzer
                        .cycle_abs_value
                        .contains_key(&analyzer.cell_to_cycle_head[&permutation.1.to_owned()])
                    {
                        l_is_fixed = true;
                        permutation_l = format!(
                            "(as ff{:?} F)",
                            analyzer.cycle_bigint_value
                                [&analyzer.cell_to_cycle_head[permutation.1]]
                                .to_owned()
                        );
                    } else {
                        permutation_l = analyzer.cell_to_cycle_head[permutation.1].to_owned();
                    }
                }

                if !permutation_l.eq(&permutation_r) {
                    if !analyzer.all_variables.contains(&permutation_l) && !l_is_fixed {
                        analyzer.all_variables.insert(permutation_l.clone());
                        printer.write_var(permutation_l.to_owned());
                    }

                    let neg = format!("(ff.neg {})", permutation_l);
                    let term = printer.write_term(
                        "add".to_owned(),
                        permutation_r.to_owned(),
                        NodeType::Advice,
                        neg,
                        NodeType::Advice,
                    );
                    if analyzer.validation_subset_assertions.len()
                        < MAX_VALIDATION_SUBSET_ASSERTIONS
                    {
                        analyzer
                            .validation_subset_assertions
                            .push(printer.get_assert(
                                term.clone(),
                                "0".to_owned(),
                                NodeType::Poly,
                                Operation::Equal,
                            )?);
                    }
                    if let Some(store) = &mut analyzer.original_recovery_assertions {
                        if store.has_capacity() {
                            let variables = [
                                (!r_is_fixed).then_some(permutation_r),
                                (!l_is_fixed).then_some(permutation_l),
                            ]
                            .into_iter()
                            .flatten();
                            store.retain(
                                printer.get_assert(
                                    term.clone(),
                                    "0".to_owned(),
                                    NodeType::Poly,
                                    Operation::Equal,
                                )?,
                                variables,
                            );
                        }
                    }
                    printer.write_assert(term, "0".to_owned(), NodeType::Poly, Operation::Equal);
                }
            }
        }

        analyzer.smt_file = Some(smt_file);

        Ok(analyzer)
    }

    /// Detects unused custom gates
    ///
    /// This function iterates through the gates in the constraint system (`self.cs`) and checks if each gate is used.
    /// A gate is considered unused if it evaluates to zero for all regions in the layouter (`self.layouter`).
    /// If an unused gate is found, it is logged in the `self.log` vector along with a suggested action.
    /// Finally, the function prints the total number of unused gates found.
    ///
    pub fn analyze_unused_custom_gates(&mut self) -> Result<AnalyzerOutput> {
        let mut count = 0;
        let mut used;
        for gate in self.cs.gates.iter() {
            used = false;

            // is this gate identically zero over regions?
            'region_search: for region in self
                .regions
                .iter()
                .filter(|reg| reg.enabled_selectors.len() > 0)
            {
                let (region_begin, region_end) = region.rows.unwrap();
                let selectors = region.enabled_selectors.keys().cloned().collect();
                for row_num in 0..region_end - region_begin + 1 {
                    for poly in gate.polynomials() {
                        let res = abstract_expr::eval_abstract(
                        poly,
                        &selectors,
                        region_begin,
                        region_end,
                        row_num as i32,
                        &self.fixed,
                        &self.cell_to_cycle_head,
                        &self.cycle_abs_value,
                    )
                    .with_context(|| format!(
                        "Failed to run abstract evaluation for polynomial at region from row: {} to {}.",
                        region_begin, region_end
                    ))?;
                        if res != AbsResult::Zero {
                            used = true;
                            break 'region_search;
                        }
                    }
                }
            }

            if !used {
                count += 1;
                self.log.push(format!("unused gate: \"{}\" (consider removing the gate or checking selectors or fixed assignments in regions)", gate.name()));
            }
        }
        println!("Finished analysis: {} unused gates found.", count);
        if count > 0 {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::UnusedCustomGates,
            })
        } else {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::NoUnusedCustomGates,
            })
        }
    }

    /// Detects unused columns
    ///
    /// This function iterates through the advice queries in the constraint system (`self.cs`) and checks if each column is used.
    /// A column is considered unused if it does not appear in any of the polynomials within the gates of the constraint system.
    /// If an unused column is found, it is logged in the `self.log` vector.
    /// Finally, the function prints the total number of unused columns found.
    ///
    pub fn analyze_unused_columns(&mut self) -> Result<AnalyzerOutput> {
        let mut count = 0;
        let mut used;
        for (column, rotation) in self.cs.advice_queries.iter().cloned() {
            used = false;

            for gate in self.cs.gates.iter() {
                for poly in gate.polynomials() {
                    let advices = abstract_expr::extract_columns(poly);
                    if advices.contains(&(column.into(), rotation)) {
                        used = true;
                    }
                }
            }

            if !used {
                count += 1;
                self.log.push(format!("unused column: {:?}", column));
            }
        }
        println!("Finished analysis: {} unused columns found.", count);
        if count > 0 {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::UnusedColumns,
            })
        } else {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::NoUnusedColumns,
            })
        }
    }

    /// Detect assigned but unconstrained cells:
    /// (does it occur in a not-identially zero polynomial in the region?)
    /// (if not almost certainly a bug)
    pub fn analyze_unconstrained_cells(&mut self) -> Result<AnalyzerOutput> {
        let mut count = 0;

        //Index the gate polynomials by the advice column/rotation they query.
        //The previous implementation rescanned and re-evaluated every polynomial on
        //every region row for every assigned cell, which was prohibitively expensive
        //for large circuits.
        let mut queries_by_column: HashMap<Column<Any>, Vec<(&Expression<F>, Rotation)>> =
            HashMap::new();
        for gate in &self.cs.gates {
            for poly in gate.polynomials() {
                for (column, rotation) in abstract_expr::extract_columns(poly) {
                    queries_by_column
                        .entry(column)
                        .or_default()
                        .push((poly, rotation));
                }
            }
        }

        for region in self.regions.iter() {
            let selectors = region.enabled_selectors.keys().cloned().collect();
            // A region that only adds copy constraints does not assign cells, so Halo2
            // legitimately leaves its row range unset. There are no assigned cells to
            // classify in such a region; the permutation assembly is analysed separately.
            let Some((region_begin, region_end)) = region.rows else {
                continue;
            };
            for cell in region.cells.clone() {
                #[cfg(any(
                    feature = "use_pse_halo2_proofs",
                    feature = "use_axiom_halo2_proofs",
                    feature = "use_scroll_halo2_proofs",
                    feature = "use_pse_v1_halo2_proofs"
                ))]
                let (reg_column, rotation) = (cell.0 .0, cell.1);
                #[cfg(feature = "use_zcash_halo2_proofs")]
                let (reg_column, assigned_row) = (cell.0, cell.1);

                if matches!(reg_column.column_type, Any::Fixed) {
                    continue;
                }

                //A permutation/copy constraint is itself a constraint. A cell in a
                //non-trivial permutation cycle must therefore not be reported as wholly
                //unconstrained even when it is not queried directly by a custom gate.
                let column_prefix = match reg_column.column_type {
                    Any::Advice => 'A',
                    Any::Instance => 'I',
                    Any::Fixed => unreachable!(),
                };
                let cell_name = format!("{}-{}-{}", column_prefix, reg_column.index, assigned_row);
                let mut used = self.cell_to_cycle_head.contains_key(&cell_name);

                if !used {
                    if let Some(queries) = queries_by_column.get(&reg_column) {
                        for (poly, query_rotation) in queries {
                            //A query at rotation r, evaluated on local row q, addresses
                            //region_begin + q + r. Solve this for q to evaluate only the
                            //single row on which it can refer to the assigned cell.
                            let local_row = i64::try_from(assigned_row).unwrap()
                                - i64::try_from(region_begin).unwrap()
                                - i64::from(query_rotation.0);
                            if local_row < 0
                                || local_row > i64::try_from(region_end - region_begin).unwrap()
                            {
                                continue;
                            }

                            let eval = abstract_expr::eval_abstract(
                                poly,
                                &selectors,
                                region_begin,
                                region_end,
                                i32::try_from(local_row).unwrap(),
                                &self.fixed,
                                &self.cell_to_cycle_head,
                                &self.cycle_abs_value,
                            )
                            .with_context(|| format!(
                                "Failed to run abstract evaluation for polynomial at region from row: {} to {}.",
                                region_begin, region_end
                            ))?;
                            if eval != AbsResult::Zero {
                                used = true;
                                break;
                            }
                        }
                    }
                }

                if !used {
                    count += 1;
                    self.log.push(format!("unconstrained cell in \"{}\" region: {:?} (row: {:?}) -- very likely a bug.", region.name, reg_column, assigned_row));
                }
            }
        }
        println!("Finished analysis: {} unconstrained cells found.", count);
        if count > 0 {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::UnconstrainedCells,
            })
        } else {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::NoUnconstrainedCells,
            })
        }
    }
    // Define a function to extract permutations from the provided permutation assembly.
    // Returns three HashMaps containing pairs, instances, and cell-to-cycle head mappings.

    pub fn extract_permutations(
        permutation: &permutation::keygen::Assembly,
        fixed: &Vec<Vec<BigInt>>,
    ) -> (
        HashMap<String, String>,
        HashMap<String, BigInt>,
        HashMap<String, String>,
        HashMap<String, AbsResult>,
        HashMap<String, BigInt>,
    ) {
        let mut pairs = HashMap::<String, String>::new();
        let mut instances = HashMap::<String, BigInt>::new();
        let mut cycles = Vec::<Vec<String>>::new();
        let mut num_of_cycles = 0;
        let mut cell_to_cycle_head = HashMap::<String, String>::new();
        let mut cycle_abs_value: HashMap<String, AbsResult> = HashMap::new();
        let mut cycle_bigint_value: HashMap<String, BigInt> = HashMap::new();

        for col in 0..permutation.sizes.len() {
            for row in 0..permutation.sizes[col].len() {
                if permutation.sizes[col][row] > 1 {
                    let mut cycle = Vec::<String>::new();
                    num_of_cycles = num_of_cycles + 1;
                    let mut cycle_length = permutation.sizes[col][row];
                    let mut cycle_col = col;
                    let mut cycle_row = row;
                    while cycle_length > 1 {
                        let mut is_instance: bool = false;
                        let mut left_is_fixed: bool = false;
                        let mut left_abs = AbsResult::Variable;
                        let mut left_big_int_val = BigInt::from(0);
                        let mut right_is_fixed: bool = false;
                        let mut right_abs = AbsResult::Variable;
                        let mut right_big_int_val = BigInt::from(0);
                        let left_cell = permutation.columns[cycle_col];

                        #[cfg(any(
                            feature = "use_zcash_halo2_proofs",
                            feature = "use_pse_v1_halo2_proofs",
                        ))]
                        let left_column_abr = match left_cell.column_type() {
                            Any::Advice => 'A',
                            Any::Fixed => {
                                left_is_fixed = true;
                                'F'
                            }
                            Any::Instance => {
                                is_instance = true;
                                'I'
                            }
                        };
                        #[cfg(any(
                            feature = "use_pse_halo2_proofs",
                            feature = "use_axiom_halo2_proofs",
                            feature = "use_scroll_halo2_proofs"
                        ))]
                        let left_column_abr = match left_cell.column_type() {
                            Any::Advice(_) => 'A',
                            Any::Fixed => {
                                left_is_fixed = true;
                                'F'
                            }
                            Any::Instance => {
                                is_instance = true;
                                'I'
                            }
                        };
                        let left_column_index = left_cell.index;
                        let left =
                            format!("{}-{}-{}", left_column_abr, left_column_index, cycle_row);
                        if left_is_fixed {
                            left_big_int_val = fixed[left_column_index][cycle_row].clone();
                            if left_big_int_val.sign() == Sign::NoSign {
                                left_abs = AbsResult::Zero;
                            } else {
                                left_abs = AbsResult::NonZero;
                            }
                        }
                        if is_instance {
                            instances.insert(left.clone(), BigInt::from(0));
                        }
                        is_instance = false;
                        let (right_cell_col, right_cell_row) =
                            permutation.mapping[cycle_col][cycle_row];
                        let right_cell = permutation.columns[right_cell_col];
                        #[cfg(any(
                            feature = "use_zcash_halo2_proofs",
                            feature = "use_pse_v1_halo2_proofs",
                        ))]
                        let right_column_abr = match right_cell.column_type() {
                            Any::Advice => 'A',
                            Any::Fixed => {
                                right_is_fixed = true;
                                'F'
                            }
                            Any::Instance => {
                                is_instance = true;
                                'I'
                            }
                        };
                        #[cfg(any(
                            feature = "use_pse_halo2_proofs",
                            feature = "use_axiom_halo2_proofs",
                            feature = "use_scroll_halo2_proofs"
                        ))]
                        let right_column_abr = match right_cell.column_type() {
                            Any::Advice(_) => 'A',
                            Any::Fixed => {
                                right_is_fixed = true;
                                'F'
                            }
                            Any::Instance => {
                                is_instance = true;
                                'I'
                            }
                        };
                        let right_column_index = right_cell.index;
                        let right = format!(
                            "{}-{}-{}",
                            right_column_abr, right_column_index, right_cell_row
                        );
                        if right_is_fixed {
                            right_big_int_val = fixed[right_column_index][right_cell_row].clone();
                            if right_big_int_val.sign() == Sign::NoSign {
                                right_abs = AbsResult::Zero;
                            } else {
                                right_abs = AbsResult::NonZero;
                            }
                        }
                        if is_instance {
                            instances.insert(right.clone(), BigInt::from(0));
                        }
                        pairs.insert(left.clone(), right.clone());

                        if cycle.is_empty() {
                            cycle.push(left.clone());
                        }
                        cycle.push(right.clone());
                        if is_instance {
                            cell_to_cycle_head.insert(left.clone(), right.clone());
                            cell_to_cycle_head.insert(right.clone(), right.clone());
                        } else {
                            cell_to_cycle_head.insert(right.clone(), left.clone());
                            cell_to_cycle_head.insert(left.clone(), left.clone());
                        }

                        if right_is_fixed {
                            cycle_abs_value.insert(cell_to_cycle_head[&right].clone(), right_abs);
                            cycle_bigint_value
                                .insert(cell_to_cycle_head[&right].clone(), right_big_int_val);
                        } else if left_is_fixed {
                            cycle_abs_value.insert(cell_to_cycle_head[&left].clone(), left_abs);
                            cycle_bigint_value
                                .insert(cell_to_cycle_head[&left].clone(), left_big_int_val);
                        }
                        cycle_col = right_cell_col;
                        cycle_row = right_cell_row;
                        cycle_length -= 1;
                    }
                    cycles.push(cycle);
                }
            }
        }
        (
            pairs,
            instances,
            cell_to_cycle_head,
            cycle_abs_value,
            cycle_bigint_value,
        )
    }

    pub fn extract_lookups(
        &mut self,
        printer: &mut smt::Printer<File>,
        cons_str_vec: Option<Vec<String>>,
    ) -> Result<()> {
        let mut lookup_index = 0;
        #[cfg(any(
            feature = "use_zcash_halo2_proofs",
            feature = "use_pse_halo2_proofs",
            feature = "use_axiom_halo2_proofs",
            feature = "use_pse_v1_halo2_proofs",
        ))]
        let lookups = self.cs.lookups.clone();
        #[cfg(any(feature = "use_scroll_halo2_proofs",))]
        let lookups = self.cs.lookups_map.clone();
        for lookup in lookups.iter() {
            let mut col_indices = Vec::new();
            #[cfg(any(
                feature = "use_zcash_halo2_proofs",
                feature = "use_pse_halo2_proofs",
                feature = "use_axiom_halo2_proofs",
                feature = "use_pse_v1_halo2_proofs",
            ))]
            let table_expressions = lookup.table_expressions.clone();
            #[cfg(any(feature = "use_scroll_halo2_proofs",))]
            let table_expressions = lookup.1.table.clone();
            for col in table_expressions {
                if let Expression::Fixed(fixed_query) = col {
                    col_indices.push(fixed_query.column_index);
                }
            }

            let row_set = self.extract_lookup_columns(&col_indices);

            let (big_cons_str, matched_lookup_exists, index) =
                Self::extract_lookup_constraints_as_function(
                    self,
                    col_indices.clone(),
                    cons_str_vec.clone(),
                    printer,
                    row_set.clone(),
                )?;

            let function_body = printer.get_or(big_cons_str);

            if matched_lookup_exists {
                self.lookup_tables.push(LookupTable {
                    function_name: String::new(),
                    function_body: String::new(),
                    column_indices: Vec::new(),
                    row_set: HashSet::new(),
                    match_index: index,
                    matched_lookup_exists,
                });
            } else {
                self.lookup_tables.push(LookupTable {
                    function_name: format!("isInLookupTable{}", lookup_index),
                    function_body: function_body,
                    column_indices: col_indices.clone(),
                    row_set,
                    match_index: 0 as usize,
                    matched_lookup_exists,
                });
            }
            lookup_index += 1;
        }
        Ok(())
    }

    /// Analyzes underconstrained circuits and generates an analyzer output.
    ///
    /// This function performs the analysis of underconstrained circuits. It takes as input an `analyzer_input` struct
    /// containing the required information for the analysis, and a `fixed` vector representing the vallues of fixed columns.
    /// The function creates an SMT file, decomposes the polynomials, writes the necessary variables and assertions, and runs
    /// the control uniqueness function to determine the `output_status` of the analysis.
    /// The analyzer output is returned as a `Result` indicating success or an error if the analysis fails.
    pub fn analyze_underconstrained(
        &mut self,
        analyzer_input: &AnalyzerInput,
    ) -> Result<AnalyzerOutput> {
        analyzer_input.verification_input.validate_public_values()?;
        let mut analyzer_output: AnalyzerOutput = AnalyzerOutput {
            output_status: AnalyzerOutputStatus::Invalid,
        };

        let output_status: AnalyzerOutputStatus = Self::uniqueness_assertion(self, &analyzer_input)
            .context("Failed to run control uniqueness function!")?;

        analyzer_output.output_status = output_status;
        output_result(analyzer_input, &analyzer_output);

        Ok(analyzer_output)
    }

    #[cfg(test)]
    pub fn log(&self) -> &[String] {
        &self.log
    }

    pub fn set_ucp_unique_cells<I>(&mut self, cells: I)
    where
        I: IntoIterator<Item = CellId>,
    {
        self.ucp_unique_variables = cells
            .into_iter()
            .filter_map(|cell| self.ucp_cell_to_smt_variable_name(&cell))
            .collect();
    }

    pub fn ucp_unique_variables(&self) -> &HashSet<String> {
        &self.ucp_unique_variables
    }

    pub fn set_ucp_value_facts(&mut self, value_facts: &UcpValueFacts) {
        self.ucp_value_domains = value_facts
            .domains()
            .iter()
            .filter_map(|(cell, domain)| {
                self.ucp_cell_to_smt_variable_name(cell)
                    .map(|variable| (variable, domain.clone()))
            })
            .collect();
    }

    pub fn ucp_value_domains(&self) -> &[(String, UcpValueDomain)] {
        &self.ucp_value_domains
    }

    pub fn query_ucp_cell_uniqueness(
        &mut self,
        analyzer_input: &AnalyzerInput,
        query_cell: &CellId,
    ) -> Result<SemanticQueryResult> {
        Ok(self
            .query_ucp_cell(analyzer_input, query_cell, false)?
            .result)
    }

    pub fn query_ucp_cell_uniqueness_with_value(
        &mut self,
        analyzer_input: &AnalyzerInput,
        query_cell: &CellId,
    ) -> Result<SemanticQueryOutput> {
        self.query_ucp_cell(analyzer_input, query_cell, true)
    }

    /// Bounds each solver process and CVC5 check without changing global environment.
    pub fn set_smt_timeout_ms(&mut self, milliseconds: Option<u64>) -> Result<()> {
        self.smt_timeout_ms = Self::resolve_smt_timeout_ms(milliseconds)?;
        Ok(())
    }

    pub fn smt_timeout_ms(&self) -> Option<u64> {
        self.smt_timeout_ms
    }

    /// Capture C before concrete public assertions; clearing an input map cannot undo earlier queries.
    pub(crate) fn original_private_query_context_without_observations(
        &mut self,
        input: &AnalyzerInput,
        cells: &[CellId],
    ) -> Result<OriginalPrivateQueryContext> {
        if self.query_context_written {
            return Err(anyhow!(
                "Unobserved SMT snapshot requires a fresh query context"
            ));
        }
        let mut unobserved = input.clone();
        unobserved.verification_method = VerificationMethod::None;
        unobserved.verification_input.instance_cells.clear();
        self.original_private_query_context(&unobserved, cells)
    }

    /// Caller establishes original SAT separately. Neither witness samples nor inferred facts are copied.
    pub(crate) fn original_private_query_context(
        &mut self,
        input: &AnalyzerInput,
        cells: &[CellId],
    ) -> Result<OriginalPrivateQueryContext> {
        if self.ucp_assertions_written
            || !self.ucp_value_domains.is_empty()
            || !self.ucp_unique_variables.is_empty()
        {
            return Err(anyhow!(
                "Original SMT snapshot requires an unstrengthened analyzer"
            ));
        }
        let (_, prime) = self.prepare_ucp_query_context(input)?;
        let mut expressions = BTreeMap::new();
        let mut constants = BTreeMap::new();
        for cell in cells {
            let expression = if let Some(variable) = self.ucp_cell_to_smt_variable_name(cell) {
                if self.all_variables.insert(variable.clone()) {
                    Printer::new(self.smt_file.as_mut().context("Missing SMT file")?)
                        .write_var(variable.clone());
                }
                variable
            } else {
                let value = self
                    .ucp_cell_constant_value(cell)
                    .context("Cannot resolve private SMT cell")?;
                constants.insert(cell.clone(), value.clone());
                format!(
                    "(as ff{} F)",
                    Self::normalize_ucp_field_value(&value, &prime)
                )
            };
            expressions.insert(cell.clone(), expression);
        }
        let mut targeted_subsets = BTreeMap::new();
        if let Some(store) = &self.original_recovery_assertions {
            let index = store.index();
            let public_variables = input
                .verification_input
                .instance_cells
                .keys()
                .cloned()
                .collect();
            for (cell, expression) in &expressions {
                if constants.contains_key(cell) {
                    continue;
                }
                let selected = store.select(expression, &public_variables, &index);
                if selected.is_empty() {
                    continue;
                }
                let mut variables: BTreeSet<_> = selected
                    .iter()
                    .flat_map(|assertion| assertion.variables.iter().cloned())
                    .collect();
                variables.insert(expression.clone());
                variables.extend(input.verification_input.instance_cells.keys().cloned());
                let mut bytes = Vec::new();
                let mut printer = Printer::new(&mut bytes);
                printer.write_start(self.prime.clone());
                for variable in variables {
                    printer.write_var(variable);
                }
                for assertion in &selected {
                    printer.write_assert_bool(assertion.body.clone(), Operation::And);
                }
                if input.verification_method == VerificationMethod::Specific {
                    for (name, value) in &input.verification_input.instance_cells {
                        printer.write_assert_bool(
                            Self::smt_field_equality(name, value, &prime),
                            Operation::And,
                        );
                    }
                }
                targeted_subsets.insert(cell.clone(), (String::from_utf8(bytes)?, selected.len()));
            }
        }
        Ok(OriginalPrivateQueryContext {
            smt: fs::read_to_string(&*SMT_FILE_PATH)
                .context("Failed to capture original SMT model")?,
            variables: self.all_variables.clone(),
            expressions,
            constants,
            prime,
            targeted_subsets,
        })
    }

    /// Checks that the current constraints and public observations admit a witness.
    pub fn check_ucp_satisfiability(
        &mut self,
        analyzer_input: &AnalyzerInput,
    ) -> Result<Satisfiability> {
        let (variables, _) = self.prepare_ucp_query_context(analyzer_input)?;
        Ok(Self::solve_and_get_model_with_timeout(
            SMT_FILE_PATH.to_string(),
            &variables,
            self.smt_timeout_ms,
        )?
        .sat)
    }

    /// A SAT answer under temporary candidate equalities also proves original SAT.
    /// UNSAT/unknown says nothing about the original context. Never retains the candidates.
    pub(crate) fn check_ucp_satisfiability_with_hints(
        &mut self,
        analyzer_input: &AnalyzerInput,
        hints: &UcpValueFacts,
    ) -> Result<Option<Satisfiability>> {
        if self.ucp_assertions_written
            || !self.ucp_value_domains.is_empty()
            || !self.ucp_unique_variables.is_empty()
        {
            return Err(anyhow!("SAT hints require an unstrengthened analyzer"));
        }
        let (_, prime) = self.prepare_ucp_query_context(analyzer_input)?;
        let equalities: BTreeSet<_> = hints
            .domains()
            .iter()
            .filter_map(|(cell, domain)| match domain {
                UcpValueDomain::Exact(value) if cell.kind == CellKind::Advice => self
                    .ucp_cell_to_smt_variable_name(cell)
                    .filter(|variable| self.all_variables.contains(variable))
                    .map(|variable| Self::smt_field_equality(&variable, value, &prime)),
                _ => None,
            })
            .collect();
        if equalities.is_empty() {
            return Ok(None);
        }
        let smt_file = self.smt_file.as_mut().context("Failed to open SMT file")?;
        let mut printer = Printer::new(smt_file);
        printer.write_push(1);
        for equality in equalities {
            printer.write_assert_bool(equality, Operation::And);
        }
        // Only existence is needed; no candidate model becomes a recovered value.
        let result = Self::solve_and_get_model_with_timeout(
            SMT_FILE_PATH.to_string(),
            &HashSet::new(),
            self.smt_timeout_ms,
        );
        printer.write_pop(1);
        result.map(|model| Some(model.sat))
    }

    /// For a fresh analyzer with no inferred assertions: checks C AND public AND x NOT IN domain.
    /// The caller must not reuse an analyzer previously strengthened with UCP facts.
    #[cfg(test)]
    pub(crate) fn query_private_domain_entailment(
        &mut self,
        analyzer_input: &AnalyzerInput,
        cell: &CellId,
        domain: &UcpValueDomain,
    ) -> Result<DomainEntailmentResult> {
        Ok(self
            .query_private_domain_entailment_internal(analyzer_input, cell, domain, true)?
            .result)
    }

    /// Requires a just-established SAT result for this fresh circuit/public context.
    /// Only the validator uses this path; it avoids repeating the same original SAT check.
    pub(crate) fn query_private_domain_entailment_after_sat(
        &mut self,
        analyzer_input: &AnalyzerInput,
        cell: &CellId,
        domain: &UcpValueDomain,
    ) -> Result<DomainEntailmentQuery> {
        self.query_private_domain_entailment_internal(analyzer_input, cell, domain, false)
    }

    fn query_private_domain_entailment_internal(
        &mut self,
        analyzer_input: &AnalyzerInput,
        cell: &CellId,
        domain: &UcpValueDomain,
        check_base: bool,
    ) -> Result<DomainEntailmentQuery> {
        if self.ucp_assertions_written
            || !self.ucp_value_domains.is_empty()
            || !self.ucp_unique_variables.is_empty()
        {
            return Err(anyhow!(
                "Domain validation must not assume inferred UCP facts"
            ));
        }
        let variable = self.ucp_cell_to_smt_variable_name(cell);
        let expression = if let Some(variable) = &variable {
            if self.all_variables.insert(variable.clone()) {
                let smt_file = self.smt_file.as_mut().context("Failed to open SMT file")?;
                Printer::new(smt_file).write_var(variable.clone());
            }
            variable.clone()
        } else {
            let constant = self
                .ucp_cell_constant_value(cell)
                .context("Cannot resolve cell to an SMT variable or a fixed constant")?;
            let prime = BigInt::from_str_radix(&self.prime, 10)?;
            format!(
                "(as ff{} F)",
                Self::normalize_ucp_field_value(&constant, &prime)
            )
        };
        let (_, prime) = self.prepare_ucp_query_context(analyzer_input)?;
        let mut solver_checks = 0;
        let mut subset_checks = 0;
        if check_base {
            solver_checks += 1;
            let base = Self::solve_and_get_model_with_timeout(
                SMT_FILE_PATH.to_string(),
                &HashSet::new(),
                self.smt_timeout_ms,
            )?;
            if base.sat == Satisfiability::Unsatisfiable {
                return Ok(DomainEntailmentQuery {
                    result: DomainEntailmentResult::Inconsistent,
                    solver_checks,
                    subset_checks,
                });
            }
        }
        let membership = match domain {
            UcpValueDomain::Exact(value) => Self::smt_field_equality(&expression, value, &prime),
            UcpValueDomain::FiniteSet(values) if values.is_empty() => "false".to_string(),
            UcpValueDomain::FiniteSet(values) => format!(
                "(or {})",
                values
                    .iter()
                    .map(|value| Self::smt_field_equality(&expression, value, &prime))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        };
        let exclusion = format!("(not {})", membership);
        if !check_base && !self.validation_subset_assertions.is_empty() {
            solver_checks += 1;
            subset_checks += 1;
            // UNSAT of a weaker conjunction proves full exclusion; SAT is not a counterexample.
            let subset = self.check_private_domain_subset(analyzer_input, &exclusion, &prime);
            if Self::subset_proves_exclusion(subset)? {
                return Ok(DomainEntailmentQuery {
                    result: DomainEntailmentResult::Entailed,
                    solver_checks,
                    subset_checks,
                });
            }
        }
        let smt_file = self.smt_file.as_mut().context("Failed to open SMT file")?;
        let mut printer = Printer::new(smt_file);
        printer.write_push(1);
        printer.write_assert_bool(exclusion, Operation::And);
        solver_checks += 1;
        let model_variables = variable.iter().cloned().collect();
        let counterexample = Self::solve_and_get_model_with_timeout(
            SMT_FILE_PATH.to_string(),
            &model_variables,
            self.smt_timeout_ms,
        );
        //Restore the scope even on solver errors; no tested claim becomes a premise.
        printer.write_pop(1);
        let counterexample = counterexample.context("Failed to validate recovered domain")?;
        if counterexample.sat == Satisfiability::Unsatisfiable {
            return Ok(DomainEntailmentQuery {
                result: DomainEntailmentResult::Entailed,
                solver_checks,
                subset_checks,
            });
        }
        let value = if let Some(variable) = variable {
            let value = &counterexample
                .result
                .get(&variable)
                .context("Missing domain counterexample value")?
                .value
                .element;
            BigInt::from_str_radix(value, 10)?
        } else {
            self.ucp_cell_constant_value(cell)
                .context("Missing fixed counterexample")?
        };
        Ok(DomainEntailmentQuery {
            result: DomainEntailmentResult::Counterexample(
                normalize_field_value(value.clone(), &prime).unwrap_or(value),
            ),
            solver_checks,
            subset_checks,
        })
    }

    fn subset_proves_exclusion(result: Result<Satisfiability>) -> Result<bool> {
        match result {
            Ok(Satisfiability::Unsatisfiable) => Ok(true),
            Ok(Satisfiability::Satisfiable) => Ok(false),
            Err(error)
                if error
                    .downcast_ref::<smt_parser::UnknownSolverResult>()
                    .is_some() =>
            {
                Ok(false)
            }
            Err(error) => Err(error),
        }
    }

    fn check_private_domain_subset(
        &self,
        analyzer_input: &AnalyzerInput,
        exclusion: &str,
        prime: &BigInt,
    ) -> Result<Satisfiability> {
        let path = "src/output/private_domain_subset.smt2";
        let mut file = File::create(path).context("Failed to create validation subset file")?;
        let mut printer = Printer::new(&mut file);
        printer.write_start(self.prime.clone());
        for variable in self.all_variables.iter().collect::<BTreeSet<_>>() {
            printer.write_var(variable.clone());
        }
        for assertion in &self.validation_subset_assertions {
            printer.write_assert_bool(assertion.clone(), Operation::And);
        }
        if analyzer_input.verification_method == VerificationMethod::Specific {
            for (name, value) in &analyzer_input.verification_input.instance_cells {
                printer.write_assert_bool(
                    Self::smt_field_equality(name, value, prime),
                    Operation::And,
                );
            }
        }
        printer.write_assert_bool(exclusion.to_owned(), Operation::And);
        Ok(Self::solve_and_get_model_with_timeout(
            path.to_owned(),
            &HashSet::new(),
            self.smt_timeout_ms,
        )?
        .sat)
    }

    fn prepare_ucp_query_context(
        &mut self,
        analyzer_input: &AnalyzerInput,
    ) -> Result<(HashSet<String>, BigInt)> {
        analyzer_input.verification_input.validate_public_values()?;
        let mut vars_to_declare = Vec::new();
        for (var, _) in &self.ucp_value_domains {
            if self.all_variables.insert(var.clone()) {
                vars_to_declare.push(var.clone());
            }
        }
        if analyzer_input.verification_method == VerificationMethod::Specific {
            for var in analyzer_input.verification_input.instance_cells.keys() {
                if self.all_variables.insert(var.clone()) {
                    vars_to_declare.push(var.clone());
                }
            }
        }
        let prime =
            BigInt::from_str_radix(&self.prime, 10).context("Failed to parse analyzer prime!")?;
        let smt_file = self.smt_file.as_mut().context("Failed to open SMT file!")?;
        let mut printer = Printer::new(smt_file);
        for var in vars_to_declare {
            printer.write_var(var);
        }
        Self::write_ucp_value_domain_assertions(&mut printer, &self.ucp_value_domains, &prime)?;
        self.ucp_assertions_written |= !self.ucp_value_domains.is_empty();
        if analyzer_input.verification_method == VerificationMethod::Specific {
            self.query_context_written |=
                !analyzer_input.verification_input.instance_cells.is_empty();
            for (var, value) in &analyzer_input.verification_input.instance_cells {
                printer.write_assert(
                    var.clone(),
                    Self::normalize_ucp_field_value(value, &prime),
                    NodeType::Instance,
                    Operation::Equal,
                );
            }
        }
        Ok((self.all_variables.clone(), prime))
    }

    fn query_ucp_cell(
        &mut self,
        analyzer_input: &AnalyzerInput,
        query_cell: &CellId,
        include_value: bool,
    ) -> Result<SemanticQueryOutput> {
        let Some(query_variable) = self.ucp_cell_to_smt_variable_name(query_cell) else {
            let constant = self.ucp_cell_constant_value(query_cell);
            let value = if include_value {
                constant.clone().and_then(|value| {
                    let prime = BigInt::from_str_radix(&self.prime, 10).ok()?;
                    normalize_field_value(value, &prime)
                })
            } else {
                None
            };
            return Ok(SemanticQueryOutput {
                result: SemanticQueryResult::ProvenUnique,
                value_unavailable_reason: if include_value && value.is_none() {
                    Some(if constant.is_some() {
                        ValueRecoveryFailure::RepresentationLimit
                    } else {
                        ValueRecoveryFailure::UnavailableConstant
                    })
                } else {
                    None
                },
                value,
                samples: Vec::new(),
            });
        };

        if !include_value && self.ucp_unique_variables.contains(&query_variable) {
            return Ok(SemanticQueryResult::ProvenUnique.into());
        }

        if self.all_variables.insert(query_variable.clone()) {
            let smt_file = self.smt_file.as_mut().context("Failed to open SMT file!")?;
            Printer::new(smt_file).write_var(query_variable.clone());
        }

        let (variables, prime) = self.prepare_ucp_query_context(analyzer_input)?;
        let ucp_unique_variables = self.ucp_unique_variables.clone();
        let ucp_value_domains = self.ucp_value_domains.clone();
        //Szabad public valtozobol egy modell csak egy mintat adna, nem globalis Exact tenyt.
        let can_recover_value = include_value
            && analyzer_input.lookup_method != LookupMethod::Uninterpreted
            && variables
                .iter()
                .filter(|var| var.starts_with("I-"))
                .all(|var| {
                    (analyzer_input.verification_method == VerificationMethod::Specific
                        && analyzer_input
                            .verification_input
                            .instance_cells
                            .contains_key(var))
                        || ucp_value_domains
                            .iter()
                            .any(|(name, domain)| name == var && domain.is_singleton())
                });

        if let Some(smt_file) = self.smt_file.as_mut() {
            let mut printer = Printer::new(smt_file);

            let model = Self::solve_and_get_model_with_timeout(
                SMT_FILE_PATH.to_string(),
                &variables,
                self.smt_timeout_ms,
            )
            .context("Failed to solve SMT model for semantic uniqueness query!")?;
            if matches!(model.sat, Satisfiability::Unsatisfiable) {
                return Ok(SemanticQueryResult::Overconstrained.into());
            }

            let Some(query_value) = model.result.get(&query_variable) else {
                return Ok(SemanticQueryResult::Unknown.into());
            };

            printer.write_push(1);

            let mut same_assignments = Vec::new();
            //Konkret visszaallitasnal K modellbeli ertekeit sem feltetelezzuk: magat az erteket bizonyitjuk.
            for var in ucp_unique_variables.iter().filter(|_| !can_recover_value) {
                if let Some(result_from_model) = model.result.get(var) {
                    let assertion = printer
                        .get_assert(
                            result_from_model.name.clone(),
                            result_from_model.value.element.clone(),
                            NodeType::Advice,
                            Operation::Equal,
                        )
                        .context("Failed to generate UCP equality assertion!")?;
                    same_assignments.push(assertion);
                }
            }

            let instance_variables: Vec<String> = variables
                .iter()
                .filter(|var| var.starts_with("I-"))
                .cloned()
                .collect();
            for var in instance_variables {
                if let Some(result_from_model) = model.result.get(&var) {
                    let assertion = printer
                        .get_assert(
                            result_from_model.name.clone(),
                            result_from_model.value.element.clone(),
                            NodeType::Instance,
                            Operation::Equal,
                        )
                        .context("Failed to generate input equality assertion!")?;
                    same_assignments.push(assertion);
                }
            }

            let query_diff = printer
                .get_assert(
                    query_value.name.clone(),
                    query_value.value.element.clone(),
                    NodeType::Advice,
                    Operation::NotEqual,
                )
                .context("Failed to generate query disequality assertion!")?;

            let mut query_formula = String::new();
            for assertion in same_assignments {
                query_formula.push_str(&assertion);
            }
            query_formula.push_str(&query_diff);

            let query_formula = printer.get_and(query_formula);
            printer.write_assert_bool(query_formula, Operation::And);

            let model_with_query = Self::solve_and_get_model_with_timeout(
                SMT_FILE_PATH.to_string(),
                &variables,
                self.smt_timeout_ms,
            );
            printer.write_pop(1);
            let model_with_query =
                model_with_query.context("Failed to solve SMT semantic uniqueness query!")?;

            if matches!(model_with_query.sat, Satisfiability::Unsatisfiable) {
                let value = if can_recover_value {
                    let value = BigInt::from_str_radix(&query_value.value.element, 10)
                        .context("Failed to parse recovered field value!")?;
                    normalize_field_value(value, &prime)
                } else {
                    None
                };
                Ok(SemanticQueryOutput {
                    result: SemanticQueryResult::ProvenUnique,
                    value_unavailable_reason: if include_value && value.is_none() {
                        Some(if can_recover_value {
                            ValueRecoveryFailure::RepresentationLimit
                        } else {
                            ValueRecoveryFailure::PublicContextNotConcrete
                        })
                    } else {
                        None
                    },
                    value,
                    samples: Vec::new(),
                })
            } else {
                let mut answer: SemanticQueryOutput = SemanticQueryResult::NotUnique.into();
                if can_recover_value {
                    for model in [&model, &model_with_query] {
                        if let Some(sample) = model.result.get(&query_variable) {
                            if BigInt::from_str_radix(&sample.value.order, 10)? != prime {
                                return Err(anyhow!(
                                    "Semantic sample belongs to a different field"
                                ));
                            }
                            let value = BigInt::from_str_radix(&sample.value.element, 10)
                                .context("Invalid semantic model sample")?;
                            if let Some(value) = normalize_field_value(value, &prime) {
                                answer.samples.push(value);
                            }
                        }
                    }
                }
                Ok(answer)
            }
        } else {
            Err(anyhow!("Failed to open SMT file!"))
        }
    }

    fn write_ucp_value_domain_assertions(
        printer: &mut Printer<File>,
        value_domains: &[(String, UcpValueDomain)],
        prime: &BigInt,
    ) -> Result<()> {
        for (var, domain) in value_domains {
            match domain {
                UcpValueDomain::Exact(value) => {
                    printer.write_assert(
                        var.clone(),
                        Self::normalize_ucp_field_value(value, prime),
                        NodeType::Advice,
                        Operation::Equal,
                    );
                }
                UcpValueDomain::FiniteSet(values) => {
                    let mut domain_assertion = String::new();
                    for value in values {
                        domain_assertion.push_str(&Self::smt_field_equality(var, value, prime));
                    }
                    printer.write_assert_bool(domain_assertion, Operation::Or);
                }
            }
        }

        Ok(())
    }

    fn smt_field_equality(var: &str, value: &BigInt, prime: &BigInt) -> String {
        format!(
            "( = {} (as ff{} F))",
            var,
            Self::normalize_ucp_field_value(value, prime)
        )
    }

    fn normalize_ucp_field_value(value: &BigInt, prime: &BigInt) -> String {
        let mut normalized = value % prime;
        if normalized.sign() == Sign::Minus {
            normalized += prime;
        }
        normalized.to_string()
    }

    fn analyzer_field_modulus() -> Result<BigInt> {
        #[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
        {
            Self::parse_field_modulus(F::MODULUS)
        }

        #[cfg(feature = "use_pse_v1_halo2_proofs")]
        {
            Self::parse_field_modulus(bn256::fr::MODULUS_STR)
        }
    }

    fn parse_field_modulus(raw_modulus: &str) -> Result<BigInt> {
        if let Some(hex) = raw_modulus.strip_prefix("0x") {
            BigInt::from_str_radix(hex, 16).context("Failed to parse hex field modulus")
        } else {
            BigInt::from_str_radix(raw_modulus, 10).context("Failed to parse decimal field modulus")
        }
    }

    fn ucp_cell_constant_value(&self, cell: &CellId) -> Option<BigInt> {
        match cell.kind {
            CellKind::Fixed => usize::try_from(cell.row)
                .ok()
                .and_then(|row| self.fixed.get(cell.column)?.get(row).cloned()),
            _ => self
                .cell_to_cycle_head
                .get(&cell.to_string())
                .and_then(|head| self.cycle_bigint_value.get(head))
                .cloned(),
        }
    }

    fn ucp_cell_to_smt_variable_name(&self, cell: &CellId) -> Option<String> {
        if matches!(cell.kind, CellKind::Fixed) {
            return None;
        }

        let name = cell.to_string();

        if let Some(cycle_head) = self.cell_to_cycle_head.get(&name) {
            if self.cycle_bigint_value.contains_key(cycle_head) {
                None
            } else {
                Some(cycle_head.clone())
            }
        } else {
            Some(name)
        }
    }
    /**
     * Decomposes an `Expression` into its corresponding SMT-LIB format (`String`) and its type (`NodeType`).
     *
     * # Arguments
     *
     * * `poly` - A reference to an `Expression` instance that is to be decomposed into SMT-LIB v2 format.
     * * `printer` - A mutable reference to a `Printer` instance which is used for writing the decomposed expression.
     * * `region_no` - An integer that represents the region number.
     * * `row_num` - An integer that represents the row number in region.
     * * `es` - A reference to a `HashSet` of Strings representing enabled selectors. These selectors are checked during the decomposition.
     *
     * # Returns
     *
     * A tuple of two elements:
     * * `String` - The SMT-LIB v2 formatted string representation of the decomposed expression.
     * * `NodeType` - The type of the node that the expression corresponds to.
     *
     * # Behavior
     *
     * The function formats a string representation of the expression in SMT-LIB v2 format and identifies its polynomial type as a NodeType.
     *  The function has a recursive behavior in the cases of `Negated`, `Sum`, `Product`,
     * and `Scaled` variants of `Expression`, where it decomposes the nested expressions by calling itself.
     */
    fn decompose_expression(
        poly: &Expression<F>,
        printer: &mut smt::Printer<File>,
        region_begin: usize,
        region_end: usize,
        row_num: i32,
        es: &HashMap<Selector, Vec<usize>>,
        fixed: &Vec<Vec<BigInt>>,
        cell_to_cycle_head: &HashMap<String, String>,
        cycle_bigint_value: &HashMap<String, BigInt>,
        new_variables: &mut HashSet<String>,
        selector_indices: &HashSet<usize>,
    ) -> (String, NodeType, IsZeroExpression) {
        let mut is_zero_expression = IsZeroExpression::NonZero;
        match &poly {
            Expression::Constant(a) => {
                let constant_decimal_value =
                    BigInt::from_str_radix(format!("{:?}", a).strip_prefix("0x").unwrap(), 16)
                        .unwrap();

                if constant_decimal_value.sign() == Sign::NoSign {
                    return (
                        "(as ff0 F)".to_owned(),
                        NodeType::Constant,
                        IsZeroExpression::Zero,
                    );
                } else if constant_decimal_value == BigInt::from(1) {
                    return (
                        "(as ff1 F)".to_owned(),
                        NodeType::Constant,
                        IsZeroExpression::One,
                    );
                }

                let term = format!("(as ff{:?} F)", constant_decimal_value);
                (term, NodeType::Constant, is_zero_expression)
            }
            Expression::Selector(a) => {
                if es
                    .get(a)
                    .is_some_and(|rows| rows.contains(&(region_begin + row_num as usize)))
                {
                    (
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::One,
                    )
                } else {
                    (
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::ZeroSelector,
                    )
                }
            }
            Expression::Fixed(fixed_query) => {
                let col = fixed_query.column_index;
                let row = query_row(
                    region_begin,
                    row_num,
                    fixed_query.rotation,
                    fixed[col].len(),
                );

                if col < fixed.len() && row < fixed[col].len() {
                    let t = &fixed[col][row];
                    let term = format!("(as ff{:?} F)", t);

                    if t.sign() == Sign::NoSign {
                        if selector_indices.contains(&col) {
                            is_zero_expression = IsZeroExpression::ZeroSelector;
                        } else {
                            is_zero_expression = IsZeroExpression::Zero;
                        }
                    } else if *t == BigInt::from(1) {
                        is_zero_expression = IsZeroExpression::One;
                    }

                    (term, NodeType::Fixed, is_zero_expression)
                } else {
                    (
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::Zero,
                    )
                }
            }
            Expression::Advice(advice_query) => {
                let term = format!(
                    "A-{}-{}",
                    advice_query.column_index,
                    query_row(
                        region_begin,
                        row_num,
                        advice_query.rotation,
                        fixed.first().map_or(region_end + 1, Vec::len)
                    )
                );
                let mut t = term.clone();
                let mut t_is_fixed = false;
                if cell_to_cycle_head.contains_key(&term) {
                    if cycle_bigint_value.contains_key(&cell_to_cycle_head[&term]) {
                        t_is_fixed = true;
                        t = format!(
                            "(as ff{:?} F)",
                            cycle_bigint_value[&cell_to_cycle_head[&term]].to_owned()
                        );
                    } else {
                        t = cell_to_cycle_head[&term.clone()].to_string();
                    }
                }
                if !t_is_fixed {
                    new_variables.insert(t.clone());
                }
                (t.to_string(), NodeType::Advice, is_zero_expression)
            }
            Expression::Instance(instance_query) => {
                let term = format!(
                    "I-{}-{}",
                    instance_query.column_index,
                    query_row(
                        region_begin,
                        row_num,
                        instance_query.rotation,
                        fixed.first().map_or(region_end + 1, Vec::len)
                    )
                );
                let mut t = term.clone();
                let mut t_is_fixed = false;
                if cell_to_cycle_head.contains_key(&term) {
                    if cycle_bigint_value.contains_key(&cell_to_cycle_head[&term]) {
                        t_is_fixed = true;
                        t = format!(
                            "(as ff{:?} F)",
                            cycle_bigint_value[&cell_to_cycle_head[&term]].to_owned()
                        );
                    } else {
                        t = cell_to_cycle_head[&term.clone()].to_string();
                    }
                }
                if !t_is_fixed {
                    new_variables.insert(t.clone());
                }
                (t.to_string(), NodeType::Instance, is_zero_expression)
            }
            Expression::Negated(poly) => {
                let (node_str, node_type, is_zero_expression) = Self::decompose_expression(
                    poly,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );
                if matches!(
                    is_zero_expression,
                    IsZeroExpression::ZeroSelector | IsZeroExpression::Zero
                ) {
                    return (
                        "(as ff0 F)".to_owned(),
                        NodeType::Constant,
                        IsZeroExpression::ZeroSelector,
                    );
                }
                let term = if (matches!(node_type.category(), NodeCategory::Variable)
                    || matches!(node_type.category(), NodeCategory::Constant))
                {
                    format!("ff.neg {}", node_str)
                } else {
                    format!("ff.neg ({})", node_str)
                };
                (term, NodeType::Negated, is_zero_expression)
            }
            Expression::Sum(a, b) => {
                let (node_str_left, node_type_left, left_is_zero) = Self::decompose_expression(
                    a,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );
                let (node_str_right, node_type_right, right_is_zero) = Self::decompose_expression(
                    b,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );

                if matches!(
                    left_is_zero,
                    IsZeroExpression::ZeroSelector | IsZeroExpression::Zero
                ) && matches!(
                    right_is_zero,
                    IsZeroExpression::ZeroSelector | IsZeroExpression::Zero
                ) {
                    return (
                        "(as ff0 F)".to_owned(),
                        NodeType::Constant,
                        IsZeroExpression::ZeroSelector,
                    );
                }

                let term = printer.write_term(
                    "add".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
                );
                (term, NodeType::Add, is_zero_expression)
            }
            Expression::Product(a, b) => {
                let (node_str_left, node_type_left, left_is_zero) = Self::decompose_expression(
                    a,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );
                let (node_str_right, node_type_right, right_is_zero) = Self::decompose_expression(
                    b,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );

                if matches!(
                    left_is_zero,
                    IsZeroExpression::ZeroSelector | IsZeroExpression::Zero
                ) || matches!(
                    right_is_zero,
                    IsZeroExpression::ZeroSelector | IsZeroExpression::Zero
                ) {
                    return (
                        "(as ff0 F)".to_owned(),
                        NodeType::Constant,
                        IsZeroExpression::ZeroSelector,
                    );
                } else if matches!(left_is_zero, IsZeroExpression::One)
                    && matches!(right_is_zero, IsZeroExpression::One)
                {
                    return (
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::One,
                    );
                } else if matches!(left_is_zero, IsZeroExpression::One) {
                    return (node_str_right, node_type_right, right_is_zero);
                } else if matches!(right_is_zero, IsZeroExpression::One) {
                    return (node_str_left, node_type_left, left_is_zero);
                }

                let term = printer.write_term(
                    "mul".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
                );
                (term, NodeType::Mult, is_zero_expression)
            }
            Expression::Scaled(_poly, c) => {
                // convering the field element into an expression constant and recurse.
                let (node_str_left, node_type_left, left_is_zero) = Self::decompose_expression(
                    &Expression::Constant(*c),
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );
                let (node_str_right, node_type_right, right_is_zero) = Self::decompose_expression(
                    _poly,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );
                if matches!(
                    left_is_zero,
                    IsZeroExpression::ZeroSelector | IsZeroExpression::Zero
                ) || matches!(
                    right_is_zero,
                    IsZeroExpression::ZeroSelector | IsZeroExpression::Zero
                ) {
                    return (
                        "(as ff0 F)".to_owned(),
                        NodeType::Constant,
                        IsZeroExpression::ZeroSelector,
                    );
                } else if matches!(left_is_zero, IsZeroExpression::One)
                    && matches!(right_is_zero, IsZeroExpression::One)
                {
                    return (
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::One,
                    );
                } else if matches!(left_is_zero, IsZeroExpression::One) {
                    return (node_str_right, node_type_right, right_is_zero);
                } else if matches!(right_is_zero, IsZeroExpression::One) {
                    return (node_str_left, node_type_left, left_is_zero);
                }
                let term = printer.write_term(
                    "mul".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
                );
                (term, NodeType::Scaled, is_zero_expression)
            }
            #[cfg(any(
                feature = "use_pse_halo2_proofs",
                feature = "use_axiom_halo2_proofs",
                feature = "use_scroll_halo2_proofs"
            ))]
            Expression::Challenge(_poly) => ("".to_string(), NodeType::Fixed, is_zero_expression),
        }
    }

    fn decompose_lookup_expression(
        poly: &Expression<F>,
        printer: &mut smt::Printer<File>,
        region_begin: usize,
        region_end: usize,
        row_num: i32,
        es: &HashMap<Selector, Vec<usize>>,
        fixed: &Vec<Vec<BigInt>>,
        cell_to_cycle_head: &HashMap<String, String>,
        new_variables: &mut HashSet<String>,
    ) -> Result<(String, NodeType, String, IsZeroExpression)> {
        let is_zero_expression = IsZeroExpression::NonZero;
        match &poly {
            Expression::Constant(a) => {
                let constant_decimal_value =
                    BigInt::from_str_radix(format!("{:?}", a).strip_prefix("0x").unwrap(), 16)
                        .unwrap();

                if constant_decimal_value.sign() == Sign::NoSign {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Constant,
                        constant_decimal_value.to_string(),
                        IsZeroExpression::Zero,
                    ));
                } else if constant_decimal_value == BigInt::from(1) {
                    return Ok((
                        "(as ff1 F)".to_owned(),
                        NodeType::Constant,
                        constant_decimal_value.to_string(),
                        IsZeroExpression::One,
                    ));
                }

                let term = format!("(as ff{:?} F)", constant_decimal_value);
                Ok((
                    term,
                    NodeType::Constant,
                    constant_decimal_value.to_string(),
                    is_zero_expression,
                ))
            }
            Expression::Selector(a) => {
                if es
                    .get(a)
                    .is_some_and(|rows| rows.contains(&(region_begin + row_num as usize)))
                {
                    Ok((
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        "1".to_owned(),
                        IsZeroExpression::One,
                    ))
                } else {
                    Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::ZeroSelector,
                    ))
                }
            }
            Expression::Fixed(fixed_query) => {
                let col = fixed_query.column_index;
                let row = query_row(
                    region_begin,
                    row_num,
                    fixed_query.rotation,
                    fixed[col].len(),
                );

                let t = &fixed[col][row];
                if t.sign() == Sign::NoSign {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::Zero,
                    ));
                } else if *t == BigInt::from(1) {
                    return Ok((
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        "1".to_owned(),
                        IsZeroExpression::One,
                    ));
                }
                let term = format!("(as ff{:?} F)", t);

                Ok((term, NodeType::Fixed, t.to_string(), is_zero_expression))
            }
            Expression::Advice(advice_query) => {
                let term = format!(
                    "A-{}-{}",
                    advice_query.column_index,
                    query_row(
                        region_begin,
                        row_num,
                        advice_query.rotation,
                        fixed.first().map_or(region_end + 1, Vec::len)
                    )
                );
                let mut t = term.clone();
                if cell_to_cycle_head.contains_key(&term) {
                    t = cell_to_cycle_head[&term.clone()].to_string();
                }

                new_variables.insert(t.clone());
                Ok((
                    t.to_string(),
                    NodeType::Advice,
                    t.to_string(),
                    is_zero_expression,
                ))
            }
            Expression::Instance(instance_query) => {
                let term = format!(
                    "I-{}-{}",
                    instance_query.column_index,
                    query_row(
                        region_begin,
                        row_num,
                        instance_query.rotation,
                        fixed.first().map_or(region_end + 1, Vec::len)
                    )
                );
                let mut t = term.clone();
                if cell_to_cycle_head.contains_key(&term) {
                    t = cell_to_cycle_head[&term.clone()].to_string();
                }
                new_variables.insert(t.clone());
                Ok((
                    t.to_string(),
                    NodeType::Advice,
                    t.to_string(),
                    is_zero_expression,
                ))
            }
            Expression::Negated(poly) => {
                let (node_str, node_type, _, _) = Self::decompose_lookup_expression(
                    poly,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    new_variables,
                )
                .with_context(|| {
                    format!(
                        "Failed to decompose negated within region from row: {} to {}, at row: {}",
                        region_begin, region_end, row_num
                    )
                })?;
                if matches!(is_zero_expression, IsZeroExpression::ZeroSelector) {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        String::from(""),
                        IsZeroExpression::ZeroSelector,
                    ));
                }
                let term = if (matches!(node_type.category(), NodeCategory::Variable)
                    || matches!(node_type.category(), NodeCategory::Constant))
                {
                    format!("ff.neg {}", node_str)
                } else {
                    format!("ff.neg ({})", node_str)
                };
                Ok((
                    term,
                    NodeType::Negated,
                    String::from(""),
                    is_zero_expression,
                ))
            }

            Expression::Sum(a, b) => {
                let (node_str_left, node_type_left, _, left_is_zero) =
                    Self::decompose_lookup_expression(
                        a,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the left side of the Sum expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                let (node_str_right, node_type_right, _, right_is_zero) =
                    Self::decompose_lookup_expression(
                        b,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the right side of the Sum expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;

                if matches!(left_is_zero, IsZeroExpression::ZeroSelector)
                    && matches!(right_is_zero, IsZeroExpression::ZeroSelector)
                {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::ZeroSelector,
                    ));
                }

                let term = printer.write_term(
                    "add".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
                );
                Ok((term, NodeType::Add, String::from(""), is_zero_expression))
            }
            Expression::Product(a, b) => {
                let (node_str_left, node_type_left, variable_left, left_is_zero) =
                    Self::decompose_lookup_expression(
                        a,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the left side of the Product expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                let (node_str_right, node_type_right, variable_right, right_is_zero) =
                    Self::decompose_lookup_expression(
                        b,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the right side of the Product expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                if matches!(node_type_left, NodeType::Invalid) {
                    return Err(anyhow!("Left side of the Product expression evaluated to an invalid type. Check the expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                } else if matches!(node_type_right, NodeType::Invalid) {
                    return Err(anyhow!("Right side of the Product expression evaluated to an invalid type. Check the expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                }

                let mut var = String::from("");
                if variable_left == "1" || variable_right == "1" {
                    if variable_left == "1" {
                        var = variable_right;
                    } else {
                        var = variable_left;
                    }
                }

                if matches!(left_is_zero, IsZeroExpression::ZeroSelector)
                    || matches!(right_is_zero, IsZeroExpression::ZeroSelector)
                {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::ZeroSelector,
                    ));
                } else if matches!(left_is_zero, IsZeroExpression::One)
                    && matches!(right_is_zero, IsZeroExpression::One)
                {
                    return Ok((
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        "1".to_owned(),
                        IsZeroExpression::One,
                    ));
                } else if matches!(left_is_zero, IsZeroExpression::One) {
                    return Ok((node_str_right, node_type_right, var, right_is_zero));
                } else if matches!(right_is_zero, IsZeroExpression::One) {
                    return Ok((node_str_left, node_type_left, var, left_is_zero));
                }

                let term = printer.write_term(
                    "mul".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
                );

                Ok((term, NodeType::Mult, var, is_zero_expression))
            }
            Expression::Scaled(poly, c) => {
                // convering the field element into an expression constant and recurse.
                let (node_str_left, node_type_left, _, left_is_zero) = Self::decompose_lookup_expression(
                    &Expression::Constant(*c),
                    printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the constant part of the Scaled expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                let (node_str_right, node_type_right, _, right_is_zero) =
                    Self::decompose_lookup_expression(
                        poly,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the polynomila part of the Scaled expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                if matches!(left_is_zero, IsZeroExpression::ZeroSelector)
                    || matches!(right_is_zero, IsZeroExpression::ZeroSelector)
                {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::ZeroSelector,
                    ));
                } else if matches!(left_is_zero, IsZeroExpression::One)
                    && matches!(right_is_zero, IsZeroExpression::One)
                {
                    return Ok((
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        String::from(""),
                        IsZeroExpression::One,
                    ));
                } else if matches!(left_is_zero, IsZeroExpression::One) {
                    return Ok((
                        node_str_right,
                        node_type_right,
                        String::from(""),
                        right_is_zero,
                    ));
                } else if matches!(right_is_zero, IsZeroExpression::One) {
                    return Ok((
                        node_str_left,
                        node_type_left,
                        String::from(""),
                        left_is_zero,
                    ));
                }
                let term = printer.write_term(
                    "mul".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
                );
                Ok((term, NodeType::Scaled, String::from(""), is_zero_expression))
            }
            #[cfg(any(
                feature = "use_pse_halo2_proofs",
                feature = "use_axiom_halo2_proofs",
                feature = "use_scroll_halo2_proofs"
            ))]
            Expression::Challenge(_poly) => Err(anyhow!(
                "Challenge expression in lookup expression is invalid."
            )),
        }
    }

    /// Decomposes polynomials and writes assertions using an SMT printer.
    ///
    /// This function iterates over the regions and rows of a layouter and decomposes the polynomials
    /// associated with gates and lookups. It writes assertions using an SMT printer based on the decomposed expressions.
    ///
    pub fn decompose_polynomial(
        &'b mut self,
        printer: &mut smt::Printer<File>,
        analyzer_input: &AnalyzerInput,
    ) -> Result<(), anyhow::Error> {
        //Region annotations do not control gate activity; fixed values do.
        let enabled_selectors = self.enabled_selectors_by_row();
        let region_begin = 0;
        let region_end = self.usable_rows.end + self.cs.blinding_factors();
        for row_num in self.usable_rows.clone() {
            for gate in self.cs.gates.iter() {
                for poly in &gate.polys {
                    let mut new_variables = HashSet::new();
                    let (node_str, node_type, is_zero) = Self::decompose_expression(
                        poly,
                        printer,
                        region_begin,
                        region_end,
                        i32::try_from(row_num).ok().unwrap(),
                        &enabled_selectors,
                        &self.fixed,
                        &self.cell_to_cycle_head,
                        &self.cycle_bigint_value,
                        &mut new_variables,
                        &self.selector_indices,
                    );

                    if !matches!(is_zero, IsZeroExpression::ZeroSelector)
                        && !(matches!(is_zero, IsZeroExpression::Zero)
                            && (matches!(node_type.category(), NodeCategory::Constant)))
                    {
                        let diff: HashSet<String> = new_variables
                            .difference(&self.all_variables)
                            .cloned()
                            .collect();
                        for element in diff {
                            self.all_variables.insert(element.clone());
                            printer.write_var(element.to_string());
                        }

                        if self.validation_subset_assertions.len()
                            < MAX_VALIDATION_SUBSET_ASSERTIONS
                            && Self::validation_affine_degree(poly) <= 1
                        {
                            self.validation_subset_assertions.push(printer.get_assert(
                                node_str.clone(),
                                "0".to_owned(),
                                node_type.clone(),
                                Operation::Equal,
                            )?);
                        }
                        if let Some(store) = &mut self.original_recovery_assertions {
                            if store.has_capacity() {
                                store.retain(
                                    printer.get_assert(
                                        node_str.clone(),
                                        "0".to_owned(),
                                        node_type.clone(),
                                        Operation::Equal,
                                    )?,
                                    new_variables.into_iter(),
                                );
                            }
                        }
                        printer.write_assert(node_str, "0".to_owned(), node_type, Operation::Equal);
                    }
                }
            }
        }
        // Extract all lookups
        if (matches!(analyzer_input.lookup_method, LookupMethod::Uninterpreted)
            || matches!(analyzer_input.lookup_method, LookupMethod::Interpreted))
        {
            // Extract all lookups as uninterpreted functions and stores all lookup structure to be use for post-processing
            self.decompose_lookups_as_function(printer, analyzer_input)?;
        } else {
            // Extract all lookup constraints
            self.decompose_lookups(printer)?;
        }
        Ok(())
    }

    // Selection is an efficiency heuristic only: every retained assertion is copied verbatim from C.
    fn validation_affine_degree(expr: &Expression<F>) -> u8 {
        match expr {
            Expression::Constant(_) | Expression::Fixed(_) | Expression::Selector(_) => 0,
            Expression::Advice(_) | Expression::Instance(_) => 1,
            Expression::Negated(inner) | Expression::Scaled(inner, _) => {
                Self::validation_affine_degree(inner)
            }
            Expression::Sum(left, right) => {
                Self::validation_affine_degree(left).max(Self::validation_affine_degree(right))
            }
            Expression::Product(left, right) => (Self::validation_affine_degree(left)
                + Self::validation_affine_degree(right))
            .min(2),
            #[cfg(any(
                feature = "use_pse_halo2_proofs",
                feature = "use_axiom_halo2_proofs",
                feature = "use_scroll_halo2_proofs"
            ))]
            Expression::Challenge(_) => 2,
        }
    }

    fn enabled_selectors_by_row(&self) -> HashMap<Selector, Vec<usize>> {
        let mut enabled: HashMap<Selector, Vec<usize>> = HashMap::new();
        for region in &self.regions {
            for (selector, rows) in &region.enabled_selectors {
                enabled.entry(*selector).or_default().extend(rows);
            }
        }
        enabled
    }

    #[cfg(any(
        feature = "use_zcash_halo2_proofs",
        feature = "use_pse_halo2_proofs",
        feature = "use_axiom_halo2_proofs",
        feature = "use_pse_v1_halo2_proofs",
    ))]
    // Extracts the lookup constraints and writes assertions using an SMT printer.
    fn decompose_lookups(&mut self, printer: &mut smt::Printer<File>) -> Result<(), anyhow::Error> {
        let enabled_selectors = self.enabled_selectors_by_row();
        let region_begin = 0;
        let region_end = self.usable_rows.end + self.cs.blinding_factors();
        let zero_memberships: Vec<bool> = self
            .cs
            .lookups
            .iter()
            .map(|lookup| {
                let columns: Vec<_> = lookup
                    .table_expressions
                    .iter()
                    .filter_map(|expr| {
                        if let Expression::Fixed(query) = expr {
                            Some(query.column_index)
                        } else {
                            None
                        }
                    })
                    .collect();
                columns.len() == lookup.table_expressions.len()
                    && self.usable_rows.clone().any(|row| {
                        columns
                            .iter()
                            .all(|col| self.fixed[*col][row] == BigInt::from(0))
                    })
            })
            .collect();
        for row_num in self.usable_rows.clone() {
            for (lookup_index, lookup) in self.cs.lookups.iter().enumerate() {
                let mut zero_lookup_expressions = Vec::new();
                let mut cons_str_vec = Vec::new();
                let mut all_zero = true;
                let mut new_variables = HashSet::new();
                for poly in &lookup.input_expressions {
                    let (node_str, node_type, is_zero) = Self::decompose_expression(
                        poly,
                        printer,
                        region_begin,
                        region_end,
                        i32::try_from(row_num).ok().unwrap(),
                        &enabled_selectors,
                        &self.fixed,
                        &self.cell_to_cycle_head,
                        &self.cycle_bigint_value,
                        &mut new_variables,
                        &self.selector_indices,
                    );
                    all_zero &= matches!(
                        is_zero,
                        IsZeroExpression::Zero | IsZeroExpression::ZeroSelector
                    );
                    cons_str_vec.push((node_str, node_type));
                    zero_lookup_expressions.push(true);
                }
                //Zero inputs still require a matching full tuple in the table.
                if all_zero && zero_memberships[lookup_index] {
                    continue;
                }
                if all_zero {
                    new_variables.clear();
                }
                for variable in new_variables
                    .difference(&self.all_variables)
                    .cloned()
                    .collect::<Vec<_>>()
                {
                    self.all_variables.insert(variable.clone());
                    printer.write_var(variable);
                }
                let mut col_indices = Vec::new();
                for col in lookup.table_expressions.clone() {
                    if let Expression::Fixed(fixed_query) = col {
                        col_indices.push(fixed_query.column_index);
                    }
                }

                let big_cons_str = Self::extract_lookup_constraints(
                    self,
                    col_indices,
                    Some(cons_str_vec),
                    printer,
                    Some(zero_lookup_expressions),
                )?;
                if big_cons_str.is_empty() {
                    continue;
                }
                printer.write_assert_bool(big_cons_str, Operation::Or);
            }
        }
        Ok(())
    }
    fn extract_lookup_constraints(
        &self,
        col_indices: Vec<usize>,
        cons_str_vec: Option<Vec<(String, NodeType)>>,
        printer: &mut smt::Printer<File>,
        zero_lookup_expressions: Option<Vec<bool>>,
    ) -> Result<String, anyhow::Error> {
        let mut big_cons_str = String::new();
        let mut big_cons = vec![];

        let rows: BTreeSet<Vec<BigInt>> = self
            .usable_rows
            .clone()
            .map(|row| {
                col_indices
                    .iter()
                    .map(|col| self.fixed[*col][row].clone())
                    .collect()
            })
            .collect();
        for row in rows {
            let mut equalities = vec![];
            let mut eq_str = String::new();
            for col in 0..col_indices.len() {
                if zero_lookup_expressions.as_ref().map_or(false, |z| !z[col]) {
                    continue;
                }
                // Define cons_str outside the match to extend its lifetime
                let default_str = (format!("x_{} ", col), NodeType::Advice);
                let cons_str = match &cons_str_vec {
                    Some(vec) => &vec[col],
                    None => &default_str,
                };

                let t = format!("{:?}", row[col]);
                let mut poly = cons_str.0.clone();
                if matches!(cons_str.1.category(), NodeCategory::Polynomial) {
                    poly = format!("({})", cons_str.0.clone());
                }
                let sa = printer
                    .get_assert(poly, t, NodeType::Advice, Operation::Equal)
                    .context("Failed to generate assert!")?;
                equalities.push(sa);
            }

            for var in equalities.iter() {
                eq_str.push_str(var);
            }
            if eq_str.is_empty() {
                continue;
            }
            let and_eqs = printer.get_and(eq_str);
            if and_eqs.is_empty() {
                continue;
            }
            big_cons.push(and_eqs);
        }
        for var in big_cons.iter() {
            big_cons_str.push_str(var);
        }
        Ok(big_cons_str)
    }
    fn extract_lookup_constraints_as_function(
        &self,
        col_indices: Vec<usize>,
        cons_str_vec: Option<Vec<String>>,
        printer: &mut smt::Printer<File>,
        row_set: HashSet<Vec<BigInt>>,
    ) -> Result<(String, bool, usize), anyhow::Error> {
        let mut big_cons_str = String::new();
        let mut big_cons = vec![];

        //if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted) {
        // First check if there is an equivalent lookup table in the lookup_tables.
        // If there is, we can use the existing lookup function.
        // Otherwise, we will generate a new lookup function.
        let mut index = 0;
        let mut matched_lookup_exists = false;
        if self.lookup_tables.len() > 0 {
            (matched_lookup_exists, index) = self.match_equivalent_lookup_tables(row_set.clone());
        }
        if matched_lookup_exists {
            Ok((self.lookup_tables[index].function_body.clone(), true, index))
        } else {
            for row in row_set.iter() {
                let mut equalities = vec![];
                let mut eq_str = String::new();
                for col in 0..col_indices.len() {
                    // Define cons_str outside the match to extend its lifetime
                    let default_str = format!("x_{} ", col);
                    let cons_str = match &cons_str_vec {
                        Some(vec) => &vec[col],
                        None => &default_str,
                    };

                    let t = format!("{:?}", row[col]);
                    let sa = printer
                        .get_assert(cons_str.clone(), t, NodeType::Advice, Operation::Equal)
                        .context("Failed to generate assert!")?;
                    equalities.push(sa);
                }

                for var in equalities.iter() {
                    eq_str.push_str(var);
                }
                if eq_str.is_empty() {
                    continue;
                }
                let and_eqs = printer.get_and(eq_str);
                if and_eqs.is_empty() {
                    continue;
                }
                big_cons.push(and_eqs);
            }

            for var in big_cons.iter() {
                big_cons_str.push_str(var);
            }
            Ok((big_cons_str, false, 0))
        }
    }
    // Extracts the lookup dependant cells and writes assertions of an uninterpreted function using an SMT printer.
    // Also extract the list of all lookup dependant cells and their corresponding lookup mappings. These data will be used for checking if a under-constrained circuit is false positive.
    #[cfg(any(
        feature = "use_zcash_halo2_proofs",
        feature = "use_pse_halo2_proofs",
        feature = "use_axiom_halo2_proofs",
        feature = "use_pse_v1_halo2_proofs",
        feature = "use_scroll_halo2_proofs",
    ))]
    fn decompose_lookups_as_function(
        &mut self,
        printer: &mut smt::Printer<File>,
        analyzer_input: &AnalyzerInput,
    ) -> Result<(), anyhow::Error> {
        self.extract_lookups(printer, None)?;
        let mut lookup_func_map = HashMap::new();
        for region in &self.regions {
            if self.selectors.is_empty() || !region.enabled_selectors.is_empty() {
                let (region_begin, region_end) = region.rows.unwrap();
                for row_num in 0..region_end - region_begin + 1 {
                    let mut lookup_index = 0;
                    #[cfg(any(
                        feature = "use_zcash_halo2_proofs",
                        feature = "use_pse_halo2_proofs",
                        feature = "use_axiom_halo2_proofs",
                        feature = "use_pse_v1_halo2_proofs",
                    ))]
                    let lookups = self.cs.lookups.clone();
                    #[cfg(any(feature = "use_scroll_halo2_proofs",))]
                    let lookups = self.cs.lookups_map.clone();
                    for lookup in lookups.iter() {
                        let mut function_name = String::new();
                        let mut function_body = String::new();
                        let lookup_table = &self.lookup_tables[lookup_index];

                        if lookup_table.matched_lookup_exists {
                            function_name = self.lookup_tables[lookup_table.match_index]
                                .function_name
                                .clone();
                            function_body = self.lookup_tables[lookup_table.match_index]
                                .function_body
                                .clone();
                        } else {
                            function_name = lookup_table.function_name.clone();
                            function_body = lookup_table.function_body.clone();
                        }

                        let mut cons_str_vec = Vec::new();
                        let mut lookup_arg_cells = Vec::new();
                        // Decompose the lookup input expressions and store the result in cons_str_vec.
                        #[cfg(any(
                            feature = "use_zcash_halo2_proofs",
                            feature = "use_pse_halo2_proofs",
                            feature = "use_axiom_halo2_proofs",
                            feature = "use_pse_v1_halo2_proofs",
                        ))]
                        for poly in &lookup.input_expressions {
                            let mut new_variables = HashSet::new();
                            // Decompose the lookup input expressions and return the SMT compatible decomposed expression and the variable name.
                            let (node_str, _, var, is_zero) = Self::decompose_lookup_expression(
                                poly,
                                printer,
                                region_begin,
                                region_end,
                                i32::try_from(row_num).ok().unwrap(),
                                &region.enabled_selectors,
                                &self.fixed,
                                &self.cell_to_cycle_head,
                                &mut new_variables,
                            )
                        .with_context(|| format!("Failed to decompose lookup input expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                            if !matches!(is_zero, IsZeroExpression::ZeroSelector) {
                                let diff: HashSet<String> = new_variables
                                    .difference(&self.all_variables)
                                    .cloned()
                                    .collect();
                                for element in diff {
                                    self.all_variables.insert(element.clone());
                                    printer.write_var(element.to_string());
                                }
                                cons_str_vec.push(node_str);
                                if !var.is_empty() {
                                    lookup_arg_cells.push(var);
                                }
                            }
                        }
                        #[cfg(any(feature = "use_scroll_halo2_proofs",))]
                        for polys in &lookup.1.inputs {
                            for poly in polys {
                                let mut new_variables = HashSet::new();
                                let (node_str, _, var, is_zero) =
                                    Self::decompose_lookup_expression(
                                        poly,
                                        printer,
                                        region_begin,
                                        region_end,
                                        i32::try_from(row_num).ok().unwrap(),
                                        &region.enabled_selectors,
                                        &self.fixed,
                                        &self.cell_to_cycle_head,
                                        &mut new_variables,
                                    )
                                    .with_context(|| format!("Failed to decompose lookup input expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                                if !matches!(is_zero, IsZeroExpression::ZeroSelector) {
                                    let diff: HashSet<String> = new_variables
                                        .difference(&self.all_variables)
                                        .cloned()
                                        .collect();
                                    for element in diff {
                                        self.all_variables.insert(element.clone());
                                        printer.write_var(element.to_string());
                                    }
                                    cons_str_vec.push(node_str);
                                    if !var.is_empty() {
                                        lookup_arg_cells.push(var);
                                    }
                                }
                            }
                        }
                        if !cons_str_vec.is_empty() {
                            let col_indices =
                                self.lookup_tables[lookup_index].column_indices.clone();

                            let mut function_input = String::new();

                            let mut lookup_mapping = HashMap::new();
                            let mut input_index = 0;
                            // Using decomposed lookup input expressions and column indexes of the lookup table, we can have the whole structure of each lookup as elements of lookup_mappings

                            for (index, var) in lookup_arg_cells.iter().enumerate() {
                                if var.is_empty() {
                                    continue;
                                }
                                if let Some(col_index) = col_indices.get(index).cloned() {
                                    // Keeping track of in the current lookup, which cell is mapped to which column in the lookup table.
                                    lookup_mapping.insert(var.clone(), col_index);
                                    // Concatenate function_input with format!("(x_{} ", col_index)
                                    if matches!(
                                        analyzer_input.lookup_method,
                                        LookupMethod::Interpreted
                                    ) {
                                        function_input.push_str(&format!("(x_{} F)", input_index));
                                        input_index += 1;
                                    }
                                }
                            }
                            if !lookup_mapping.is_empty() {
                                self.lookup_mappings.push(lookup_mapping.clone());
                            }

                            if !lookup_mapping.is_empty() {
                                if !lookup_func_map.contains_key(&lookup_index) {
                                    lookup_func_map.insert(lookup_index, true);
                                    if matches!(
                                        analyzer_input.lookup_method,
                                        LookupMethod::Interpreted
                                    ) {
                                        if !self.lookup_tables[lookup_index].matched_lookup_exists {
                                            printer.write_define_fn(
                                                function_name.clone(),
                                                function_input,
                                                "Bool".to_owned(),
                                                function_body,
                                            );
                                        }
                                    } else {
                                        printer.write_declare_fn(
                                            function_name.clone(),
                                            "F".to_owned(),
                                            "Bool".to_owned(),
                                        );
                                    }
                                }
                                if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted)
                                {
                                    // Concatenate all lookup input expressions and write assertions of an interpreted function using an SMT printer.
                                    let cons_str = lookup_arg_cells
                                        .iter()
                                        .fold(String::new(), |acc, x| acc + x + " ");
                                    let cons_str = cons_str.trim();
                                    printer.write_assert_boolean_func(
                                        function_name.clone(),
                                        cons_str.to_owned(),
                                    );
                                } else {
                                    for cons_str in cons_str_vec.iter() {
                                        printer.write_assert_boolean_func(
                                            function_name.clone(),
                                            format!("{}", cons_str).to_owned(),
                                        );
                                    }
                                }
                            }
                        }
                        lookup_index += 1;
                    }
                }
            }
        }
        Ok(())
    }

    #[cfg(any(feature = "use_scroll_halo2_proofs"))]
    fn decompose_lookups(&mut self, printer: &mut smt::Printer<File>) -> Result<(), anyhow::Error> {
        for region in &self.regions {
            if self.selectors.is_empty() || !region.enabled_selectors.is_empty() {
                let (region_begin, region_end) = region.rows.unwrap();
                for row_num in 0..region_end - region_begin + 1 {
                    for lookup in &self.cs.lookups_map {
                        let mut zero_lookup_expressions = Vec::new();
                        let mut cons_str_vec = Vec::new();
                        for polys in &lookup.1.inputs {
                            for poly in polys {
                                let mut new_variables = HashSet::new();
                                let (node_str, node_type, is_zero) = Self::decompose_expression(
                                    &poly,
                                    printer,
                                    region_begin,
                                    region_end,
                                    i32::try_from(row_num).ok().unwrap(),
                                    &region.enabled_selectors,
                                    &self.fixed,
                                    &self.cell_to_cycle_head,
                                    &self.cycle_bigint_value,
                                    &mut new_variables,
                                    &self.selector_indices,
                                );
                                if !matches!(is_zero, IsZeroExpression::ZeroSelector) {
                                    let diff: HashSet<String> = new_variables
                                        .difference(&self.all_variables)
                                        .cloned()
                                        .collect();
                                    for element in diff {
                                        self.all_variables.insert(element.clone());
                                        printer.write_var(element.to_string());
                                    }
                                    cons_str_vec.push((node_str.clone(), node_type));
                                    zero_lookup_expressions.push(true);
                                } else {
                                    zero_lookup_expressions.push(false);
                                }
                            }
                        }
                        let mut col_indices = Vec::new();
                        for col in lookup.1.table.clone() {
                            if let Expression::Fixed(fixed_query) = col {
                                col_indices.push(fixed_query.column_index);
                            }
                        }
                        let big_cons_str = Self::extract_lookup_constraints(
                            self,
                            col_indices,
                            Some(cons_str_vec),
                            printer,
                            Some(zero_lookup_expressions),
                        )?;
                        if big_cons_str.is_empty() {
                            continue;
                        }

                        printer.write_assert_bool(big_cons_str, Operation::Or);
                    }
                }
            }
        }
        Ok(())
    }
    /// Checks the uniqueness inputs and returns the analysis result.
    ///
    /// This function checks the uniqueness by solving SMT formulas with various assignments
    /// and constraints. It iterates over the variables and applies different rules based on the verification method
    /// specified in the `analyzer_input`. The function writes assertions using an SMT printer and returns the
    /// analysis result as `AnalyzerOutputStatus`.
    ///
    pub fn uniqueness_assertion(
        &mut self,
        analyzer_input: &AnalyzerInput,
    ) -> Result<AnalyzerOutputStatus> {
        // Legacy search can retain model exclusions; it is not a fresh unobserved context.
        self.query_context_written = true;
        let ucp_unique_variables = self.ucp_unique_variables.clone();

        if let Some(smt_file) = self.smt_file.as_mut() {
            let mut printer = Printer::new(smt_file);
            let mut result: AnalyzerOutputStatus = AnalyzerOutputStatus::NotUnderconstrainedLocal;
            let mut variables: HashSet<String> = HashSet::new();
            for variable in &self.all_variables {
                variables.insert(variable.clone());
            }

            let mut max_iterations: u128 = 1;

            // Determine the verification method and configure the analysis accordingly.
            match analyzer_input.verification_method {
                // For specific public input, directly write assertions for each variable.
                VerificationMethod::Specific => {
                    let prime = Self::analyzer_field_modulus()?;
                    for var in self.instance_cells.iter() {
                        // Declare the variables in the SMT formula.
                        if !self.all_variables.contains(&var.0.to_owned()) {
                            self.all_variables.insert(var.0.clone());
                            printer.write_var(var.0.to_owned());
                        }
                        // Write an assertion that each veriables equals the given value.
                        printer.write_assert(
                            var.0.clone(),
                            Self::normalize_ucp_field_value(var.1, &prime),
                            NodeType::Instance,
                            Operation::Equal,
                        );
                    }
                }
                // For random verification, set the number of iterations as specified.
                VerificationMethod::Random => {
                    max_iterations = analyzer_input.verification_input.iterations;
                }
                VerificationMethod::None => {}
            }
            let model = Self::solve_and_get_model(SMT_FILE_PATH.to_string(), &variables)
                .context("Failed to solve and get model!")?;
            // With uninterpreted function, the model might be invalid due to the lookup constraints. We will ignore these models.
            let mut valid_model_lookeded_up = false;
            if matches!(model.sat, Satisfiability::Unsatisfiable) {
                result = AnalyzerOutputStatus::Overconstrained;
                return Ok(result); // We can just break here.
            }
            let mut uc_lookup_dependency_fp = false;
            let mut uc_lookup_dependency: bool = false;
            for i in 1..=max_iterations {
                // Attempt to solve the SMT problem and obtain a model.
                let model = Self::solve_and_get_model(SMT_FILE_PATH.to_string(), &variables)
                    .context("Failed to solve and get model!")?;
                if matches!(model.sat, Satisfiability::Unsatisfiable) {
                    result = AnalyzerOutputStatus::NotUnderconstrained;
                    return Ok(result); // We can just break here.
                }
                // No need to do the lookup as they are already constrained in SMT solver where uninterpreted functions are not used for lookups.
                if !matches!(analyzer_input.lookup_method, LookupMethod::Uninterpreted) {
                    valid_model_lookeded_up = true;
                }
                // if using uninterpreted function, we need to check if the model is valid by performing the lookup.
                else {
                    uc_lookup_dependency = false;
                    // Lookup search to make sure all values in the model are valid.
                    let num_of_lookup_mappings = self.lookup_mappings.clone().len();
                    for index in 0..num_of_lookup_mappings {
                        // Perform the lookup
                        let lookup_sucessful =
                            Self::lookup(&model, &self.lookup_mappings[index], self.fixed.clone());

                        if lookup_sucessful {
                            valid_model_lookeded_up = true;
                        }
                    }
                }
                // If the model is not valid, we ignore it and continue to the next iteration.
                if valid_model_lookeded_up {
                    info!("Model {} to be checked:", i);
                    for r in &model.result {
                        info!("{} : {}", r.1.name, r.1.value.element)
                    }
                    // Imitate the creation of a new solver by utilizing the stack functionality of solver
                    printer.write_push(1);

                    //*** To check the model is under-constrained we need to:
                    //      1. Fix the public input
                    //      2. Change the other vars
                    //      3. add these rules to the current solver and,
                    //      4. find a model that satisfies these rules

                    let mut same_assignments = vec![];
                    let mut diff_assignments = vec![];
                    for var in variables.iter() {
                        // The second condition is needed because the following constraints would've been added already to the solver in the beginning.
                        // It is not strictly necessary, but there is no point in adding redundant constraints to the solver.
                        if ucp_unique_variables.contains(var)
                            || (self.instance_cells.contains_key(var)
                                && !matches!(
                                    analyzer_input.verification_method,
                                    VerificationMethod::Specific
                                ))
                        {
                            // 1. Fix the public input and every variable that UCP has already proven unique.
                            let result_from_model = &model.result[var];
                            let sa = printer
                                .get_assert(
                                    result_from_model.name.clone(),
                                    result_from_model.value.element.clone(),
                                    NodeType::Instance,
                                    Operation::Equal,
                                )
                                .context("Failled to generate assert!")?;
                            same_assignments.push(sa);
                        } else {
                            //2. Change the other vars
                            let result_from_model = &model.result[var];
                            let sa = printer
                                .get_assert(
                                    result_from_model.name.clone(),
                                    result_from_model.value.element.clone(),
                                    NodeType::Advice,
                                    Operation::NotEqual,
                                )
                                .context("Failled to generate assert!")?;
                            diff_assignments.push(sa);
                        }
                    }

                    let mut same_str = "".to_owned();
                    for var in same_assignments.iter() {
                        same_str.push_str(var);
                    }
                    let mut diff_str = "".to_owned();
                    for var in diff_assignments.iter() {
                        diff_str.push_str(var);
                    }

                    // 3. add these rules to the current solver,
                    let or_diff_assignments = printer.get_or(diff_str);
                    same_str.push_str(&or_diff_assignments);
                    let and_all = printer.get_and(same_str);
                    printer.write_assert_bool(and_all, Operation::And);

                    // 4. find a model that satisfies these rules
                    let model_with_constraint =
                        Self::solve_and_get_model(SMT_FILE_PATH.to_string(), &variables)
                            .context("Failed to solve and get model!")?;

                    // If using uninterpreted function, we need to check if the model is valid by performing the lookup.
                    if matches!(analyzer_input.lookup_method, LookupMethod::Uninterpreted) {
                        info!("Equivalent model for the same public input!(No Lookup Constraint):");
                        for r in &model_with_constraint.result {
                            info!("{} : {}", r.1.name, r.1.value.element)
                        }
                        uc_lookup_dependency = false;
                        let num_of_lookup_mappings = self.lookup_mappings.clone().len();
                        for index in 0..num_of_lookup_mappings {
                            // Lookup search to make sure all values in the model are valid.
                            let lookup_sucessful = Self::lookup(
                                &model_with_constraint,
                                &self.lookup_mappings[index],
                                self.fixed.clone(),
                            );
                            // if the lookup is not successful, the model found is not valid and the under-constrained flag is a false positive, still we can't say if the circuit is under-constrained or not.
                            if !lookup_sucessful {
                                uc_lookup_dependency = true;
                                uc_lookup_dependency_fp = true;
                                if (matches!(
                                    analyzer_input.verification_method,
                                    VerificationMethod::Specific
                                ) || (matches!(
                                    analyzer_input.verification_method,
                                    VerificationMethod::Random
                                ) && i == max_iterations))
                                {
                                    info!("Lookup unsuccessful! Probably a false positive!");
                                    result = AnalyzerOutputStatus::NotUnderconstrainedLocalUninterpretedLookups;
                                    return Ok(result);
                                }
                            }
                        }
                    }
                    if (matches!(model_with_constraint.sat, Satisfiability::Satisfiable)
                        && !uc_lookup_dependency)
                    {
                        info!("Equivalent model for the same public input:");
                        for r in &model_with_constraint.result {
                            info!("{} : {}", r.1.name, r.1.value.element)
                        }
                        result = AnalyzerOutputStatus::Underconstrained;
                        return Ok(result);
                    } else {
                        info!("There is no equivalent model with the same public input to prove model {} is under-constrained!", i);
                    }
                    printer.write_pop(1);
                }

                // If no model found, add some rules to the initial solver to make sure does not generate the same model again
                let mut negated_model_variable_assignments = vec![];
                for res in &model.result {
                    if self.instance_cells.contains_key(&res.1.name) {
                        let sa = printer
                            .get_assert(
                                res.1.name.clone(),
                                res.1.value.element.clone(),
                                NodeType::Instance,
                                Operation::NotEqual,
                            )
                            .context("Failled to generate assert!")?;
                        negated_model_variable_assignments.push(sa);
                    }
                }
                let mut neg_model = "".to_owned();

                if negated_model_variable_assignments.is_empty() {
                    continue;
                }
                for var in negated_model_variable_assignments.iter() {
                    neg_model.push_str(var);
                }
                printer.write_assert_bool(neg_model, Operation::Or);
            }
            if uc_lookup_dependency_fp
                && matches!(result, AnalyzerOutputStatus::NotUnderconstrainedLocal)
            {
                result = AnalyzerOutputStatus::NotUnderconstrainedLocalUninterpretedLookups;
            }
            Ok(result)
        } else {
            Err(anyhow!("Failed to open SMT file!"))
        }
    }
    /// Generates a copy path for the SMT file.
    ///
    /// This function takes the original SMT file path as input and generates a copy path
    /// for the SMT file. The copy path is constructed by appending "_temp.smt2" to the
    /// original file's stem (i.e., file name without extension), and placing it in the
    /// "src/output/" directory. The function then creates a copy of the original file
    /// at the generated copy path.
    ///
    pub fn generate_copy_path(smt_file_path: String) -> Result<String> {
        let smt_path_clone = smt_file_path.clone();
        let smt_path_obj = Path::new(&smt_path_clone);
        let smt_file_stem = smt_path_obj.file_stem().unwrap();
        let smt_file_copy_path = format!(
            "{}{}{}",
            "src/output/",
            smt_file_stem.to_str().unwrap(),
            "_temp.smt2"
        );
        fs::copy(smt_file_path, smt_file_copy_path.clone()).context("Failed to copy file!")?;
        Ok(smt_file_copy_path)
    }
    // Solves the SMT formula in the specified file and retrieves the model result.
    ///
    /// This function solves the SMT formula in the given `smt_file_path` by executing the CVC5 solver.
    /// It appends the necessary commands to the SMT file for checking satisfiability and retrieving values
    /// for the specified variables. The function then runs the CVC5 solver and captures its output.
    /// The output is parsed to extract the model result, which is returned as a `ModelResult`.
    ///
    pub fn solve_and_get_model(
        smt_file_path: String,
        variables: &HashSet<String>,
    ) -> Result<ModelResult> {
        Self::solve_and_get_model_with_timeout(smt_file_path, variables, None)
    }

    pub(crate) fn resolve_smt_timeout_ms(explicit: Option<u64>) -> Result<Option<u64>> {
        let milliseconds = match explicit {
            Some(value) => Some(value),
            None => std::env::var_os("HALO2_ANALYZER_SMT_TIMEOUT_MS")
                .map(|raw| {
                    raw.to_str()
                        .context("SMT timeout must be valid text")?
                        .parse::<u64>()
                        .context("SMT timeout must be a positive integer in milliseconds")
                })
                .transpose()?,
        };
        if milliseconds == Some(0) {
            return Err(anyhow!("SMT timeout must be greater than zero"));
        }
        Ok(milliseconds)
    }

    fn solve_and_get_model_with_timeout(
        smt_file_path: String,
        variables: &HashSet<String>,
        timeout_ms: Option<u64>,
    ) -> Result<ModelResult> {
        let smt_file_copy_path =
            Self::generate_copy_path(smt_file_path).context("Failed to generate copy path!")?;
        let mut smt_file_copy = OpenOptions::new()
            .append(true)
            .open(smt_file_copy_path.clone())
            .expect("cannot open file");
        let mut copy_printer = Printer::new(&mut smt_file_copy);

        // Add (check-sat) (get-value var) ... here.
        copy_printer.write_end();
        for var in variables.iter() {
            copy_printer.write_get_value(var.clone());
        }
        let mut command = Command::new("cvc5");
        let timeout_ms = Self::resolve_smt_timeout_ms(timeout_ms)?;
        //Optional per-query budget; unknown stays an error, never a successful proof.
        if let Some(milliseconds) = timeout_ms {
            command.arg(format!("--tlimit-per={}", milliseconds));
        }
        command.arg("--output=incomplete").arg(smt_file_copy_path);
        let term = crate::smt_solver::process::run(
            command,
            timeout_ms.map(std::time::Duration::from_millis),
        )
        .context("Failed to execute cvc5")?;
        let output_string = String::from_utf8_lossy(&term.stdout);

        smt_parser::extract_model_response(output_string.to_string())
            .context("Failed to parse smt result!")
    }

    fn lookup(
        model_with_constraint: &ModelResult,
        lookup_mapping: &HashMap<String, usize>,
        fixed: Vec<Vec<BigInt>>,
    ) -> bool {
        let variables: Vec<_> = model_with_constraint
            .result
            .iter()
            .filter_map(|(key, var)| {
                if let Some(&col_index) = lookup_mapping.get(key) {
                    Some((col_index, var))
                } else {
                    None
                }
            })
            .collect();

        'outer: for (_, row) in fixed.iter().enumerate() {
            for &(column_index, variable) in &variables {
                if let Some(cell) = row.get(column_index) {
                    let t = format!("{:?}", cell);

                    if t != variable.value.element {
                        continue 'outer;
                    }
                } else {
                    continue 'outer; // Either Unassigned, Poison, or column_index out of bounds
                }
            }
            return true;
        }
        // No row matched all conditions
        false
    }

    fn have_same_rows(matrix1: Vec<Vec<BigInt>>, matrix2: Vec<Vec<BigInt>>) -> bool {
        if matrix1.len() != matrix2.len() {
            return false;
        }
        let num_columns = matrix1[0].len();
        let num_rows = matrix1.len();

        // Transform matrices into sets of column tuples
        let mut set1: HashSet<Vec<BigInt>> = HashSet::new();
        let mut set2: HashSet<Vec<BigInt>> = HashSet::new();

        for col_index in 0..num_columns {
            let mut col_tuple1 = Vec::with_capacity(num_rows);

            let mut col_tuple2 = Vec::with_capacity(num_rows);

            for row_index in 0..num_rows {
                col_tuple1.push(matrix1[row_index][col_index].clone());
                col_tuple2.push(matrix2[row_index][col_index].clone());
            }

            set1.insert(col_tuple1);
            set2.insert(col_tuple2);
        }
        set1 == set2
    }

    fn match_equivalent_lookup_tables(
        &self,
        new_lookup_table: HashSet<Vec<BigInt>>,
    ) -> (bool, usize) {
        for (index, existing_table) in self.lookup_tables.iter().enumerate() {
            let result = existing_table.row_set == new_lookup_table;

            if result {
                return (true, index); // Match found, return true with the index of the existing table
            }
        }

        (false, 0) // No match found, return false with a default index
    }

    fn extract_lookup_columns(&self, col_indices: &[usize]) -> HashSet<Vec<BigInt>> {
        let matrix: Vec<Vec<BigInt>> = col_indices
            .iter()
            .filter_map(|&index| self.fixed.get(index).cloned())
            .collect();
        let num_columns = matrix[0].len();
        let num_rows: usize = matrix.len();

        // Transform matrices into sets of column tuples
        let mut set: HashSet<Vec<BigInt>> = HashSet::new();

        for col_index in 0..num_columns {
            let mut col_tuple = Vec::with_capacity(num_rows);

            for row_index in 0..num_rows {
                col_tuple.push(matrix[row_index][col_index].clone());
            }

            set.insert(col_tuple);
        }
        set
    }

    /// Dispatches the analysis based on the specified analyzer type.
    ///
    /// This function takes an `AnalyzerType` enum and performs the corresponding analysis
    /// based on the type. The supported analyzer types include:
    ///
    /// - `UnusedGates`: Analyzes and identifies unused custom gates in the circuit.
    /// - `UnconstrainedCells`: Analyzes and identifies cells with unconstrained values in the circuit.
    /// - `UnusedColumns`: Analyzes and identifies unused columns in the circuit.
    /// - `UnderconstrainedCircuit`: Analyzes the circuit for underconstrained properties by
    ///   retrieving user input for specific instance columns and conducting analysis.
    ///
    /// The function performs the analysis and updates the internal state accordingly.
    ///
    pub fn dispatch_analysis(
        &mut self,
        analyzer_input: &mut AnalyzerInput,
    ) -> Result<AnalyzerOutput> {
        match self.analysis_type {
            AnalyzerType::UnusedGates => self.analyze_unused_custom_gates(),
            AnalyzerType::UnconstrainedCells => self.analyze_unconstrained_cells(),
            AnalyzerType::UnusedColumns => self.analyze_unused_columns(),
            AnalyzerType::UnderconstrainedCircuit => self.analyze_underconstrained(analyzer_input),
        }
    }
}

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod validation_subset_tests {
    use super::*;

    fn search_domain_context() -> (Analyzer<Fr>, OriginalPrivateQueryContext) {
        use crate::io::analyzer_io_type::VerificationInput;
        use crate::sample_circuits::zcash::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit;
        let input = AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput::new([("I-0-0".to_owned(), 3)], 1),
            lookup_method: LookupMethod::InlineConstraints,
        };
        let mut analyzer = Analyzer::<Fr>::new_with_original_subset_capture(
            &TwoBitDecompCircuit::<Fr>::default(),
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
            true,
        )
        .unwrap();
        let original = analyzer
            .original_private_query_context(
                &input,
                &[
                    CellId::advice(0, 0),
                    CellId::advice(1, 0),
                    CellId::advice(2, 0),
                    CellId::instance(0, 0),
                ],
            )
            .unwrap();
        (analyzer, original)
    }

    #[test]
    fn candidate_sat_models_share_projections_and_unsat_models_share_nothing() {
        let (_, mut original) = search_domain_context();
        let first = CellId::advice(0, 0);
        let second = CellId::advice(1, 0);
        let packed = CellId::advice(2, 0);
        let alias = CellId::advice(7, 0);
        original
            .expressions
            .insert(alias.clone(), original.expressions[&first].clone());
        let cells = BTreeSet::from([first.clone(), second.clone(), packed.clone(), alias.clone()]);
        let before = crate::smt_solver::process::invocation_count();
        let sat = original
            .query_candidate_with_search_facts::<Fr>(
                &first,
                &UcpValueDomain::exact(1.into()),
                Some(2_000),
                &PrivateSearchFacts::default(),
                &cells,
            )
            .unwrap();
        assert_eq!(crate::smt_solver::process::invocation_count() - before, 1);
        assert_eq!(sat.sat, Satisfiability::Satisfiable);
        assert_eq!(sat.samples[&first], 1.into());
        assert_eq!(sat.samples[&second], 1.into());
        assert_eq!(sat.samples[&packed], 3.into());
        assert_eq!(sat.samples[&alias], sat.samples[&first]);
        let unsat = original
            .query_candidate_with_search_facts::<Fr>(
                &first,
                &UcpValueDomain::exact(0.into()),
                Some(2_000),
                &PrivateSearchFacts::default(),
                &cells,
            )
            .unwrap();
        assert_eq!(unsat.sat, Satisfiability::Unsatisfiable);
        assert!(unsat.samples.is_empty());
    }

    #[test]
    fn shared_model_projections_reject_missing_values_and_wrong_fields() {
        let (_, original) = search_domain_context();
        let cell = CellId::advice(0, 0);
        let cells = BTreeSet::from([cell.clone()]);
        let empty = ModelResult {
            sat: Satisfiability::Satisfiable,
            result: HashMap::new(),
        };
        assert!(original.project_feasible_model(&empty, &cells).is_err());
        let wrong_field = smt_parser::extract_model_response(format!(
            "sat\n(({} #f1m7))\n",
            original.expressions[&cell]
        ))
        .unwrap();
        assert!(original
            .project_feasible_model(&wrong_field, &cells)
            .is_err());
    }

    #[test]
    fn search_domains_use_covering_sets_without_completeness_or_target_assumptions() {
        let (mut analyzer, original) = search_domain_context();
        let snapshot = original.smt.clone();
        let first = CellId::advice(0, 0);
        let second = CellId::advice(1, 0);
        let packed = CellId::advice(2, 0);
        let public = CellId::instance(0, 0);
        let first_name = &original.expressions[&first];
        let mut values = UcpValueFacts::new();
        values.mark_domain(
            first.clone(),
            UcpValueDomain::finite_set([1.into(), 2.into(), &original.prime + 1]).unwrap(),
        );
        values.mark_domain(
            second.clone(),
            UcpValueDomain::finite_set((0..=MAX_SEARCH_DOMAIN_SIZE).map(BigInt::from)).unwrap(),
        );
        assert!(!values.domain_is_complete(&first));
        let before = values.clone();
        let facts = original.search_facts(&analyzer, &values).unwrap();
        assert_eq!(facts.domains.len(), 1);
        assert_eq!(
            facts.domains[first_name],
            BTreeSet::from([1.into(), 2.into()])
        );
        assert_eq!(values, before);
        let expected = format!(
            "(or {} {})",
            Analyzer::<Fr>::smt_field_equality(first_name, &1.into(), &original.prime),
            Analyzer::<Fr>::smt_field_equality(first_name, &2.into(), &original.prime),
        );
        assert_eq!(
            original
                .check_candidate_with_search_facts::<Fr>(
                    &second,
                    &UcpValueDomain::exact(1.into()),
                    Some(2_000),
                    &facts
                )
                .unwrap(),
            Satisfiability::Satisfiable
        );
        let query = fs::read_to_string("src/output/private_domain_refinement.smt2").unwrap();
        assert!(query.starts_with(&snapshot));
        assert!(query[snapshot.len()..].contains(&expected));
        assert_eq!(
            original
                .query_unseen_value_with_search_facts::<Fr>(
                    &second,
                    &BTreeSet::new(),
                    Some(2_000),
                    &facts
                )
                .unwrap(),
            Some(1.into())
        );
        let query = fs::read_to_string("src/output/private_domain_discovery.smt2").unwrap();
        assert!(query[snapshot.len()..].contains(&expected));

        // A szándékosan hibás céldomaint sem közvetlenül, sem másolati aliason keresztül nem feltételezi.
        values.mark_domain(
            packed,
            UcpValueDomain::finite_set([0.into(), 1.into()]).unwrap(),
        );
        let facts = original.search_facts(&analyzer, &values).unwrap();
        assert_eq!(
            original
                .check_coverage_with_search_facts::<Fr>(
                    &public,
                    &UcpValueDomain::finite_set([0.into(), 1.into()]).unwrap(),
                    Some(2_000),
                    &facts
                )
                .unwrap(),
            Satisfiability::Satisfiable
        );
        let query = fs::read_to_string("src/output/private_domain_refinement.smt2").unwrap();
        let packed_name = &original.expressions[&public];
        let packed_equality =
            Analyzer::<Fr>::smt_field_equality(packed_name, &0.into(), &original.prime);
        assert_eq!(query[snapshot.len()..].matches(&packed_equality).count(), 1);

        let alias = CellId::advice(99, 0);
        analyzer
            .cell_to_cycle_head
            .insert(alias.to_string(), first_name.clone());
        values.mark_domain(
            alias.clone(),
            UcpValueDomain::finite_set([1.into(), 3.into()]).unwrap(),
        );
        let facts = original.search_facts(&analyzer, &values).unwrap();
        assert_eq!(facts.domains[first_name], BTreeSet::from([1.into()]));
        values.mark_known(first, 1.into());
        values.mark_domain(
            alias,
            UcpValueDomain::finite_set([2.into(), 3.into()]).unwrap(),
        );
        assert!(original.search_facts(&analyzer, &values).is_err());
        assert_eq!(original.smt, snapshot);
    }

    #[test]
    fn search_domain_budget_skips_whole_sets_deterministically_and_retains_exact_values() {
        let (analyzer, mut original) = search_domain_context();
        let mut forward = UcpValueFacts::new();
        let mut reverse = UcpValueFacts::new();
        for row in 0..200 {
            let cell = CellId::advice(90, row);
            original.variables.insert(cell.to_string());
            forward.mark_domain(
                cell,
                UcpValueDomain::finite_set([0.into(), 1.into(), 2.into()]).unwrap(),
            );
            reverse.mark_domain(
                CellId::advice(90, 199 - row),
                UcpValueDomain::finite_set([0.into(), 1.into(), 2.into()]).unwrap(),
            );
        }
        let exact = CellId::advice(90, 1000);
        original.variables.insert(exact.to_string());
        forward.mark_known(exact.clone(), 7.into());
        reverse.mark_known(exact.clone(), 7.into());
        let before = forward.clone();
        let facts = original.search_facts(&analyzer, &forward).unwrap();
        assert_eq!(
            facts.domains,
            original.search_facts(&analyzer, &reverse).unwrap().domains
        );
        assert_eq!(
            facts.domains[&exact.to_string()],
            BTreeSet::from([7.into()])
        );
        let finite: Vec<_> = facts
            .domains
            .values()
            .filter(|domain| domain.len() > 1)
            .collect();
        assert!(finite.iter().all(|domain| domain.len() == 3));
        assert_eq!(finite.len() * 3, MAX_SEARCH_DOMAIN_VALUES / 3 * 3);
        assert_eq!(forward, before);
    }

    #[test]
    fn search_facts_filter_domains_and_preserve_original_queries() {
        use crate::io::analyzer_io_type::VerificationInput;
        use crate::sample_circuits::zcash::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit;
        let input = AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput::new([("I-0-0".to_owned(), 3)], 1),
            lookup_method: LookupMethod::InlineConstraints,
        };
        let mut analyzer = Analyzer::<Fr>::new_with_original_subset_capture(
            &TwoBitDecompCircuit::<Fr>::default(),
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
            true,
        )
        .unwrap();
        let first = CellId::advice(0, 0);
        let second = CellId::advice(1, 0);
        let packed = CellId::advice(2, 0);
        let public = CellId::instance(0, 0);
        let original = analyzer
            .original_private_query_context(
                &input,
                &[
                    first.clone(),
                    second.clone(),
                    packed.clone(),
                    public.clone(),
                ],
            )
            .unwrap();
        let snapshot = original.smt.clone();
        let subsets = original.targeted_subsets.clone();
        let main_file = fs::read_to_string(&*SMT_FILE_PATH).unwrap();
        let mut values = UcpValueFacts::new();
        values.mark_known(first.clone(), &original.prime + 1);
        values.mark_domain(
            second.clone(),
            UcpValueDomain::finite_set([0.into(), 1.into()]).unwrap(),
        );
        values.mark_known(packed.clone(), 3.into());
        values.mark_known(public.clone(), 3.into());
        values.mark_known(CellId::fixed(0, 0), 1.into());
        values.mark_known(CellId::advice(99, 0), 123.into());
        let exact = original.search_facts(&analyzer, &values).unwrap();
        let first_name = &original.expressions[&first];
        let packed_name = &original.expressions[&packed];
        assert_eq!(exact.domains.len(), 3);
        assert_eq!(exact.domains[first_name], BTreeSet::from([BigInt::from(1)]));
        assert_eq!(
            exact.domains[packed_name],
            BTreeSet::from([BigInt::from(3)])
        );
        assert_eq!(
            exact.domains[&original.expressions[&second]],
            BTreeSet::from([BigInt::from(0), BigInt::from(1)])
        );

        // Querying an instance alias must also exclude the packed advice cell's exact fact.
        assert_eq!(original.expressions[&public], *packed_name);
        let mut bytes = Vec::new();
        original.write_search_facts::<Fr, _>(
            &mut Printer::new(&mut bytes),
            &original.expressions[&public],
            &exact,
        );
        let appended = String::from_utf8(bytes).unwrap();
        assert!(appended.contains(&Analyzer::<Fr>::smt_field_equality(
            first_name,
            &1.into(),
            &original.prime
        )));
        assert!(!appended.contains(&Analyzer::<Fr>::smt_field_equality(
            packed_name,
            &3.into(),
            &original.prime
        )));

        assert_eq!(
            original
                .query_unseen_value_with_search_facts::<Fr>(
                    &second,
                    &BTreeSet::new(),
                    Some(2_000),
                    &exact
                )
                .unwrap(),
            Some(1.into())
        );
        let accelerated = fs::read_to_string("src/output/private_domain_discovery.smt2").unwrap();
        let first_equality =
            Analyzer::<Fr>::smt_field_equality(first_name, &1.into(), &original.prime);
        assert!(accelerated[snapshot.len()..].contains(&first_equality));
        assert!(!accelerated[snapshot.len()..].contains("(or "));
        original
            .query_unseen_value::<Fr>(&second, &BTreeSet::new(), Some(2_000))
            .unwrap();
        let clean = fs::read_to_string("src/output/private_domain_discovery.smt2").unwrap();
        assert!(!clean[snapshot.len()..].contains(&first_equality));

        let candidate = UcpValueDomain::exact(1.into());
        assert_eq!(
            original
                .check_candidate_with_search_facts::<Fr>(&second, &candidate, Some(2_000), &exact)
                .unwrap(),
            Satisfiability::Satisfiable
        );
        let accelerated = fs::read_to_string("src/output/private_domain_refinement.smt2").unwrap();
        assert!(accelerated[snapshot.len()..].contains(&first_equality));
        assert_eq!(
            original
                .check_coverage_with_search_facts::<Fr>(&second, &candidate, Some(2_000), &exact)
                .unwrap(),
            Satisfiability::Unsatisfiable
        );
        let accelerated = fs::read_to_string("src/output/private_domain_refinement.smt2").unwrap();
        assert!(accelerated.starts_with(&snapshot));
        assert!(accelerated[snapshot.len()..].contains(&first_equality));
        // A lefedést a jelölthalmaz feltételezése helyett annak tagadásával vizsgálja.
        let second_equality = Analyzer::<Fr>::smt_field_equality(
            &original.expressions[&second],
            &1.into(),
            &original.prime,
        );
        assert!(accelerated[snapshot.len()..].contains(&format!("(not {second_equality})")));
        assert_eq!(
            original
                .check_coverage_with_search_facts::<Fr>(
                    &second,
                    &UcpValueDomain::exact(0.into()),
                    Some(2_000),
                    &exact
                )
                .unwrap(),
            Satisfiability::Satisfiable
        );
        assert_eq!(
            original
                .check_coverage_with_search_facts::<Fr>(
                    &public,
                    &UcpValueDomain::exact(3.into()),
                    Some(2_000),
                    &exact
                )
                .unwrap(),
            Satisfiability::Unsatisfiable
        );
        let accelerated = fs::read_to_string("src/output/private_domain_refinement.smt2").unwrap();
        let packed_equality =
            Analyzer::<Fr>::smt_field_equality(packed_name, &3.into(), &original.prime);
        // A cél másolati aliasának pontos ténye nem szerepel külön premisszaként, csak a kizárási kérdésben.
        assert_eq!(
            accelerated[snapshot.len()..]
                .matches(&packed_equality)
                .count(),
            1
        );
        assert!(accelerated[snapshot.len()..].contains(&format!("(not {packed_equality})")));
        original
            .check_membership::<Fr>(&second, &candidate, true, Some(2_000))
            .unwrap();
        let clean = fs::read_to_string("src/output/private_domain_refinement.smt2").unwrap();
        assert!(!clean[snapshot.len()..].contains(&first_equality));
        assert_eq!(original.smt, snapshot);
        assert_eq!(original.targeted_subsets, subsets);
        assert_eq!(fs::read_to_string(&*SMT_FILE_PATH).unwrap(), main_file);
    }

    #[test]
    fn subset_assertions_are_literal_original_equations_not_sat_hints() {
        use crate::io::analyzer_io_type::VerificationInput;
        use crate::sample_circuits::zcash::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit;
        let input = AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput::new([("I-0-0".to_owned(), 3)], 1),
            lookup_method: LookupMethod::InlineConstraints,
        };
        let mut analyzer = Analyzer::<Fr>::new(
            &TwoBitDecompCircuit::<Fr>::default(),
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
        )
        .unwrap();
        let original = fs::read_to_string(&*SMT_FILE_PATH).unwrap();
        let subset = analyzer.validation_subset_assertions.clone();
        assert!(!subset.is_empty());
        assert!(subset.len() <= MAX_VALIDATION_SUBSET_ASSERTIONS);
        for assertion in &subset {
            assert!(original.contains(&format!("(assert {assertion})")));
        }
        let mut hints = UcpValueFacts::new();
        hints.mark_known(CellId::advice(0, 0), BigInt::from(0));
        assert_eq!(
            analyzer
                .check_ucp_satisfiability_with_hints(&input, &hints)
                .unwrap(),
            Some(Satisfiability::Unsatisfiable)
        );
        assert_eq!(analyzer.validation_subset_assertions, subset);
    }

    #[test]
    fn subset_unknown_and_sat_require_full_fallback() {
        assert!(!Analyzer::<Fr>::subset_proves_exclusion(Ok(Satisfiability::Satisfiable)).unwrap());
        assert!(
            Analyzer::<Fr>::subset_proves_exclusion(Ok(Satisfiability::Unsatisfiable)).unwrap()
        );
        assert!(!Analyzer::<Fr>::subset_proves_exclusion(Err(anyhow!(
            smt_parser::UnknownSolverResult
        )))
        .unwrap());
        assert!(Analyzer::<Fr>::subset_proves_exclusion(Err(anyhow!("malformed output"))).is_err());
    }

    #[test]
    fn recovery_subsets_capture_literal_nonlinear_equations_only_when_enabled() {
        use crate::io::analyzer_io_type::VerificationInput;
        use crate::sample_circuits::zcash::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit;
        let input = AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput::new([("I-0-0".to_owned(), 3)], 1),
            lookup_method: LookupMethod::InlineConstraints,
        };
        let circuit = TwoBitDecompCircuit::<Fr>::default();
        let plain = Analyzer::<Fr>::new(
            &circuit,
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
        )
        .unwrap();
        assert!(plain.original_recovery_assertions.is_none());
        let mut captured = Analyzer::<Fr>::new_with_original_subset_capture(
            &circuit,
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
            true,
        )
        .unwrap();
        let full = fs::read_to_string(&*SMT_FILE_PATH).unwrap();
        let store = captured.original_recovery_assertions.as_ref().unwrap();
        assert!(store.assertions.iter().any(|a| a.body.contains("ff.mul")));
        for assertion in &store.assertions {
            assert!(full.contains(&format!("(assert {})", assertion.body)));
            assert!(assertion
                .variables
                .iter()
                .all(|v| captured.all_variables.contains(v)));
        }
        let targets = [CellId::advice(0, 0), CellId::advice(1, 0)];
        let original = captured
            .original_private_query_context(&input, &targets)
            .unwrap();
        let store = captured.original_recovery_assertions.as_ref().unwrap();
        for (text, count) in original.targeted_subsets.values() {
            assert!(*count > 0);
            assert!(
                *count
                    <= crate::circuit_analyzer::ucp::privacy_subset::MAX_TARGETED_SUBSET_ASSERTIONS
            );
            for line in text
                .lines()
                .filter(|line| line.starts_with("(assert (and ( = ("))
            {
                assert!(store
                    .assertions
                    .iter()
                    .any(|a| line == format!("(assert (and {}))", a.body)));
            }
            assert!(!text.contains("(check-sat)"));
        }
        assert!(!original.targeted_subsets.is_empty());
    }
}
