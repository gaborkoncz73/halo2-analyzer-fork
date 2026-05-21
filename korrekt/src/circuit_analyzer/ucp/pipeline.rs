#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

use super::{
    cell::{CellId, CellKind},
    engine::{analyze_expressions, UcpResult, UcpTargetCheck},
    expr::UcpExpr,
    extractor::extract_ucp_problem_with_targets,
    facts::UcpFacts,
};
use crate::{
    circuit_analyzer::{
        analyzable::AnalyzableField,
        analyzer::{Analyzer, SemanticQueryResult},
        halo2_proofs_libs::*,
    },
    io::analyzer_io_type::{AnalyzerInput, AnalyzerOutput, AnalyzerOutputStatus, AnalyzerType},
};
use anyhow::{Context, Result};
use std::collections::HashSet;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum UcpAnalyzerPipelineStatus {
    VerifiedByUcp,
    VerifiedBySmt,
    RefutedBySmt,
    Unknown,
}

#[derive(Debug)]
pub struct UcpAnalyzerPipelineOutput {
    pub status: UcpAnalyzerPipelineStatus,
    pub ucp_result: UcpResult,
    pub target_check: UcpTargetCheck,
    pub analyzer_output: AnalyzerOutput,
    pub used_smt: bool,
    pub semantic_queries: usize,
    pub smt_learned_cells: Vec<CellId>,
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
pub fn analyze_underconstrained_with_ucp<F, ConcreteCircuit, I>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    target_cells: I,
) -> Result<UcpAnalyzerPipelineOutput>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
    I: IntoIterator<Item = CellId>,
{
    let target_cells: Vec<CellId> = target_cells.into_iter().collect();
    let analyzable =
        crate::circuit_analyzer::analyzable::Analyzable::config_and_synthesize(circuit, k)
            .context("Failed to build analyzable circuit for UCP!")?;
    let problem = extract_ucp_problem_with_targets(&analyzable, target_cells);
    let mut facts = problem.initial_facts.clone();
    let target_set: HashSet<CellId> = problem.target_cells.iter().cloned().collect();
    let mut queried_cells = HashSet::new();
    let mut smt_learned_cells = Vec::new();
    let mut semantic_queries = 0;
    let mut analyzer = None;

    loop {
        let ucp_result = analyze_expressions(&problem.expressions, facts.clone());
        let target_check = ucp_result.check_targets(&problem.target_cells);

        if target_check.all_targets_unique() {
            let used_smt = semantic_queries > 0;
            return Ok(UcpAnalyzerPipelineOutput {
                status: if used_smt {
                    UcpAnalyzerPipelineStatus::VerifiedBySmt
                } else {
                    UcpAnalyzerPipelineStatus::VerifiedByUcp
                },
                ucp_result,
                target_check,
                analyzer_output: AnalyzerOutput {
                    output_status: AnalyzerOutputStatus::NotUnderconstrainedLocal,
                },
                used_smt,
                semantic_queries,
                smt_learned_cells,
            });
        }

        let Some(query_cell) = choose_query_cell(
            &problem.expressions,
            &ucp_result.facts,
            &problem.target_cells,
            &queried_cells,
        ) else {
            return Ok(UcpAnalyzerPipelineOutput {
                status: UcpAnalyzerPipelineStatus::Unknown,
                ucp_result,
                target_check,
                analyzer_output: AnalyzerOutput {
                    output_status: AnalyzerOutputStatus::Invalid,
                },
                used_smt: semantic_queries > 0,
                semantic_queries,
                smt_learned_cells,
            });
        };

        if analyzer.is_none() {
            analyzer = Some(
                Analyzer::<F>::new(
                    circuit,
                    k,
                    AnalyzerType::UnderconstrainedCircuit,
                    Some(analyzer_input),
                )
                .context("Failed to initialize analyzer after UCP!")?,
            );
        }
        let analyzer = analyzer
            .as_mut()
            .expect("analyzer was initialized above before semantic query");
        analyzer.set_ucp_unique_cells(ucp_result.facts.unique_cells().iter().cloned());
        semantic_queries += 1;

        match analyzer
            .query_ucp_cell_uniqueness(analyzer_input, &query_cell)
            .with_context(|| format!("Failed to query SMT uniqueness for {}", query_cell))?
        {
            SemanticQueryResult::ProvenUnique => {
                facts = ucp_result.facts;
                if facts.mark_unique(query_cell.clone()) {
                    smt_learned_cells.push(query_cell);
                } else {
                    queried_cells.insert(query_cell);
                }
            }
            SemanticQueryResult::NotUnique => {
                if target_set.contains(&query_cell) {
                    return Ok(UcpAnalyzerPipelineOutput {
                        status: UcpAnalyzerPipelineStatus::RefutedBySmt,
                        ucp_result,
                        target_check,
                        analyzer_output: AnalyzerOutput {
                            output_status: AnalyzerOutputStatus::Underconstrained,
                        },
                        used_smt: true,
                        semantic_queries,
                        smt_learned_cells,
                    });
                }
                queried_cells.insert(query_cell);
                facts = ucp_result.facts;
            }
            SemanticQueryResult::Overconstrained => {
                return Ok(UcpAnalyzerPipelineOutput {
                    status: UcpAnalyzerPipelineStatus::Unknown,
                    ucp_result,
                    target_check,
                    analyzer_output: AnalyzerOutput {
                        output_status: AnalyzerOutputStatus::Overconstrained,
                    },
                    used_smt: true,
                    semantic_queries,
                    smt_learned_cells,
                });
            }
            SemanticQueryResult::Unknown => {
                queried_cells.insert(query_cell);
                facts = ucp_result.facts;
            }
        }
    }
}

fn choose_query_cell(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    target_cells: &[CellId],
    queried_cells: &HashSet<CellId>,
) -> Option<CellId> {
    for target in target_cells {
        if !facts.is_unique(target) && !queried_cells.contains(target) {
            return Some(target.clone());
        }
    }

    let mut advice_cells = HashSet::new();
    for expr in expressions {
        collect_advice_cells(expr, &mut advice_cells);
    }

    let mut advice_cells: Vec<CellId> = advice_cells
        .into_iter()
        .filter(|cell| !facts.is_unique(cell) && !queried_cells.contains(cell))
        .collect();
    advice_cells.sort();
    advice_cells.into_iter().next()
}

fn collect_advice_cells(expr: &UcpExpr, cells: &mut HashSet<CellId>) {
    match expr {
        UcpExpr::Var(cell) => {
            if matches!(cell.kind, CellKind::Advice) {
                cells.insert(cell.clone());
            }
        }
        UcpExpr::Const(_) => {}
        UcpExpr::Neg(inner) | UcpExpr::Scale(inner, _) => collect_advice_cells(inner, cells),
        UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
            collect_advice_cells(left, cells);
            collect_advice_cells(right, cells);
        }
    }
}

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod tests {
    use super::*;
    use crate::io::analyzer_io_type::{
        AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod,
    };
    use std::{collections::HashMap, marker::PhantomData};

    #[derive(Clone, Debug)]
    struct PipelineConfig {
        advice: Column<Advice>,
        selector: Selector,
    }

    #[derive(Clone, Debug, Default)]
    struct PipelineCircuit {
        _marker: PhantomData<Fr>,
    }

    #[derive(Clone, Debug)]
    struct SmtOnlyConfig {
        advice: Column<Advice>,
    }

    #[derive(Clone, Debug, Default)]
    struct SmtOnlyCircuit {
        _marker: PhantomData<Fr>,
    }

    impl Circuit<Fr> for PipelineCircuit {
        type Config = PipelineConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let advice = meta.advice_column();
            let instance = meta.instance_column();
            let selector = meta.selector();

            meta.create_gate("pipeline selected assignment", |meta| {
                let selector = meta.query_selector(selector);
                let advice = meta.query_advice(advice, Rotation::cur());
                let public = meta.query_instance(instance, Rotation::cur());

                vec![selector * (advice + public - Expression::Constant(Fr::from(5)))]
            });

            PipelineConfig { advice, selector }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> std::result::Result<(), Error> {
            layouter.assign_region(
                || "pipeline row",
                |mut region| {
                    config.selector.enable(&mut region, 0)?;
                    region.assign_advice(
                        || "advice",
                        config.advice,
                        0,
                        || Value::known(Fr::from(3)),
                    )?;
                    Ok(())
                },
            )
        }
    }

    impl Circuit<Fr> for SmtOnlyCircuit {
        type Config = SmtOnlyConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let advice = meta.advice_column();

            meta.create_gate("square zero", |meta| {
                let x = meta.query_advice(advice, Rotation::cur());

                vec![x.clone() * x]
            });

            SmtOnlyConfig { advice }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> std::result::Result<(), Error> {
            layouter.assign_region(
                || "smt only row",
                |mut region| {
                    region.assign_advice(|| "x", config.advice, 0, || Value::known(Fr::zero()))?;
                    Ok(())
                },
            )
        }
    }

    #[test]
    fn verifies_targets_with_ucp_before_smt() {
        let circuit = PipelineCircuit::default();
        let mut instance_cells = HashMap::new();
        instance_cells.insert("I-0-0".to_string(), 2);
        let analyzer_input = AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instance_cells,
                iterations: 1,
            },
            lookup_method: LookupMethod::InlineConstraints,
        };

        let output = analyze_underconstrained_with_ucp::<Fr, _, _>(
            &circuit,
            4,
            &analyzer_input,
            [CellId::advice(0, 0)],
        )
        .unwrap();

        assert!(!output.used_smt);
        assert!(output.target_check.all_targets_unique());
        assert_eq!(
            output.analyzer_output.output_status,
            AnalyzerOutputStatus::NotUnderconstrainedLocal
        );
    }

    #[test]
    fn analyzer_accepts_ucp_unique_cells_as_smt_fixed_variables() {
        let circuit = PipelineCircuit::default();
        let mut instance_cells = HashMap::new();
        instance_cells.insert("I-0-0".to_string(), 2);
        let analyzer_input = AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instance_cells,
                iterations: 1,
            },
            lookup_method: LookupMethod::InlineConstraints,
        };
        let mut analyzer = Analyzer::<Fr>::new(
            &circuit,
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&analyzer_input),
        )
        .unwrap();

        analyzer.set_ucp_unique_cells([CellId::advice(0, 0), CellId::fixed(0, 0)]);

        assert!(analyzer.ucp_unique_variables().contains("A-0-0"));
        assert!(!analyzer.ucp_unique_variables().contains("F-0-0"));
    }

    #[test]
    fn learns_target_from_smt_query_and_updates_k() {
        let circuit = SmtOnlyCircuit::default();
        let analyzer_input = AnalyzerInput {
            verification_method: VerificationMethod::None,
            verification_input: VerificationInput {
                instance_cells: HashMap::new(),
                iterations: 1,
            },
            lookup_method: LookupMethod::InlineConstraints,
        };

        let output = analyze_underconstrained_with_ucp::<Fr, _, _>(
            &circuit,
            4,
            &analyzer_input,
            [CellId::advice(0, 0)],
        )
        .unwrap();

        assert_eq!(output.status, UcpAnalyzerPipelineStatus::VerifiedBySmt);
        assert!(output.used_smt);
        assert_eq!(output.semantic_queries, 1);
        assert_eq!(output.smt_learned_cells, vec![CellId::advice(0, 0)]);
        assert!(output.target_check.all_targets_unique());
    }
}
