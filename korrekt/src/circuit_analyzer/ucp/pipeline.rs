#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

// Ez a modul köti össze a lightweight UCP-t a meglévő SMT alapú Analyzerrel.
// A pipeline menete a cikkhez hasonló:
//   1. UCP fut a circuitből kinyert constraint expressionökön.
//   2. Ha minden target/output unique, akkor SMT nélkül kész vagyunk.
//   3. Ha marad unresolved target vagy advice cella, akkor egy cellára rákérdezünk SMT-vel.
//   4. Ha az SMT unique-nak bizonyítja, hozzáadjuk K-hoz, és újra futtatjuk az UCP-t.
// Így az SMT-nek kevesebb változót kell szabadon kezelnie, az UCP pedig új információból tovább tud propagálni.
use super::{
    cell::CellId,
    choose_var::choose_query_cell,
    engine::{analyze_expressions_with_values_and_modulus, UcpResult, UcpTargetCheck},
    extractor::extract_ucp_problem_with_targets,
    value::initial_values_from_instance_cells,
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
    //Minden targetet tisztán UCP bizonyított unique-nak
    VerifiedByUcp,
    //SMT is kellett, de végül minden target unique lett
    VerifiedBySmt,
    //SMT bizonyította, hogy egy target nem unique
    RefutedBySmt,
    //Nem sikerült dönteni: se UCP, se SMT query sorozat nem adott végső választ
    Unknown,
}

#[derive(Debug)]
pub struct UcpAnalyzerPipelineOutput {
    //A teljes pipeline magas szintű eredménye
    pub status: UcpAnalyzerPipelineStatus,
    //Az utolsó UCP fixpoint futás eredménye
    pub ucp_result: UcpResult,
    //A target cellák ellenőrzési összefoglalója
    pub target_check: UcpTargetCheck,
    //Analyzer-kompatibilis output, hogy a régi API-val is együtt tudjon élni
    pub analyzer_output: AnalyzerOutput,
    //Igaz, ha legalább egyszer ténylegesen SMT-hez kellett fordulni
    pub used_smt: bool,
    //Hány egycellás semantic query futott
    pub semantic_queries: usize,
    //Azok a cellák, amelyeket SMT bizonyított unique-nak és bekerültek K-ba
    pub smt_learned_cells: Vec<CellId>,
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
//Teljes UCP + SMT pipeline underconstrained ellenőrzéshez
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
    //A célcellák azok az outputok/targetek, amelyek unique voltát végül bizonyítani akarjuk
    let target_cells: Vec<CellId> = target_cells.into_iter().collect();
    //Először létrehozzuk az analyzable circuitet, ebből tudunk gate-eket, régiókat és copy constraint-eket kinyerni
    let analyzable =
        crate::circuit_analyzer::analyzable::Analyzable::config_and_synthesize(circuit, k)
            .context("Failed to build analyzable circuit for UCP!")?;
    //A circuitből UCP problem lesz: expressionök, kezdeti K, targetek
    let problem = extract_ucp_problem_with_targets(&analyzable, target_cells);
    //Kezdeti K: instance/fixed cellák, plusz később SMT által tanult unique cellák
    let mut facts = problem.initial_facts.clone();
    //Kezdeti Delta: analyzer inputból ismert public instance értékek
    let mut value_facts =
        initial_values_from_instance_cells(analyzer_input.verification_input.instance_cells.iter());
    //Gyors membership check ahhoz, hogy egy SMT által refutált cella target-e
    let target_set: HashSet<CellId> = problem.target_cells.iter().cloned().collect();
    //Ezekre már rákérdeztünk SMT-vel, ne pörgessük újra ugyanazt
    let mut queried_cells = HashSet::new();
    let mut smt_learned_cells = Vec::new();
    let mut semantic_queries = 0;
    //Az Analyzer drága inicializálását csak akkor végezzük el, ha UCP önmagában nem elég
    let mut analyzer = None;

    loop {
        //UCP fixpoint futtatása az aktuális K és Delta mellett
        let ucp_result = analyze_expressions_with_values_and_modulus(
            &problem.expressions,
            facts.clone(),
            value_facts.clone(),
            &problem.field_modulus,
        );
        //Megnézzük, hogy a targetek bekerültek-e a végső K halmazba
        let target_check = ucp_result.check_targets(&problem.target_cells);

        //Ha minden target unique, akkor kész vagyunk; lehet tiszta UCP vagy SMT-vel támogatott siker
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

        //Ha maradt unresolved target/cella, kiválasztunk egyet SMT query-re
        let Some(query_cell) = choose_query_cell(
            &problem.expressions,
            &ucp_result.facts,
            &ucp_result.value_facts,
            &problem.field_modulus,
            &problem.target_cells,
            &queried_cells,
        ) else {
            //Nincs több értelmes cella, amit kérdezhetnénk, ezért a pipeline nem tud dönteni
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

        //SMT Analyzer csak itt épül fel először, ha tényleg szükség van rá
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
        //Az UCP által már unique-nak bizonyított advice cellákat fixként átadjuk az SMT-nek
        analyzer.set_ucp_unique_cells(ucp_result.facts.unique_cells().iter().cloned());
        semantic_queries += 1;

        //Egyetlen cellára kérdezünk rá: unique-e az aktuális constraint rendszer mellett?
        match analyzer
            .query_ucp_cell_uniqueness(analyzer_input, &query_cell)
            .with_context(|| format!("Failed to query SMT uniqueness for {}", query_cell))?
        {
            SemanticQueryResult::ProvenUnique => {
                //SMT tanult egy új unique cellát: frissítjük K-t, majd új UCP kör indul
                value_facts = ucp_result.value_facts.clone();
                facts = ucp_result.facts;
                if facts.mark_unique(query_cell.clone()) {
                    smt_learned_cells.push(query_cell);
                } else {
                    queried_cells.insert(query_cell);
                }
            }
            SemanticQueryResult::NotUnique => {
                //Ha ez target volt, akkor tényleges underconstrained hibát találtunk
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
                //Nem target advice cella nem lett unique; megjegyezzük, hogy erre már ne kérdezzünk rá
                queried_cells.insert(query_cell);
                value_facts = ucp_result.value_facts.clone();
                facts = ucp_result.facts;
            }
            SemanticQueryResult::Overconstrained => {
                //Az SMT oldalon overconstrained jelzés jött, ezt nem UCP döntésként kezeljük
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
                //SMT sem döntötte el ezt a cellát, ezért később mást próbálunk
                queried_cells.insert(query_cell);
                value_facts = ucp_result.value_facts.clone();
                facts = ucp_result.facts;
            }
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

    //Egyszerű selectoros circuit, amit az UCP önmagában meg tud oldani
    #[derive(Clone, Debug)]
    struct PipelineConfig {
        advice: Column<Advice>,
        selector: Selector,
    }

    //A pipeline teszt circuit példánya
    #[derive(Clone, Debug, Default)]
    struct PipelineCircuit {
        _marker: PhantomData<Fr>,
    }

    //Olyan circuit config, ahol UCP önmagában nem látja be a target uniqueness-t
    #[derive(Clone, Debug)]
    struct SmtOnlyConfig {
        advice: Column<Advice>,
    }

    //Ezt a példát SMT query fogja unique-nak bizonyítani
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

            //A gate: advice + public - 5 = 0, selectorrel aktiválva
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
                    //Bekapcsoljuk a gate-et az adott sorban
                    config.selector.enable(&mut region, 0)?;
                    //A witness érték public=2 mellett 3, így 3+2-5=0
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

            //A polynomial (x-1)^2 = 0 alakú, amit az SMT tud egyértelműsíteni x=1-re
            meta.create_gate("expanded repeated root", |meta| {
                let x = meta.query_advice(advice, Rotation::cur());

                vec![
                    x.clone() * x.clone() - Expression::Constant(Fr::from(2)) * x
                        + Expression::Constant(Fr::from(1)),
                ]
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
                    //A witness érték a gyök: x = 1
                    region.assign_advice(|| "x", config.advice, 0, || Value::known(Fr::from(1)))?;
                    Ok(())
                },
            )
        }
    }

    //Ellenőrzi, hogy ha UCP már bizonyítja a targetet, akkor SMT nem indul el
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

    //Ellenőrzi, hogy az Analyzer megkapja az UCP által unique advice cellákat fix változóként
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

    //Ellenőrzi a teljes ciklust: UCP nem elég, SMT tanul egy cellát, majd az bekerül K-ba
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
