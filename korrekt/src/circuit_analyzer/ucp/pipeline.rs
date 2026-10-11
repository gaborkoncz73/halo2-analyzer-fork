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
    engine::{UcpResult, UcpTargetCheck},
    extractor::extract_ucp_problem_with_targets,
    value::{normalize_field_value, parse_cell_id},
};
use crate::{
    circuit_analyzer::{
        analyzable::AnalyzableField,
        analyzer::{Analyzer, SemanticQueryResult},
        halo2_proofs_libs::*,
    },
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerOutput, AnalyzerOutputStatus, AnalyzerType, VerificationMethod,
    },
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
    analyze_underconstrained_with_ucp_internal(circuit, k, analyzer_input, target_cells, false)
}

/// Attempts concrete values even after all targets have been proved unique.
/// Recovery is bounded and may remain incomplete; inspect `ucp_result.value_facts`
/// for exact values. The returned status continues to describe target uniqueness.
pub fn analyze_underconstrained_with_ucp_and_value_recovery<F, ConcreteCircuit, I>(
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
    analyze_underconstrained_with_ucp_internal(circuit, k, analyzer_input, target_cells, true)
}

fn analyze_underconstrained_with_ucp_internal<F, ConcreteCircuit, I>(
    circuit: &ConcreteCircuit,
    k: u32,
    analyzer_input: &AnalyzerInput,
    target_cells: I,
    recover_target_values: bool,
) -> Result<UcpAnalyzerPipelineOutput>
where
    F: AnalyzableField,
    ConcreteCircuit: Circuit<F>,
    I: IntoIterator<Item = CellId>,
{
    //A célcellák azok az outputok/targetek, amelyek unique voltát végül bizonyítani akarjuk
    analyzer_input.verification_input.validate_public_values()?;
    let target_cells: Vec<CellId> = target_cells.into_iter().collect();
    //Először létrehozzuk az analyzable circuitet, ebből tudunk gate-eket, régiókat és copy constraint-eket kinyerni
    let analyzable =
        crate::circuit_analyzer::analyzable::Analyzable::config_and_synthesize(circuit, k)
            .context("Failed to build analyzable circuit for UCP!")?;
    //A circuitből UCP problem lesz: expressionök, kezdeti K, O outputok és W witnessek
    let problem = extract_ucp_problem_with_targets(&analyzable, target_cells);
    //Kezdeti K: instance/fixed cellák, plusz később SMT által tanult unique cellák
    let mut facts = problem.initial_facts.clone();
    //Kezdeti Delta: lookup/range table domainek, plusz analyzer inputból ismert public instance értékek
    let mut value_facts = problem.initial_value_facts.clone();
    if analyzer_input.verification_method == VerificationMethod::Specific {
        for (name, value) in &analyzer_input.verification_input.instance_cells {
            if let Some(cell) = parse_cell_id(name) {
                let value = normalize_field_value(value.clone(), &problem.field_modulus)
                    .context("Public observation is outside the supported value range")?;
                value_facts.mark_known(cell, value);
            }
        }
    }
    //Gyors membership check ahhoz, hogy egy SMT által refutált cella target-e
    let target_set: HashSet<CellId> = problem.output_cells.iter().cloned().collect();
    //Ezekre már rákérdeztünk SMT-vel, ne pörgessük újra ugyanazt
    let mut queried_cells = HashSet::new();
    let mut smt_learned_cells = Vec::new();
    let mut semantic_queries = 0;
    //Az Analyzer drága inicializálását csak akkor végezzük el, ha UCP önmagában nem elég
    let mut analyzer = None;

    loop {
        //UCP fixpoint futtatása az aktuális K és Delta mellett
        let ucp_result = problem.analyze_with_values(facts.clone(), value_facts.clone());
        //Megnézzük, hogy a targetek bekerültek-e a végső K halmazba
        let target_check = ucp_result.check_targets(&problem.output_cells);
        let recovery_cell = if recover_target_values && target_check.all_targets_unique() {
            problem
                .output_cells
                .iter()
                .find(|cell| {
                    ucp_result.value_facts.known_value(cell).is_none()
                        && !queried_cells.contains(*cell)
                })
                .cloned()
        } else {
            None
        };

        //Ha minden target unique, akkor kész vagyunk; lehet tiszta UCP vagy SMT-vel támogatott siker
        if target_check.all_targets_unique() && recovery_cell.is_none() {
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

        //Ha maradt unresolved output/witness, kiválasztunk egyet SMT query-re:
        //V = (O unio W) \ K', a cikk Algorithm 1 lépése szerint
        let Some(query_cell) = recovery_cell.or_else(|| {
            choose_query_cell(
                &problem.expressions,
                &ucp_result.facts,
                &ucp_result.value_facts,
                &problem.field_modulus,
                &problem.output_cells,
                &problem.witness_cells,
                &queried_cells,
            )
        }) else {
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
        //A cikk QUERY(Delta, C, K', v) lépésének megfelelően a domain információt is átadjuk
        analyzer.set_ucp_value_facts(&ucp_result.value_facts);
        semantic_queries += 1;

        //Egyetlen cellára kérdezünk rá: unique-e az aktuális constraint rendszer mellett?
        let query_output = analyzer
            .query_ucp_cell_uniqueness_with_value(analyzer_input, &query_cell)
            .with_context(|| format!("Failed to query SMT uniqueness for {}", query_cell))?;
        match query_output.result {
            SemanticQueryResult::ProvenUnique => {
                //SMT tanult egy új unique cellát: frissítjük K-t, majd új UCP kör indul
                value_facts = ucp_result.value_facts.clone();
                facts = ucp_result.facts;
                if let Some(value) = query_output.value {
                    value_facts.mark_known(query_cell.clone(), value);
                }
                //Ertekkorlat vagy ismeretlen public miatt a visszaallitas eredmenytelen is lehet.
                queried_cells.insert(query_cell.clone());
                if facts.mark_unique(query_cell.clone()) {
                    smt_learned_cells.push(query_cell);
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
    use crate::circuit_analyzer::ucp::value::{UcpValueDomain, UcpValueFacts};
    use crate::io::analyzer_io_type::{
        AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod,
    };
    use num_bigint::BigInt;
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

    #[derive(Clone, Debug)]
    struct DomainOnlyConfig {
        advice: Column<Advice>,
    }

    #[derive(Clone, Debug, Default)]
    struct DomainOnlyCircuit {
        _marker: PhantomData<Fr>,
    }

    #[derive(Clone, Debug, Default)]
    struct PartialPublicCircuit;

    impl Circuit<Fr> for PartialPublicCircuit {
        type Config = (Column<Advice>, Selector);
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let advice = meta.advice_column();
            let public = meta.instance_column();
            let selector = meta.selector();
            meta.create_gate("two public values", |meta| {
                let x = meta.query_advice(advice, Rotation::cur());
                let first = meta.query_instance(public, Rotation::cur());
                let second = meta.query_instance(public, Rotation::next());
                vec![
                    meta.query_selector(selector)
                        * (x + first + second - Expression::Constant(Fr::from(5))),
                ]
            });
            (advice, selector)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "partial public row",
                |mut region| {
                    config.1.enable(&mut region, 0)?;
                    region.assign_advice(|| "x", config.0, 0, || Value::known(Fr::from(3)))?;
                    Ok(())
                },
            )
        }
    }

    #[derive(Clone, Debug)]
    struct LargeLinearConfig {
        cells: Vec<Column<Advice>>,
        selector: Selector,
    }

    #[derive(Clone, Debug, Default)]
    struct LargeLinearCircuit;

    //Paratlan hosszu kor: x_i+x_(i+1)=2 minden i-re, az egyetlen megoldas mindenhol 1.
    impl Circuit<Fr> for LargeLinearCircuit {
        type Config = LargeLinearConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let cells: Vec<_> = (0..65).map(|_| meta.advice_column()).collect();
            let selector = meta.selector();
            meta.create_gate("large coupled linear ring", |meta| {
                let selected = meta.query_selector(selector);
                (0..cells.len())
                    .map(|index| {
                        let x = meta.query_advice(cells[index], Rotation::cur());
                        let next =
                            meta.query_advice(cells[(index + 1) % cells.len()], Rotation::cur());
                        selected.clone() * (x + next - Expression::Constant(Fr::from(2)))
                    })
                    .collect::<Vec<_>>()
            });
            LargeLinearConfig { cells, selector }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "linear ring",
                |mut region| {
                    config.selector.enable(&mut region, 0)?;
                    for cell in &config.cells {
                        region.assign_advice(
                            || "balance",
                            *cell,
                            0,
                            || Value::known(Fr::from(1)),
                        )?;
                    }
                    Ok(())
                },
            )
        }
    }

    fn no_public_input() -> AnalyzerInput {
        AnalyzerInput {
            verification_method: VerificationMethod::None,
            verification_input: VerificationInput {
                instance_cells: HashMap::new(),
                iterations: 1,
            },
            lookup_method: LookupMethod::InlineConstraints,
        }
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

    impl Circuit<Fr> for DomainOnlyCircuit {
        type Config = DomainOnlyConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let advice = meta.advice_column();

            DomainOnlyConfig { advice }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> std::result::Result<(), Error> {
            layouter.assign_region(
                || "domain only row",
                |mut region| {
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
        instance_cells.insert("I-0-0".to_string(), 2.into());
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
        instance_cells.insert("I-0-0".to_string(), 2.into());
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

    //Ellenőrzi, hogy a Delta exact domain tényleges SMT assertionként bekerül a semantic query-be
    #[test]
    fn analyzer_uses_ucp_exact_value_domains_in_semantic_query() {
        let circuit = DomainOnlyCircuit::default();
        let analyzer_input = AnalyzerInput {
            verification_method: VerificationMethod::None,
            verification_input: VerificationInput {
                instance_cells: HashMap::new(),
                iterations: 1,
            },
            lookup_method: LookupMethod::InlineConstraints,
        };
        let target = CellId::advice(0, 0);
        let mut analyzer = Analyzer::<Fr>::new(
            &circuit,
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&analyzer_input),
        )
        .unwrap();

        assert_eq!(
            analyzer
                .query_ucp_cell_uniqueness(&analyzer_input, &target)
                .unwrap(),
            SemanticQueryResult::NotUnique
        );

        let mut value_facts = UcpValueFacts::new();
        value_facts.mark_known(target.clone(), BigInt::from(1));
        analyzer.set_ucp_value_facts(&value_facts);

        assert_eq!(
            analyzer.ucp_value_domains(),
            &[("A-0-0".to_string(), UcpValueDomain::exact(BigInt::from(1)))]
        );
        assert_eq!(
            analyzer
                .query_ucp_cell_uniqueness(&analyzer_input, &target)
                .unwrap(),
            SemanticQueryResult::ProvenUnique
        );
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
        assert_eq!(
            output
                .ucp_result
                .value_facts
                .known_value(&CellId::advice(0, 0)),
            Some(&BigInt::from(1))
        );
    }

    //K tagsag mellett is valoban ellenorizzuk a konkret erteket, nem rogzitjuk a modell K ertekeit.
    #[test]
    fn recovers_value_of_cell_already_in_k() {
        let input = no_public_input();
        let target = CellId::advice(0, 0);
        let mut analyzer = Analyzer::<Fr>::new(
            &SmtOnlyCircuit::default(),
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
        )
        .unwrap();
        analyzer.set_ucp_unique_cells([target.clone()]);
        let output = analyzer
            .query_ucp_cell_uniqueness_with_value(&input, &target)
            .unwrap();
        assert_eq!(output.result, SemanticQueryResult::ProvenUnique);
        assert_eq!(output.value, Some(BigInt::from(1)));

        let mut analyzer = Analyzer::<Fr>::new(
            &DomainOnlyCircuit::default(),
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
        )
        .unwrap();
        analyzer.set_ucp_unique_cells([target.clone()]);
        let output = analyzer
            .query_ucp_cell_uniqueness_with_value(&input, &target)
            .unwrap();
        assert_eq!(output.result, SemanticQueryResult::NotUnique);
        assert_eq!(output.value, None);
    }

    #[test]
    fn symbolic_public_input_does_not_become_an_exact_model_sample() {
        let mut input = no_public_input();
        input.verification_method = VerificationMethod::Random;
        let mut analyzer = Analyzer::<Fr>::new(
            &PipelineCircuit::default(),
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
        )
        .unwrap();
        let output = analyzer
            .query_ucp_cell_uniqueness_with_value(&input, &CellId::advice(0, 0))
            .unwrap();
        assert_eq!(output.result, SemanticQueryResult::ProvenUnique);
        assert_eq!(output.value, None);
    }

    #[test]
    fn partially_fixed_public_inputs_do_not_produce_exact_values() {
        let mut input = no_public_input();
        input.verification_method = VerificationMethod::Specific;
        input
            .verification_input
            .instance_cells
            .insert("I-0-0".to_string(), 2.into());
        let mut analyzer = Analyzer::<Fr>::new(
            &PartialPublicCircuit,
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
        )
        .unwrap();
        let output = analyzer
            .query_ucp_cell_uniqueness_with_value(&input, &CellId::advice(0, 0))
            .unwrap();
        assert_eq!(output.result, SemanticQueryResult::ProvenUnique);
        assert_eq!(output.value, None);

        //Mindket public ertek rogzitve: a solver erteke a kenyszerekbol jon, nem a synthesize witnessbol.
        input
            .verification_input
            .instance_cells
            .insert("I-0-1".to_string(), 1.into());
        let mut analyzer = Analyzer::<Fr>::new(
            &PartialPublicCircuit,
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
        )
        .unwrap();
        let output = analyzer
            .query_ucp_cell_uniqueness_with_value(&input, &CellId::advice(0, 0))
            .unwrap();
        assert_eq!(output.result, SemanticQueryResult::ProvenUnique);
        assert_eq!(output.value, Some(BigInt::from(2)));
    }

    #[test]
    fn recovered_values_use_signed_field_representatives() {
        let input = no_public_input();
        let target = CellId::advice(0, 0);
        let mut analyzer = Analyzer::<Fr>::new(
            &DomainOnlyCircuit::default(),
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
        )
        .unwrap();
        let mut values = UcpValueFacts::new();
        values.mark_known(target.clone(), BigInt::from(-1));
        analyzer.set_ucp_value_facts(&values);
        let output = analyzer
            .query_ucp_cell_uniqueness_with_value(&input, &target)
            .unwrap();
        assert_eq!(output.result, SemanticQueryResult::ProvenUnique);
        assert_eq!(output.value, Some(BigInt::from(-1)));
    }

    #[test]
    fn inconsistent_constraints_do_not_produce_recovered_values() {
        let input = no_public_input();
        let target = CellId::advice(0, 0);
        let mut analyzer = Analyzer::<Fr>::new(
            &SmtOnlyCircuit::default(),
            4,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&input),
        )
        .unwrap();
        let mut values = UcpValueFacts::new();
        values.mark_known(target.clone(), BigInt::from(0));
        analyzer.set_ucp_value_facts(&values);
        let output = analyzer
            .query_ucp_cell_uniqueness_with_value(&input, &target)
            .unwrap();
        assert_eq!(output.result, SemanticQueryResult::Overconstrained);
        assert_eq!(output.value, None);
    }

    //A gyors ut K-val kesz; a recovery ut egy SMT ertekbol mind a 65 Delta erteket megtanulja.
    #[test]
    fn value_recovery_continues_after_targets_are_unique() {
        let input = no_public_input();
        let target = CellId::advice(0, 0);
        let fast = analyze_underconstrained_with_ucp::<Fr, _, _>(
            &LargeLinearCircuit,
            4,
            &input,
            [target.clone()],
        )
        .unwrap();
        assert_eq!(fast.status, UcpAnalyzerPipelineStatus::VerifiedByUcp);
        assert_eq!(fast.semantic_queries, 0);
        assert!(fast.ucp_result.value_facts.known_value(&target).is_none());

        let recovered = analyze_underconstrained_with_ucp_and_value_recovery::<Fr, _, _>(
            &LargeLinearCircuit,
            4,
            &input,
            [target],
        )
        .unwrap();
        assert_eq!(recovered.status, UcpAnalyzerPipelineStatus::VerifiedBySmt);
        assert_eq!(recovered.semantic_queries, 1);
        assert!(recovered.smt_learned_cells.is_empty());
        for column in 0..65 {
            assert_eq!(
                recovered
                    .ucp_result
                    .value_facts
                    .known_value(&CellId::advice(column, 0)),
                Some(&BigInt::from(1))
            );
        }
    }
}
