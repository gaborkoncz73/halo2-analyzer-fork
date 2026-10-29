#![cfg(not(feature = "use_pse_v1_halo2_proofs"))]

// Ez a modul az UCP-következtetést a meglévő SMT-alapú Analyzer rendszerhez kapcsolja.
// A vezérlés a cikkhez hasonló lépéseket követ:
//    1. UCP-t futtat a kapcsolásból kinyert kifejezéseken.
//    2. Ha minden célcella egyértelmű, további egyértelműségi SMT-vizsgálat nélkül eredményt ad.
//    3. Ha marad vizsgálandó cél- vagy advice cella, kiválaszt egyet SMT-lekérdezésre.
//    4. Az újonnan igazolt egyértelműséget K-ba jegyzi, majd újra futtatja az UCP-t.
// Az SMT-től kapott új tényekkel további következtetéseket végez, az igazolt tényeket pedig átadja az SMT-nek.
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
    // Minden célcella egyértelműségét tisztán UCP-vel igazolja.
    VerifiedByUcp,
    // SMT-vizsgálatot is végez, és végül minden célcella egyértelműségét igazolja.
    VerifiedBySmt,
    // SMT-vel igazolja legalább egy célcella nemegyértelműségét.
    RefutedBySmt,
    // Sem UCP-vel, sem a végrehajtott SMT-lekérdezésekkel nem jut végső döntésre.
    Unknown,
}

#[derive(Debug)]
pub struct UcpAnalyzerPipelineOutput {
    // A teljes elemzési folyamat eredményét tartalmazza.
    pub status: UcpAnalyzerPipelineStatus,
    // Az utolsó UCP-fixpontszámítás eredményét tárolja.
    pub ucp_result: UcpResult,
    // A célcellák ellenőrzésének összefoglalóját tárolja.
    pub target_check: UcpTargetCheck,
    // Az eredményt az Analyzer felületével kompatibilis alakban is elérhetővé teszi.
    pub analyzer_output: AnalyzerOutput,
    // Azt jelzi, hogy a futás indított-e SMT-vizsgálatot.
    pub used_smt: bool,
    // A végrehajtott egycellás szemantikai próbákat számolja.
    pub semantic_queries: usize,
    // Az SMT-vel igazolt és K-ba felvett cellákat tárolja.
    pub smt_learned_cells: Vec<CellId>,
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
// Az alulkényszerezettség vizsgálatához összekapcsolja az UCP- és SMT-következtetést.
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

/// A konkrét értékek visszaállítását minden célcella egyértelműségének igazolása után is megpróbálja.
/// A visszaállítást korlátozza; a konkrét értékeket a ucp_result.value_facts mezőben adja vissza.
/// A visszaadott fő státusz továbbra is a célcellák egyértelműségét minősíti.
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
    // Kijelöli a kimeneti célcellákat, amelyek egyértelműségét igazolni próbálja.
    analyzer_input.verification_input.validate_public_values()?;
    let target_cells: Vec<CellId> = target_cells.into_iter().collect();
    // Előállítja az Analyzable kapcsolást a kapuk, régiók és másolási kényszerek kigyűjtéséhez.
    let analyzable =
        crate::circuit_analyzer::analyzable::Analyzable::config_and_synthesize(circuit, k)
            .context("Failed to build analyzable circuit for UCP!")?;
    // A kapcsolásból UCP-problémát készít: kifejezéseket, kezdeti K-t, O célokat és W advice cellákat.
    let problem = extract_ucp_problem_with_targets(&analyzable, target_cells);
    // K-t az instance és fixed cellákkal inicializálja; az SMT-tényeket később adja hozzá.
    let mut facts = problem.initial_facts.clone();
    // Deltát a lookup-domainekkel és a megadott publikus instance értékekkel inicializálja.
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
    // Halmazban tárolja a célcellákat, hogy gyorsan eldöntse, célhoz tartozik-e az ellenpélda.
    let target_set: HashSet<CellId> = problem.output_cells.iter().cloned().collect();
    // Megjegyzi a már lekérdezett cellákat, hogy ne ismételje ugyanazt a próbát.
    let mut queried_cells = HashSet::new();
    let mut smt_learned_cells = Vec::new();
    let mut semantic_queries = 0;
    // Az Analyzer költséges inicializálását az első szükséges SMT-vizsgálatig halasztja.
    let mut analyzer = None;

    loop {
        // Az aktuális K és Delta alapján UCP-fixpontot számít.
        let ucp_result = problem.analyze_with_values(facts.clone(), value_facts.clone());
        // Ellenőrzi, hogy minden célcella bekerült-e a végső K-ba.
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

        // Minden célcella egyértelműségénél elkészíti a tisztán UCP-s vagy SMT-vel támogatott eredményt.
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

        // A még vizsgálandó kimeneti és advice cellák közül választ SMT-lekérdezésre:
        // a cikk algoritmusának megfelelő V = (O unio W) \ K' halmazt használja.
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
            // Ha nincs több lekérdezhető cella, bizonytalan eredménnyel zárja a folyamatot.
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

        // Az SMT-analyzert az első ténylegesen szükséges vizsgálatnál építi fel.
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
        // Az UCP-vel igazoltan egyértelmű advice cellákat rögzítettként átadja az SMT-nek.
        analyzer.set_ucp_unique_cells(ucp_result.facts.unique_cells().iter().cloned());
        // A cikk QUERY(Delta,C,K',v) lépésének megfelelően a domainadatokat is átadja.
        analyzer.set_ucp_value_facts(&ucp_result.value_facts);
        semantic_queries += 1;

        // Egy cella egyértelműségét vizsgálja az aktuális kényszerrendszer mellett.
        let query_output = analyzer
            .query_ucp_cell_uniqueness_with_value(analyzer_input, &query_cell)
            .with_context(|| format!("Failed to query SMT uniqueness for {}", query_cell))?;
        match query_output.result {
            SemanticQueryResult::ProvenUnique => {
                // Az SMT új egyértelműségi tényét K-ba jegyzi, majd új UCP-kört indít.
                value_facts = ucp_result.value_facts.clone();
                facts = ucp_result.facts;
                if let Some(value) = query_output.value {
                    value_facts.mark_known(query_cell.clone(), value);
                }
                // Értékméretkorlát vagy ismeretlen publikus érték esetén nem feltétlenül állít vissza konkrét értéket.
                queried_cells.insert(query_cell.clone());
                if facts.mark_unique(query_cell.clone()) {
                    smt_learned_cells.push(query_cell);
                }
            }
            SemanticQueryResult::NotUnique => {
                // Célcellára kapott ellenpéldánál alulkényszerezettséget jelez.
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
                // A nemegyértelmű köztes advice cellát megjegyzi, és nem kérdezi le újra.
                queried_cells.insert(query_cell);
                value_facts = ucp_result.value_facts.clone();
                facts = ucp_result.facts;
            }
            SemanticQueryResult::Overconstrained => {
                // Az SMT következetlenségi jelzését külön kezeli, nem UCP-döntésként jelenti.
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
                // Bizonytalan SMT-eredménynél más cellával folytatja a keresést.
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

    // A teszt egyszerű, szelektorral vezérelt, tisztán UCP-vel megoldható kapcsolást állít elő.
    #[derive(Clone, Debug)]
    struct PipelineConfig {
        advice: Column<Advice>,
        selector: Selector,
    }

    // A teszt a kapcsolás privát értékeit tárolja ebben a példányban.
    #[derive(Clone, Debug, Default)]
    struct PipelineCircuit {
        _marker: PhantomData<Fr>,
    }

    // A teszt olyan konfigurációt készít, amelynek célcelláját az alap UCP nem határozza meg.
    #[derive(Clone, Debug)]
    struct SmtOnlyConfig {
        advice: Column<Advice>,
    }

    // A teszt az egyértelműségi tényt SMT-vizsgálattal állapítja meg.
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

    // A teszt páratlan hosszú x_i+x_(i+1)=2 ciklust készít, amelynek egyetlen megoldása mindenhol 1.
    impl Circuit<Fr> for LargeLinearCircuit {
        type Config = LargeLinearConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            // A 129 cellás ciklus meghaladja a domainelimináció 128 oszlopos keretét is.
            let cells: Vec<_> = (0..129).map(|_| meta.advice_column()).collect();
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

            // A teszt szelektorral aktiválja az advice + public - 5 = 0 kaput.
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
                    // Aktiválja a kaput az adott soron.
                    config.selector.enable(&mut region, 0)?;
                    // A teszt public=2 mellett 3 értéket rendel az advice cellához, így a kényszer teljesül.
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

            // A teszt (x-1)^2 = 0 polinomot készít, amelyből az SMT x=1-et igazol.
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
                    // A teszt az x=1 gyököt rendeli a cellához.
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

    // A teszt ellenőrzi, hogy tisztán UCP-vel igazolt céloknál nem indít SMT-vizsgálatot.
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

    // A teszt ellenőrzi az igazolt advice-egyértelműség átadását rögzített változóként.
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

    // A teszt ellenőrzi, hogy az egyelemű Delta-domaint SMT-állításként is átadja.
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

    // A teszt a teljes UCP -> SMT -> K-frissítés visszacsatolást ellenőrzi.
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

    // A teszt K-tagság mellett is ellenőrzi a konkrét értéket, és nem feltételezi a modell többi értékét.
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

        // A teszt rögzíti mindkét publikus értéket; az SMT a kényszerekből, nem a privát értékadásból következtet.
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

    // A teszt visszaállítási útja egy SMT-értékből mind a 65 Delta-értéket megtanulja.
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
        for column in 0..129 {
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
