use super::{cell::CellId, expr::UcpExpr, facts::UcpFacts};

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
use super::{
    facts::initial_facts_from_expressions, plonkish::expression_to_ucp_expr_with_fixed_values,
};
#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
use crate::circuit_analyzer::{
    analyzable::{Analyzable, AnalyzableField},
    halo2_proofs_libs::*,
};
#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
use num::Num;
use num_bigint::BigInt;
#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
use std::collections::HashSet;

//Egy teljes UCP bemenet: constraint expressionök, kezdeti K és ellenőrizendő target cellák
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UcpProblem {
    pub expressions: Vec<UcpExpr>,
    pub initial_facts: UcpFacts,
    pub target_cells: Vec<CellId>,
    pub field_modulus: BigInt,
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
//Analyzable circuitből UCP problem létrehozása targetek nélkül
pub fn extract_ucp_problem<F: AnalyzableField>(analyzable: &Analyzable<F>) -> UcpProblem {
    extract_ucp_problem_with_targets(analyzable, [])
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
//Analyzable circuitből UCP problem létrehozása megadott target cellákkal
pub fn extract_ucp_problem_with_targets<F, I>(
    analyzable: &Analyzable<F>,
    target_cells: I,
) -> UcpProblem
where
    F: AnalyzableField,
    I: IntoIterator<Item = CellId>,
{
    let expressions = extract_ucp_expressions(analyzable);
    //Az expressionökben szereplő instance/fixed cellákból indul a K halmaz
    let initial_facts = initial_facts_from_expressions(&expressions);

    UcpProblem {
        expressions,
        initial_facts,
        target_cells: target_cells.into_iter().collect(),
        field_modulus: field_modulus::<F>(),
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
//A circuit mezőjének p modulusát adja vissza BigInt-ként
pub fn field_modulus<F: AnalyzableField>() -> BigInt {
    parse_field_modulus(F::MODULUS)
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
fn parse_field_modulus(raw_modulus: &str) -> BigInt {
    if let Some(hex) = raw_modulus.strip_prefix("0x") {
        BigInt::from_str_radix(hex, 16).expect("field modulus hex string must parse")
    } else {
        BigInt::from_str_radix(raw_modulus, 10).expect("field modulus decimal string must parse")
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
//Kiszed minden UCP zero-equation expressiont a gate-ekből és copy constraint-ekből
pub fn extract_ucp_expressions<F: AnalyzableField>(analyzable: &Analyzable<F>) -> Vec<UcpExpr> {
    let mut expressions = Vec::new();

    //Végigmegyünk az analyzable által rögzített régiókon
    for region in &analyzable.regions {
        //Sor nélküli régióból nem tudunk konkrét UCP cellákat képezni
        let Some((region_begin, region_end)) = region.rows else {
            continue;
        };

        //Ha vannak selectorok, de ebben a régióban egyik sincs engedélyezve, kihagyjuk
        if !analyzable.selectors.is_empty() && region.enabled_selectors.is_empty() {
            continue;
        }

        //A régió minden abszolút sorára külön kiértékeljük az aktív gate-eket
        for absolute_row in region_begin..=region_end {
            //Selectoros circuitnél csak olyan sort nézünk, ahol legalább egy selector aktív
            if !analyzable.selectors.is_empty() && !row_has_enabled_selector(region, absolute_row) {
                continue;
            }

            //A Halo2 expression konverzió lokális sort vár a region_begin-hez képest
            let row = i32::try_from(absolute_row - region_begin)
                .expect("UCP local row does not fit into i32");
            //Minden gate minden polynomial constraintjét UCP expressionné alakítjuk
            for gate in &analyzable.cs.gates {
                for poly in &gate.polys {
                    expressions.push(expression_to_ucp_expr_with_fixed_values(
                        poly,
                        region_begin,
                        row,
                        &analyzable.fixed,
                    ));
                }
            }
        }
    }

    //A permutation/copy constraint-ekből is zero-equation expressionöket készítünk
    expressions.extend(extract_copy_constraint_expressions(&analyzable.permutation));

    expressions
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
//Copy/permutation constraint-ekből A - B = 0 alakú UCP expressionöket készít
fn extract_copy_constraint_expressions(
    permutation: &permutation::keygen::Assembly,
) -> Vec<UcpExpr> {
    let mut expressions = Vec::new();
    //Ugyanazt az élt ne vegyük fel többször
    let mut seen_edges = HashSet::new();

    //Bejárjuk a permutation mappingben szereplő oszlopokat és sorokat
    for col in 0..permutation.sizes.len() {
        for row in 0..permutation.sizes[col].len() {
            let cycle_len = permutation.sizes[col][row];
            //Egyelemű cycle nem jelent valódi copy constraint-et
            if cycle_len <= 1 {
                continue;
            }

            let mut cycle_col = col;
            let mut cycle_row = row;

            //A permutation cycle mentén minden szomszédos kapcsolatból egyenlőséget készítünk
            for _ in 0..cycle_len {
                let (right_col, right_row) = permutation.mapping[cycle_col][cycle_row];

                let Some(left) = permutation_cell_id(permutation, cycle_col, cycle_row) else {
                    break;
                };
                let Some(right) = permutation_cell_id(permutation, right_col, right_row) else {
                    break;
                };

                //left == right constraint UCP-ben: left - right = 0
                if left != right && seen_edges.insert((left.clone(), right.clone())) {
                    expressions.push(UcpExpr::add(
                        UcpExpr::var(left),
                        UcpExpr::neg(UcpExpr::var(right)),
                    ));
                }

                cycle_col = right_col;
                cycle_row = right_row;
            }
        }
    }

    expressions
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
//Permutation oszlop/sor pozícióból UCP CellId-t készít
fn permutation_cell_id(
    permutation: &permutation::keygen::Assembly,
    col: usize,
    row: usize,
) -> Option<CellId> {
    let column = permutation.columns.get(col)?;
    let row = i32::try_from(row).ok()?;

    #[cfg(feature = "use_zcash_halo2_proofs")]
    {
        //Zcash halo2-ben az Any variánsok nem hordoznak plusz adatot
        match column.column_type() {
            Any::Advice => Some(CellId::advice(column.index, row)),
            Any::Fixed => Some(CellId::fixed(column.index, row)),
            Any::Instance => Some(CellId::instance(column.index, row)),
        }
    }

    #[cfg(any(
        feature = "use_pse_halo2_proofs",
        feature = "use_axiom_halo2_proofs",
        feature = "use_scroll_halo2_proofs"
    ))]
    {
        //Más halo2 forkokban az Advice variáns hordozhat plusz adatot
        match column.column_type() {
            Any::Advice(_) => Some(CellId::advice(column.index, row)),
            Any::Fixed => Some(CellId::fixed(column.index, row)),
            Any::Instance => Some(CellId::instance(column.index, row)),
        }
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
//Megmondja, hogy az adott abszolút sorban van-e engedélyezett selector
fn row_has_enabled_selector(region: &Region, absolute_row: usize) -> bool {
    region
        .enabled_selectors
        .values()
        .any(|rows| rows.contains(&absolute_row))
}

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod tests {
    use super::*;
    use crate::circuit_analyzer::{
        analyzable::Analyzable,
        ucp::{
            cell::CellId,
            engine::{
                analyze_expressions, analyze_expressions_with_values,
                analyze_expressions_with_values_and_modulus,
            },
            value::{initial_values_from_instance_cells, UcpValueFacts},
        },
    };
    use num_bigint::BigInt;
    use std::collections::HashMap;
    use std::marker::PhantomData;

    //Teszt circuit egy aktív selectoros assignment gate-hez
    #[derive(Clone, Debug)]
    struct ExtractorConfig {
        advice: Column<Advice>,
        selector: Selector,
    }

    #[derive(Clone, Debug, Default)]
    struct ExtractorCircuit {
        _marker: PhantomData<Fr>,
    }

    //Teszt circuit copy constraint ellenőrzéséhez
    #[derive(Clone, Debug)]
    struct CopyConfig {
        advice: Column<Advice>,
        instance: Column<Instance>,
    }

    #[derive(Clone, Debug, Default)]
    struct CopyCircuit {
        _marker: PhantomData<Fr>,
    }

    //Két selectoros teszt circuit, ahol csak a második gate aktív
    #[derive(Clone, Debug)]
    struct CompressedSelectorConfig {
        advice_a: Column<Advice>,
        advice_b: Column<Advice>,
        selector_b: Selector,
    }

    #[derive(Clone, Debug, Default)]
    struct CompressedSelectorCircuit {
        _marker: PhantomData<Fr>,
    }

    impl Circuit<Fr> for ExtractorCircuit {
        type Config = ExtractorConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let advice = meta.advice_column();
            let instance = meta.instance_column();
            let selector = meta.selector();

            //Constraint: selector * (advice + public - 5) = 0
            meta.create_gate("extractor selected assignment", |meta| {
                let selector = meta.query_selector(selector);
                let advice = meta.query_advice(advice, Rotation::cur());
                let public = meta.query_instance(instance, Rotation::cur());

                vec![selector * (advice + public - Expression::Constant(Fr::from(5)))]
            });

            ExtractorConfig { advice, selector }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "extractor row",
                |mut region| {
                    //A gate csak ezen a soron aktív
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

    impl Circuit<Fr> for CopyCircuit {
        type Config = CopyConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let advice = meta.advice_column();
            let instance = meta.instance_column();

            //Equality engedélyezése kell a copy/permutation constraintekhez
            meta.enable_equality(advice);
            meta.enable_equality(instance);

            CopyConfig { advice, instance }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            //Advice cellát hozzárendeljük egy instance cellához
            let advice_cell = layouter.assign_region(
                || "copy row",
                |mut region| {
                    region.assign_advice(
                        || "copied advice",
                        config.advice,
                        0,
                        || Value::known(Fr::from(2)),
                    )
                },
            )?;

            layouter.constrain_instance(advice_cell.cell(), config.instance, 0)
        }
    }

    impl Circuit<Fr> for CompressedSelectorCircuit {
        type Config = CompressedSelectorConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let advice_a = meta.advice_column();
            let advice_b = meta.advice_column();
            let instance = meta.instance_column();
            let selector_a = meta.selector();
            let selector_b = meta.selector();

            meta.create_gate("first selected assignment", |meta| {
                let selector = meta.query_selector(selector_a);
                let advice = meta.query_advice(advice_a, Rotation::cur());
                let public = meta.query_instance(instance, Rotation::cur());

                vec![selector * (advice + public - Expression::Constant(Fr::from(5)))]
            });

            meta.create_gate("second selected assignment", |meta| {
                let selector = meta.query_selector(selector_b);
                let advice = meta.query_advice(advice_b, Rotation::cur());
                let public = meta.query_instance(instance, Rotation::cur());

                vec![selector * (advice + public - Expression::Constant(Fr::from(7)))]
            });

            CompressedSelectorConfig {
                advice_a,
                advice_b,
                selector_b,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "compressed selector row",
                |mut region| {
                    //Csak a második selector aktív ezen a soron
                    config.selector_b.enable(&mut region, 0)?;
                    region.assign_advice(
                        || "inactive advice",
                        config.advice_a,
                        0,
                        || Value::known(Fr::from(11)),
                    )?;
                    region.assign_advice(
                        || "active advice",
                        config.advice_b,
                        0,
                        || Value::known(Fr::from(5)),
                    )?;
                    Ok(())
                },
            )
        }
    }

    //Azt ellenőrzi, hogy Analyzable circuitből UCP problem készül és UCP lefut rajta
    #[test]
    fn extracts_problem_from_analyzable_and_runs_ucp() {
        use zcash_halo2_proofs::dev::MockProver;
        let circuit = ExtractorCircuit::default();
        let k = 4;

        let public_inputs = vec![vec![Fr::from(2)]];
        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();

        prover.assert_satisfied();
        let analyzable = Analyzable::config_and_synthesize(&circuit, 4).unwrap();

        let target = CellId::advice(0, 0);
        let problem = extract_ucp_problem_with_targets(&analyzable, [target.clone()]);

        assert!(!problem.expressions.is_empty());
        assert_eq!(problem.target_cells, vec![target.clone()]);
        assert_eq!(problem.field_modulus, field_modulus::<Fr>());
        assert!(problem.initial_facts.is_unique(&CellId::instance(0, 0)));
        assert!(!problem.initial_facts.is_unique(&target));

        let result = analyze_expressions(&problem.expressions, problem.initial_facts);
        let target_check = result.check_targets(&problem.target_cells);

        assert!(result.facts.is_unique(&target));
        assert!(result.all_targets_unique(&problem.target_cells));
        assert!(target_check.all_targets_unique());
        assert_eq!(target_check.checked_targets, 1);
        assert_eq!(target_check.unique_targets, 1);
        assert!(result.all_expressions_unique());
    }

    //Azt ellenőrzi, hogy copy constraintből UCP egyenlet készül, és abból advice érték tanulható
    #[test]
    fn extracts_copy_constraints_and_value_facts_can_learn_copied_advice() {
        use zcash_halo2_proofs::dev::MockProver;

        let circuit = CopyCircuit::default();
        let k = 4;
        let public_inputs = vec![vec![Fr::from(2)]];
        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        prover.assert_satisfied();

        let analyzable = Analyzable::config_and_synthesize(&circuit, k).unwrap();
        let target = CellId::advice(0, 0);
        let problem = extract_ucp_problem_with_targets(&analyzable, [target.clone()]);

        let mut instance_cells = HashMap::new();
        instance_cells.insert("I-0-0".to_string(), 2);
        let value_facts = initial_values_from_instance_cells(instance_cells.iter());

        let result = analyze_expressions_with_values(
            &problem.expressions,
            problem.initial_facts,
            value_facts,
        );

        assert!(result.facts.is_unique(&target));
        assert_eq!(
            result.value_facts.known_value(&target),
            Some(&BigInt::from(2))
        );
    }

    //Azt ellenőrzi, hogy kompresszált selector fixed értéknél csak az aktív gate-ből tanulunk
    #[test]
    fn extracts_compressed_selectors_using_actual_fixed_values() {
        use zcash_halo2_proofs::dev::MockProver;

        let circuit = CompressedSelectorCircuit::default();
        let k = 4;
        let public_inputs = vec![vec![Fr::from(2)]];
        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        prover.assert_satisfied();

        let analyzable = Analyzable::config_and_synthesize(&circuit, k).unwrap();
        let inactive_advice = CellId::advice(0, 0);
        let active_advice = CellId::advice(1, 0);
        let problem = extract_ucp_problem_with_targets(
            &analyzable,
            [inactive_advice.clone(), active_advice.clone()],
        );

        let result = analyze_expressions_with_values_and_modulus(
            &problem.expressions,
            problem.initial_facts,
            UcpValueFacts::new(),
            &problem.field_modulus,
        );

        assert!(!result.facts.is_unique(&inactive_advice));
        assert!(result.facts.is_unique(&active_advice));
    }
}
