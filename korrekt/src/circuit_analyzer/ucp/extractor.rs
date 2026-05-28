use super::{
    cell::{CellId, CellKind},
    expr::UcpExpr,
    facts::UcpFacts,
};

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
use super::{
    facts::initial_facts_from_expressions,
    plonkish::{expression_to_ucp_expr_with_fixed_values, field_to_bigint},
    value::{infer_domains_from_expression_domain_with_modulus, UcpValueDomain, UcpValueFacts},
};
#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
use crate::circuit_analyzer::{
    analyzable::{Analyzable, AnalyzableField},
    halo2_proofs_libs::*,
};
#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
use num::Num;
use num_bigint::BigInt;
use std::collections::BTreeSet;
#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
use std::collections::HashSet;

//Egy teljes UCP bemenet: constraint expressionök, kezdeti K, outputok, witnessek és field modulus
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UcpProblem {
    pub expressions: Vec<UcpExpr>,
    pub initial_facts: UcpFacts,
    //A régi név kompatibilitás miatt marad: ugyanaz, mint az output_cells
    pub target_cells: Vec<CellId>,
    //O halmaz: azok az output/target cellák, amelyek constrained voltát végül bizonyítani akarjuk
    pub output_cells: Vec<CellId>,
    //W halmaz: a constraint rendszerben szereplő witness/advice cellák
    pub witness_cells: Vec<CellId>,
    //Delta kezdeti része: lookup/range table domainekből tanult értékhalmazok
    pub initial_value_facts: UcpValueFacts,
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
    //O: a caller által megadott output/target cellák
    let output_cells = dedup_cells_preserving_order(target_cells);
    //W: a circuitben assignolt és/vagy constraintben hivatkozott advice cellák
    let witness_cells = witness_cells_from_analyzable(analyzable, &expressions);
    //Delta: lookup táblákból biztonságosan kinyerhető finite domainek
    let initial_value_facts = extract_lookup_value_facts(analyzable);

    UcpProblem {
        expressions,
        initial_facts,
        target_cells: output_cells.clone(),
        output_cells,
        witness_cells,
        initial_value_facts,
        field_modulus: field_modulus::<F>(),
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
//Lookup argumentekből kezdeti Delta domaineket tanul.
//A table oldal konkrét assigned fixed/table értékek véges halmaza.
//Az input lehet sima advice cella vagy egyszerű lineáris expression, például x + 1 vagy 2*x.
pub fn extract_lookup_value_facts<F: AnalyzableField>(analyzable: &Analyzable<F>) -> UcpValueFacts {
    let mut values = UcpValueFacts::new();
    let field_modulus = field_modulus::<F>();

    for region in &analyzable.regions {
        if !region_has_advice_cell(region) {
            continue;
        }

        let Some((region_begin, region_end)) = region.rows else {
            continue;
        };

        for absolute_row in region_begin..=region_end {
            let row = i32::try_from(absolute_row - region_begin)
                .expect("UCP local row does not fit into i32");

            for lookup in &analyzable.cs.lookups {
                for (input_expr, table_expr) in lookup
                    .input_expressions
                    .iter()
                    .zip(lookup.table_expressions.iter())
                {
                    let Some(domain) = lookup_table_domain(table_expr, &analyzable.fixed) else {
                        continue;
                    };

                    let input = expression_to_ucp_expr_with_fixed_values(
                        input_expr,
                        region_begin,
                        row,
                        &analyzable.fixed,
                    );

                    for (cell, inferred_domain) in infer_domains_from_expression_domain_with_modulus(
                        &input,
                        &domain,
                        &values,
                        &field_modulus,
                    ) {
                        if matches!(&cell.kind, CellKind::Advice) {
                            values.mark_domain(cell, inferred_domain);
                        }
                    }
                }
            }
        }
    }

    values
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
fn region_has_advice_cell(region: &Region) -> bool {
    #[cfg(feature = "use_zcash_halo2_proofs")]
    {
        region
            .cells
            .iter()
            .any(|(column, row)| assigned_advice_cell_id(column, *row).is_some())
    }

    #[cfg(any(
        feature = "use_pse_halo2_proofs",
        feature = "use_axiom_halo2_proofs",
        feature = "use_scroll_halo2_proofs"
    ))]
    {
        region
            .cells
            .iter()
            .any(|((column, row), _)| assigned_advice_cell_id(column, *row).is_some())
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
fn lookup_table_domain<F: AnalyzableField>(
    expr: &Expression<F>,
    fixed_values: &[Vec<CellValue<F>>],
) -> Option<UcpValueDomain> {
    let Expression::Fixed(query) = expr else {
        return None;
    };

    //A Halo2 table expression normál esetben Rotation::cur(); ettől eltérő fixed expressiont
    //nem kezelünk range-domain táblaként.
    if query.rotation != Rotation::cur() {
        return None;
    }

    let column_values = fixed_values.get(query.column_index)?;
    let mut domain_values = Vec::with_capacity(column_values.len());

    for value in column_values {
        match value {
            CellValue::Assigned(value) => domain_values.push(field_to_bigint(value)),
            //Lookup table domainhez csak ténylegesen assignolt table értékeket veszünk fel.
            //Az Unassigned itt nem bizonyított table entry, ezért nem tanulunk belőle nullát.
            CellValue::Unassigned => {}
            //Poison nem valódi table érték; ilyenkor inkább semmit nem tanulunk.
            CellValue::Poison(_) => return None,
        }
    }

    UcpValueDomain::finite_set(domain_values)
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
//Analyzable circuitből és expressionökből kigyűjti a W halmazt
pub fn witness_cells_from_analyzable<F: AnalyzableField>(
    analyzable: &Analyzable<F>,
    expressions: &[UcpExpr],
) -> Vec<CellId> {
    let mut cells = BTreeSet::new();

    for region in &analyzable.regions {
        collect_region_witness_cells(region, &mut cells);
    }

    for expr in expressions {
        collect_witness_cells(expr, &mut cells);
    }

    cells.into_iter().collect()
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
fn collect_region_witness_cells(region: &Region, cells: &mut BTreeSet<CellId>) {
    #[cfg(feature = "use_zcash_halo2_proofs")]
    {
        for (column, row) in &region.cells {
            if let Some(cell) = assigned_advice_cell_id(column, *row) {
                cells.insert(cell);
            }
        }
    }

    #[cfg(any(
        feature = "use_pse_halo2_proofs",
        feature = "use_axiom_halo2_proofs",
        feature = "use_scroll_halo2_proofs"
    ))]
    {
        for ((column, row), _) in &region.cells {
            if let Some(cell) = assigned_advice_cell_id(column, *row) {
                cells.insert(cell);
            }
        }
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
fn assigned_advice_cell_id(column: &Column<Any>, row: usize) -> Option<CellId> {
    let row = i32::try_from(row).ok()?;

    #[cfg(feature = "use_zcash_halo2_proofs")]
    {
        match column.column_type() {
            Any::Advice => Some(CellId::advice(column.index, row)),
            Any::Fixed | Any::Instance => None,
        }
    }

    #[cfg(any(
        feature = "use_pse_halo2_proofs",
        feature = "use_axiom_halo2_proofs",
        feature = "use_scroll_halo2_proofs"
    ))]
    {
        match column.column_type() {
            Any::Advice(_) => Some(CellId::advice(column.index, row)),
            Any::Fixed | Any::Instance => None,
        }
    }
}

//Expression listából kigyűjti a W halmaz expressionökben hivatkozott részét
pub fn witness_cells_from_expressions(expressions: &[UcpExpr]) -> Vec<CellId> {
    let mut cells = BTreeSet::new();

    for expr in expressions {
        collect_witness_cells(expr, &mut cells);
    }

    cells.into_iter().collect()
}

fn collect_witness_cells(expr: &UcpExpr, cells: &mut BTreeSet<CellId>) {
    match expr {
        UcpExpr::Var(cell) => {
            if matches!(cell.kind, CellKind::Advice) {
                cells.insert(cell.clone());
            }
        }
        UcpExpr::Const(_) => {}
        UcpExpr::Neg(inner) | UcpExpr::Scale(inner, _) => collect_witness_cells(inner, cells),
        UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
            collect_witness_cells(left, cells);
            collect_witness_cells(right, cells);
        }
    }
}

fn dedup_cells_preserving_order<I>(cells: I) -> Vec<CellId>
where
    I: IntoIterator<Item = CellId>,
{
    let mut seen = BTreeSet::new();
    let mut unique_cells = Vec::new();

    for cell in cells {
        if seen.insert(cell.clone()) {
            unique_cells.push(cell);
        }
    }

    unique_cells
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
            value::{initial_values_from_instance_cells, UcpValueDomain, UcpValueFacts},
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

    //Lookup/range-check teszt circuit: selector * advice szerepel egy 0..3 lookup táblában
    #[derive(Clone, Debug)]
    struct LookupRangeConfig {
        advice: Column<Advice>,
        selector: Selector,
        table: TableColumn,
    }

    #[derive(Clone, Debug, Default)]
    struct LookupRangeCircuit {
        _marker: PhantomData<Fr>,
    }

    //Lookup/range-check teszt circuit, ahol a lookup input egy skálázott advice expression: 2*x
    #[derive(Clone, Debug)]
    struct ScaledLookupRangeConfig {
        advice: Column<Advice>,
        selector: Selector,
        table: TableColumn,
    }

    #[derive(Clone, Debug, Default)]
    struct ScaledLookupRangeCircuit {
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

    impl Circuit<Fr> for LookupRangeCircuit {
        type Config = LookupRangeConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let advice = meta.advice_column();
            let selector = meta.complex_selector();
            let table = meta.lookup_table_column();

            meta.lookup(|meta| {
                let selector = meta.query_selector(selector);
                let value = meta.query_advice(advice, Rotation::cur());

                vec![(selector * value, table)]
            });

            LookupRangeConfig {
                advice,
                selector,
                table,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            layouter.assign_table(
                || "range table",
                |mut table| {
                    for value in 0..4 {
                        table.assign_cell(
                            || "range value",
                            config.table,
                            value,
                            || Value::known(Fr::from(value as u64)),
                        )?;
                    }
                    Ok(())
                },
            )?;

            layouter.assign_region(
                || "lookup input",
                |mut region| {
                    config.selector.enable(&mut region, 0)?;
                    region.assign_advice(
                        || "range checked advice",
                        config.advice,
                        0,
                        || Value::known(Fr::from(2)),
                    )?;
                    Ok(())
                },
            )
        }
    }

    impl Circuit<Fr> for ScaledLookupRangeCircuit {
        type Config = ScaledLookupRangeConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let advice = meta.advice_column();
            let selector = meta.complex_selector();
            let table = meta.lookup_table_column();

            meta.lookup(|meta| {
                let selector = meta.query_selector(selector);
                let value = meta.query_advice(advice, Rotation::cur());
                let scaled_value = Expression::Constant(Fr::from(2)) * value;

                vec![(selector * scaled_value, table)]
            });

            ScaledLookupRangeConfig {
                advice,
                selector,
                table,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            layouter.assign_table(
                || "scaled range table",
                |mut table| {
                    for (row, value) in [0u64, 2, 4].into_iter().enumerate() {
                        table.assign_cell(
                            || "scaled range value",
                            config.table,
                            row,
                            || Value::known(Fr::from(value)),
                        )?;
                    }
                    Ok(())
                },
            )?;

            layouter.assign_region(
                || "scaled lookup input",
                |mut region| {
                    config.selector.enable(&mut region, 0)?;
                    region.assign_advice(
                        || "scaled range checked advice",
                        config.advice,
                        0,
                        || Value::known(Fr::from(2)),
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
        assert_eq!(problem.output_cells, vec![target.clone()]);
        assert!(problem.witness_cells.contains(&target));
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

        assert_eq!(problem.output_cells, vec![target.clone()]);
        assert!(problem.witness_cells.contains(&target));

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

        assert_eq!(
            problem.output_cells,
            vec![inactive_advice.clone(), active_advice.clone()]
        );
        assert!(problem.witness_cells.contains(&inactive_advice));
        assert!(problem.witness_cells.contains(&active_advice));

        let result = analyze_expressions_with_values_and_modulus(
            &problem.expressions,
            problem.initial_facts,
            UcpValueFacts::new(),
            &problem.field_modulus,
        );

        assert!(!result.facts.is_unique(&inactive_advice));
        assert!(result.facts.is_unique(&active_advice));
    }

    //Azt ellenőrzi, hogy lookup táblából finite Delta domain készül a range-checkelt advice cellára
    #[test]
    fn extracts_lookup_table_domain_for_active_range_checked_advice() {
        use zcash_halo2_proofs::dev::MockProver;

        let circuit = LookupRangeCircuit::default();
        let k = 4;
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

        let analyzable = Analyzable::config_and_synthesize(&circuit, k).unwrap();
        let target = CellId::advice(0, 0);
        let problem = extract_ucp_problem_with_targets(&analyzable, [target.clone()]);
        let expected_domain =
            UcpValueDomain::finite_set((0..4).map(BigInt::from)).expect("non-empty range domain");

        assert_eq!(
            problem.initial_value_facts.domain(&target),
            Some(&expected_domain)
        );

        let result = analyze_expressions_with_values_and_modulus(
            &problem.expressions,
            problem.initial_facts,
            problem.initial_value_facts,
            &problem.field_modulus,
        );

        assert!(result.value_facts.domain_is_subset_of_range(
            &target,
            &BigInt::from(0),
            &BigInt::from(3)
        ));
        assert!(!result.facts.is_unique(&target));
    }

    //Azt ellenőrzi, hogy lookup input expressionből is tanulunk domaint: 2*x in {0,2,4} => x in {0,1,2}
    #[test]
    fn extracts_lookup_domain_from_scaled_input_expression() {
        use zcash_halo2_proofs::dev::MockProver;

        let circuit = ScaledLookupRangeCircuit::default();
        let k = 4;
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

        let analyzable = Analyzable::config_and_synthesize(&circuit, k).unwrap();
        let target = CellId::advice(0, 0);
        let problem = extract_ucp_problem_with_targets(&analyzable, [target.clone()]);
        let expected_domain =
            UcpValueDomain::finite_set((0..3).map(BigInt::from)).expect("non-empty range domain");

        assert_eq!(
            problem.initial_value_facts.domain(&target),
            Some(&expected_domain)
        );
    }

    //Azt ellenőrzi, hogy poisonos lookup table-ből nem tanulunk túl szűk Delta domaint
    #[test]
    fn lookup_table_domain_does_not_learn_from_poisoned_table() {
        use zcash_halo2_proofs::dev::MockProver;

        let circuit = LookupRangeCircuit::default();
        let k = 4;
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

        let mut analyzable = Analyzable::config_and_synthesize(&circuit, k).unwrap();
        let Expression::Fixed(query) = &analyzable.cs.lookups[0].table_expressions[0] else {
            panic!("test lookup table should be a fixed/table column");
        };
        analyzable.fixed[query.column_index][0] = CellValue::Poison(0);

        let target = CellId::advice(0, 0);
        let problem = extract_ucp_problem_with_targets(&analyzable, [target.clone()]);

        assert_eq!(problem.initial_value_facts.domain(&target), None);
    }
}
