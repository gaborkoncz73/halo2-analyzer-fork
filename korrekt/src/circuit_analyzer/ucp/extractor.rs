//! A Halo2-struktúrából összeállítja az UCP bemenetét: egyenletek, cellák és kezdeti tények.
//! A lookupokat külön modulban gyűjti ki, majd az eredményüket a teljes problémához kapcsolja.

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
#[path = "lookup_extractor.rs"]
mod lookup_extraction;
#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
use super::value::MAX_FINITE_DOMAIN_SIZE;
#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
pub use lookup_extraction::{extract_lookup_expression_domains, extract_lookup_value_facts};
#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
use lookup_extraction::{extract_lookup_relations, lookup_values_from_domains};

use super::{
    cell::{CellId, CellKind},
    expr::{UcpExpr, UcpScalar},
    facts::UcpFacts,
    lookup::UcpLookup,
    value::{UcpValueDomain, UcpValueFacts},
};

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
use super::{
    facts::initial_facts_from_expressions,
    plonkish::{expression_to_ucp_expr_with_fixed_values, field_to_bigint, query_row},
    value::normalize_field_value,
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

// Egy UCP-bemenetben fogja össze a kifejezéseket, kezdeti tényeket, cellákat és testmodulust.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UcpProblem {
    pub expressions: Vec<UcpExpr>,
    /// A szükséges véges lookup-vetületeket tárolja, a teljes relációként túl nagy táblákhoz is.
    pub expression_domains: Vec<(UcpExpr, UcpValueDomain)>,
    pub lookups: Vec<UcpLookup>,
    pub initial_facts: UcpFacts,
    // Az output_cells másolatát tartalmazza; a target_cells elérési utat kompatibilitásból biztosítja.
    pub target_cells: Vec<CellId>,
    // Az O halmazban a bizonyítandóan egyértelmű kimeneti célcellákat tárolja.
    pub output_cells: Vec<CellId>,
    // A W halmazban a kényszerrendszerben szereplő advice cellákat tárolja.
    pub witness_cells: Vec<CellId>,
    // A kezdeti Deltában a lookup-táblákból kinyert értékhalmazokat tárolja.
    pub initial_value_facts: UcpValueFacts,
    pub field_modulus: BigInt,
}

impl UcpProblem {
    pub(crate) fn simulate_with_values(
        &self,
        facts: UcpFacts,
        values: UcpValueFacts,
    ) -> super::engine::UcpResult {
        super::engine::simulate_expressions_with_relations_and_modulus(
            &self.expressions,
            &self.expression_domains,
            &self.lookups,
            facts,
            values,
            &self.field_modulus,
        )
    }

    /// Minden propagációs körben megtartja a lookup-tagságokat, az SMT-értékek visszacsatolásakor is.
    pub fn analyze_with_values(
        &self,
        facts: UcpFacts,
        values: UcpValueFacts,
    ) -> super::engine::UcpResult {
        super::engine::analyze_expressions_with_relations_and_modulus(
            &self.expressions,
            &self.expression_domains,
            &self.lookups,
            facts,
            values,
            &self.field_modulus,
        )
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
// Az Analyzable kapcsolásból külön célcellák nélkül állít elő UCP-problémát.
pub fn extract_ucp_problem<F: AnalyzableField>(analyzable: &Analyzable<F>) -> UcpProblem {
    extract_ucp_problem_with_targets(analyzable, [])
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
// Az Analyzable kapcsolásból a megadott célcellákkal állít elő UCP-problémát.
pub fn extract_ucp_problem_with_targets<F, I>(
    analyzable: &Analyzable<F>,
    target_cells: I,
) -> UcpProblem
where
    F: AnalyzableField,
    I: IntoIterator<Item = CellId>,
{
    let expressions = extract_ucp_expressions(analyzable);
    // A kifejezések instance és fixed celláiból inicializálja K-t.
    let expression_domains = extract_lookup_expression_domains(analyzable);
    let lookups = extract_lookup_relations(analyzable);
    let mut initial_facts = initial_facts_from_expressions(&expressions);
    for (expr, _) in &expression_domains {
        for cell in initial_facts_from_expressions(std::slice::from_ref(expr)).unique_cells() {
            initial_facts.mark_unique(cell.clone());
        }
    }
    // Az O halmazt a hívó által megadott kimeneti célcellákból állítja össze.
    let output_cells = dedup_cells_preserving_order(target_cells);
    // A W halmazba felveszi a hozzárendelt vagy kényszerben hivatkozott advice cellákat.
    let mut witnesses: BTreeSet<_> = witness_cells_from_analyzable(analyzable, &expressions)
        .into_iter()
        .collect();
    for (expr, _) in &expression_domains {
        collect_witness_cells(expr, &mut witnesses);
    }
    for lookup in &lookups {
        for expr in lookup.inputs() {
            collect_witness_cells(expr, &mut witnesses);
        }
    }
    let witness_cells = witnesses.into_iter().collect();
    // A lookup-táblákból biztonságosan kinyerhető véges domaineket bejegyzi Deltába.
    let modulus = field_modulus::<F>();
    let mut initial_value_facts = lookup_values_from_domains(&expression_domains, &modulus);
    // A másolási egyenletek fixed celláira csak ténylegesen hozzárendelt értékből jegyez be nyilvános konstanst.
    for cell in initial_facts.unique_cells() {
        if cell.kind != CellKind::Fixed {
            continue;
        }
        let Some(value) = usize::try_from(cell.row).ok().and_then(|row| {
            analyzable
                .fixed
                .get(cell.column)
                .and_then(|column| column.get(row))
        }) else {
            continue;
        };
        if let CellValue::Assigned(value) = value {
            if let Some(value) = normalize_field_value(field_to_bigint(value), &modulus) {
                initial_value_facts.mark_known(cell.clone(), value);
            }
        }
    }

    UcpProblem {
        expressions,
        expression_domains,
        lookups,
        initial_facts,
        target_cells: output_cells.clone(),
        output_cells,
        witness_cells,
        initial_value_facts,
        field_modulus: modulus,
    }
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
// Az Analyzable kapcsolásból és a kifejezésekből kigyűjti a W halmazt.
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

// A kifejezésekből kigyűjti a W halmazban hivatkozott cellákat.
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
// BigInt alakban visszaadja a kapcsolás testének p modulusát.
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
// A kapukból és a másolási kényszerekből kigyűjti a nullával egyenlő UCP-kifejezéseket.
pub fn extract_ucp_expressions<F: AnalyzableField>(analyzable: &Analyzable<F>) -> Vec<UcpExpr> {
    let mut expressions = Vec::new();

    // A kapukat minden használható soron vizsgálja, a régió- és szelektormetaadatoktól függetlenül.
    let region_begin = 0;
    for absolute_row in analyzable.usable_rows.clone() {
        let row = i32::try_from(absolute_row).expect("UCP absolute row does not fit into i32");
        // Minden kapu összes polinomiális kényszerét UCP-kifejezéssé alakítja.
        for gate in &analyzable.cs.gates {
            for poly in &gate.polys {
                // A szelektortömörítés után a kapuk fixed oszlopoktól függő polinomokat tartalmaznak.
                // Ezek közül sok az adott soron azonosan nulla. Ezt a teljes UCP-fa
                // felépítése előtt ellenőrzi, hogy elkerülje a szükségtelen munkát.
                // Csak azt az egyenletet hagyja ki, amelynek bal oldaláról
                // advice és instance értékek felhasználása nélkül
                // megállapítja, hogy a testben nulla.
                if fixed_only_expression_value(poly, region_begin, row, &analyzable.fixed)
                    .is_some_and(|value| bool::from(value.is_zero()))
                {
                    continue;
                }

                let mut expression = expression_to_ucp_expr_with_fixed_values(
                    poly,
                    region_begin,
                    row,
                    &analyzable.fixed,
                );
                wrap_query_rows(&mut expression, analyzable.k);
                if !matches!(expression, UcpExpr::Const(UcpScalar::Zero)) {
                    expressions.push(expression);
                }
            }
        }
    }

    // A permutációs és másolási kényszerekből is nullával egyenlő kifejezéseket képez.
    expressions.extend(extract_copy_constraint_expressions(&analyzable.permutation));

    expressions
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
fn wrap_query_rows(expr: &mut UcpExpr, k: u32) {
    match expr {
        UcpExpr::Var(cell) => {
            let period = 1_i64
                .checked_shl(k)
                .expect("UCP evaluation domain overflow");
            cell.row =
                i32::try_from(i64::from(cell.row).rem_euclid(period)).expect("UCP row exceeds i32");
        }
        UcpExpr::Neg(inner) | UcpExpr::Scale(inner, _) => wrap_query_rows(inner, k),
        UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
            wrap_query_rows(left, k);
            wrap_query_rows(right, k);
        }
        UcpExpr::Const(_) => {}
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
// A kifejezést akkor értékeli ki, ha kizárólag konstansoktól és ismert fixed értékektől függ.
// Advice, instance vagy ismeretlen kihívásérték esetén nem ad konkrét értéket.
fn fixed_only_expression_value<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
    fixed_values: &[Vec<CellValue<F>>],
) -> Option<F> {
    match expr {
        Expression::Constant(value) => Some(*value),
        // A config_and_synthesize szelektortömörítése után nem vár nyers szelektorhivatkozást;
        // ha mégis ilyet talál, nem feltételez róla konkrét értéket.
        Expression::Selector(_) => None,
        Expression::Fixed(query) => {
            let column = fixed_values.get(query.column_index)?;
            if column.is_empty() {
                return None;
            }
            let absolute_row = query_row(region_begin, row, query.rotation, column.len());
            match column.get(absolute_row)? {
                CellValue::Assigned(value) => Some(*value),
                CellValue::Unassigned | CellValue::Poison(_) => None,
            }
        }
        Expression::Advice(_) | Expression::Instance(_) => None,
        Expression::Negated(inner) => {
            fixed_only_expression_value(inner, region_begin, row, fixed_values).map(|value| -value)
        }
        Expression::Sum(left, right) => Some(
            fixed_only_expression_value(left, region_begin, row, fixed_values)?
                + fixed_only_expression_value(right, region_begin, row, fixed_values)?,
        ),
        Expression::Product(left, right) => {
            // A tényezőket külön értékeli ki, így ismert nullatényező esetén
            // az advice cellákat tartalmazó másik tényező ismerete nélkül is nullát ad.
            let left_value = fixed_only_expression_value(left, region_begin, row, fixed_values);
            if left_value
                .as_ref()
                .is_some_and(|value| bool::from(value.is_zero()))
            {
                return Some(F::ZERO);
            }

            let right_value = fixed_only_expression_value(right, region_begin, row, fixed_values);
            if right_value
                .as_ref()
                .is_some_and(|value| bool::from(value.is_zero()))
            {
                return Some(F::ZERO);
            }

            Some(left_value? * right_value?)
        }
        Expression::Scaled(inner, scale) => {
            if bool::from(scale.is_zero()) {
                Some(F::ZERO)
            } else {
                fixed_only_expression_value(inner, region_begin, row, fixed_values)
                    .map(|value| value * *scale)
            }
        }
        #[cfg(any(
            feature = "use_pse_halo2_proofs",
            feature = "use_axiom_halo2_proofs",
            feature = "use_scroll_halo2_proofs"
        ))]
        Expression::Challenge(_) => None,
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
// A másolási és permutációs kényszerekből A - B = 0 alakú UCP-egyenleteket képez.
fn extract_copy_constraint_expressions(
    permutation: &permutation::keygen::Assembly,
) -> Vec<UcpExpr> {
    let mut expressions = Vec::new();
    // Az azonos irányfüggetlen éleket csak egyszer veszi fel.
    let mut seen_edges = HashSet::new();

    // Bejárja a permutációs leképezés oszlopait és sorait.
    for col in 0..permutation.mapping.len() {
        for row in 0..permutation.mapping[col].len() {
            // A leképezésből cellánként a ciklus következő tagját olvassa ki.
            // Ezt az egy élt dolgozza fel, így nem járja be újra
            // a teljes ciklust minden egyes tagból.
            let (right_col, right_row) = permutation.mapping[col][row];
            // A ciklusméretet nem tekinti minden tagnál hitelesnek, mert azt a reprezentáns tárolja.
            if (right_col, right_row) == (col, row) {
                continue;
            }
            let Some(left) = permutation_cell_id(permutation, col, row) else {
                continue;
            };
            let Some(right) = permutation_cell_id(permutation, right_col, right_row) else {
                continue;
            };

            // Az egyenlőséget irányfüggetlenül kanonizálja, így a kétcellás ciklus
            // A->B és B->A élét ugyanannak a kapcsolatnak tekinti.
            let edge = if left <= right {
                (left.clone(), right.clone())
            } else {
                (right.clone(), left.clone())
            };

            // A left == right feltételből left - right = 0 UCP-kifejezést készít.
            if left != right && seen_edges.insert(edge) {
                expressions.push(UcpExpr::add(
                    UcpExpr::var(left),
                    UcpExpr::neg(UcpExpr::var(right)),
                ));
            }
        }
    }

    expressions
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
// A permutáció oszlop- és sorpozíciójából UCP-cellaazonosítót készít.
fn permutation_cell_id(
    permutation: &permutation::keygen::Assembly,
    col: usize,
    row: usize,
) -> Option<CellId> {
    let column = permutation.columns.get(col)?;
    let row = i32::try_from(row).ok()?;

    #[cfg(feature = "use_zcash_halo2_proofs")]
    {
        // A Zcash Halo2 adat nélküli Any-változatait alakítja cellatípussá.
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
        // A többi támogatott Halo2-változat adathordozó Advice-változatát is kezeli.
        match column.column_type() {
            Any::Advice(_) => Some(CellId::advice(column.index, row)),
            Any::Fixed => Some(CellId::fixed(column.index, row)),
            Any::Instance => Some(CellId::instance(column.index, row)),
        }
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
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

    // A teszt egy szelektorral aktivált értékadási kaput állít elő.
    #[derive(Clone, Debug)]
    struct ExtractorConfig {
        advice: Column<Advice>,
        selector: Selector,
    }

    #[derive(Clone, Debug, Default)]
    struct ExtractorCircuit {
        _marker: PhantomData<Fr>,
    }

    // A teszt másolási kényszert tartalmazó kapcsolást állít elő.
    #[derive(Clone, Debug)]
    struct CopyConfig {
        advice: Column<Advice>,
        instance: Column<Instance>,
    }

    #[derive(Clone, Debug, Default)]
    struct CopyCircuit {
        _marker: PhantomData<Fr>,
    }

    // A teszt két szelektor közül csak a másodikhoz tartozó kaput aktiválja.
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

    // A teszt a selector * advice bemenetet egy 0..3 értékű lookup-táblához köti.
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

    // A teszt skálázott advice kifejezést, 2*x-et használ lookup-bemenetként.
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

            // A teszt a selector * (advice + public - 5) = 0 kényszert állítja elő.
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
                    // A kaput csak ezen a soron aktiválja.
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

            // Engedélyezi az egyenlőségi kapcsolatokat a másolási kényszerekhez.
            meta.enable_equality(advice);
            meta.enable_equality(instance);

            CopyConfig { advice, instance }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            // Az advice cellát másolási kényszerrel instance cellához köti.
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
                    // Csak a második szelektort aktiválja ezen a soron.
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

    // A teszt ellenőrzi az Analyzable kapcsolásból előállított UCP-probléma elemzését.
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

    // A teszt ellenőrzi az advice értékének kikövetkeztetését egy másolási egyenletből.
    #[test]
    fn copy_cycles_include_members_without_representative_size_metadata() {
        for reverse in [false, true] {
            let mut cs = ConstraintSystem::<Fr>::default();
            let advice = cs.advice_column();
            let instance = cs.instance_column();
            cs.enable_equality(advice);
            cs.enable_equality(instance);
            let mut permutation = permutation::keygen::Assembly::new(16, &cs.permutation);
            let rows = if reverse { [2, 1, 0] } else { [0, 1, 2] };
            permutation
                .copy(advice.into(), rows[0], advice.into(), rows[1])
                .unwrap();
            permutation
                .copy(advice.into(), rows[1], advice.into(), rows[2])
                .unwrap();
            permutation
                .copy(advice.into(), rows[2], instance.into(), 0)
                .unwrap();
            let expressions = extract_copy_constraint_expressions(&permutation);
            // A négytagú ciklus mind a négy élét feldolgozza akkor is, ha egyes tárolt méretek 1 értékűek.
            assert_eq!(expressions.len(), 4);
            assert!(permutation
                .mapping
                .iter()
                .zip(&permutation.sizes)
                .any(|(mapping, sizes)| {
                    mapping
                        .iter()
                        .zip(sizes)
                        .enumerate()
                        .any(|(row, (next, size))| *size == 1 && next.1 != row)
                }));
            let mut values = UcpValueFacts::new();
            values.mark_known(CellId::instance(0, 0), BigInt::from(7));
            let result = analyze_expressions_with_values(
                &expressions,
                initial_facts_from_expressions(&expressions),
                values,
            );
            for row in 0..3 {
                assert_eq!(
                    result.value_facts.known_value(&CellId::advice(0, row)),
                    Some(&BigInt::from(7))
                );
            }
        }
    }

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
        let copy_expressions = extract_copy_constraint_expressions(&analyzable.permutation);

        // A kétcellás permutációs ciklusban az irányfüggetlen
        // egyenlőséget csak egyszer veszi fel.
        assert_eq!(copy_expressions.len(), 1);

        let problem = extract_ucp_problem_with_targets(&analyzable, [target.clone()]);

        assert_eq!(problem.output_cells, vec![target.clone()]);
        assert!(problem.witness_cells.contains(&target));

        let mut instance_cells = HashMap::new();
        instance_cells.insert("I-0-0".to_string(), BigInt::from(2));
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

    // A teszt ellenőrzi, hogy tömörített szelektor mellett csak az aktív kapuból következtet.
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

        // A két globális kapu közül ezen a soron csak a másodikat aktiválja.
        assert_eq!(problem.expressions.len(), 1);

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

    // A teszt ellenőrzi, hogy a lookup-táblából véges domaint rendel a korlátozott advice cellához.
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

    // A teszt ellenőrzi a 2*x in {0,2,4} feltételből az x in {0,1,2} domain visszavetítését.
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

    // A teszt ellenőrzi, hogy érvénytelen táblabejegyzésből nem tanul túl szűk domaint.
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

    #[test]
    fn lookup_table_projection_does_not_truncate_an_oversized_domain() {
        let circuit = LookupRangeCircuit::default();
        let mut analyzable = Analyzable::config_and_synthesize(&circuit, 4).unwrap();
        let Expression::Fixed(query) = &analyzable.cs.lookups[0].table_expressions[0] else {
            panic!("Expected fixed lookup table");
        };
        analyzable.fixed[query.column_index] = (0..=MAX_FINITE_DOMAIN_SIZE)
            .map(|value| CellValue::Assigned(Fr::from(value as u64)))
            .collect();
        let problem = extract_ucp_problem(&analyzable);
        assert!(problem.expression_domains.is_empty());
        assert!(problem
            .initial_value_facts
            .domain(&CellId::advice(0, 0))
            .is_none());
    }
}
