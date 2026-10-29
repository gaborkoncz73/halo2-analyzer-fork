use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
};
use crate::circuit_analyzer::{analyzable::AnalyzableField, halo2_proofs_libs::*};
use num::{BigInt, Num};
use std::collections::HashSet;

// A régió kezdetéből, a helyi sorból és a rotációból abszolút UCP-sort számít.
fn absolute_row(region_begin: usize, row: i32, rotation: Rotation) -> i32 {
    let region_begin =
        i32::try_from(region_begin).expect("region_begin does not fit into i32 for UCP");

    region_begin
        .checked_add(row)
        .and_then(|base| base.checked_add(rotation.0))
        .expect("absolute UCP row overflowed i32")
}

// A rotációt a kiértékelési tartományon körbefordítja, negatív eltolás esetén is.
pub(crate) fn query_row(
    region_begin: usize,
    row: i32,
    rotation: Rotation,
    num_rows: usize,
) -> usize {
    let base = i64::try_from(region_begin).expect("region row does not fit into i64");
    let period = i64::try_from(num_rows).expect("evaluation domain does not fit into i64");
    (base + i64::from(row) + i64::from(rotation.0)).rem_euclid(period) as usize
}

// A Halo2-testelemet BigInt alakra hozza az UCP-konstanshoz.
pub(crate) fn field_to_bigint<F: AnalyzableField>(value: &F) -> BigInt {
    BigInt::from_str_radix(format!("{:?}", value).strip_prefix("0x").unwrap(), 16).unwrap()
}

// A Halo2-testelemből UCP-konstanskifejezést készít.
fn field_to_ucp_constant<F: AnalyzableField>(value: &F) -> UcpExpr {
    if bool::from(value.is_zero()) {
        UcpExpr::zero()
    } else {
        UcpExpr::known_constant(field_to_bigint(value))
    }
}

// A fixed vagy szelektorcella ténylegesen hozzárendelt értékét olvassa ki, ha elérhető.
fn fixed_query_value<F: AnalyzableField>(
    query: &FixedQuery,
    region_begin: usize,
    row: i32,
    fixed_values: &[Vec<CellValue<F>>],
) -> Option<UcpExpr> {
    let column = fixed_values.get(query.column_index)?;
    if column.is_empty() {
        return None;
    }
    let absolute_row = query_row(region_begin, row, query.rotation, column.len());

    match column.get(absolute_row)? {
        CellValue::Assigned(value) => Some(field_to_ucp_constant(value)),
        CellValue::Unassigned | CellValue::Poison(_) => None,
    }
}

// A Halo2-kifejezést UcpExpr fára fordítja a szelektorértékek ismerete nélkül.
pub fn expression_to_ucp_expr<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
) -> UcpExpr {
    expression_to_ucp_expr_with_selector_scalar(
        expr,
        region_begin,
        row,
        &HashSet::new(),
        UcpScalar::Unknown,
    )
}

// A fordításban felhasználja a fixed és szelektorcellák ténylegesen hozzárendelt értékeit.
pub fn expression_to_ucp_expr_with_fixed_values<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
    fixed_values: &[Vec<CellValue<F>>],
) -> UcpExpr {
    expression_to_ucp_expr_with_fixed_values_and_selector_scalar(
        expr,
        region_begin,
        row,
        fixed_values,
        UcpScalar::Unknown,
    )
}

// A megadott oszlopindexek alapján megkülönbözteti a fixed szelektoroszlopokat.
pub fn expression_to_ucp_expr_with_selector_indices<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
    selector_indices: &HashSet<usize>,
) -> UcpExpr {
    expression_to_ucp_expr_with_selector_scalar(
        expr,
        region_begin,
        row,
        selector_indices,
        UcpScalar::Unknown,
    )
}

// Aktív szelektor mellett fordít; a szelektort nemnullának tekinti.
pub fn expression_to_ucp_expr_with_active_selectors<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
    selector_indices: &HashSet<usize>,
) -> UcpExpr {
    expression_to_ucp_expr_with_selector_scalar(
        expr,
        region_begin,
        row,
        selector_indices,
        UcpScalar::NonZero,
    )
}

// Inaktív szelektor mellett fordít; a szelektort nullának tekinti.
pub fn expression_to_ucp_expr_with_inactive_selectors<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
    selector_indices: &HashSet<usize>,
) -> UcpExpr {
    expression_to_ucp_expr_with_selector_scalar(
        expr,
        region_begin,
        row,
        selector_indices,
        UcpScalar::Zero,
    )
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
// A megadott aktív szelektorindexek alapján fordítja a kifejezést.
pub fn expression_to_ucp_expr_with_enabled_selector_indices<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
    selector_indices: &HashSet<usize>,
    enabled_selector_indices: &HashSet<usize>,
) -> UcpExpr {
    match expr {
        // A konstans értékét UCP-konstansként adja tovább.
        Expression::Constant(value) => field_to_ucp_constant(value),
        // A szelektor értékét az adott sorban ismert engedélyezésből állapítja meg.
        Expression::Selector(selector) => selector_constant(selector.0, enabled_selector_indices),
        // A fixed hivatkozásnál megkülönbözteti a szelektoroszlopot és a szokásos fixed cellát.
        Expression::Fixed(query) => {
            if selector_indices.contains(&query.column_index) {
                selector_constant(query.column_index, enabled_selector_indices)
            } else {
                UcpExpr::var(CellId::fixed(
                    query.column_index,
                    absolute_row(region_begin, row, query.rotation),
                ))
            }
        }
        // Az advice lekérdezést konkrét UCP-cellahivatkozásra fordítja.
        Expression::Advice(query) => UcpExpr::var(CellId::advice(
            query.column_index,
            absolute_row(region_begin, row, query.rotation),
        )),
        // Az instance lekérdezést konkrét UCP-cellahivatkozásra fordítja.
        Expression::Instance(query) => UcpExpr::var(CellId::instance(
            query.column_index,
            absolute_row(region_begin, row, query.rotation),
        )),
        // A negálás belső kifejezését rekurzívan UCP-re fordítja.
        Expression::Negated(inner) => {
            UcpExpr::neg(expression_to_ucp_expr_with_enabled_selector_indices(
                inner,
                region_begin,
                row,
                selector_indices,
                enabled_selector_indices,
            ))
        }
        // Az összeg tagjait rekurzívan UCP-re fordítja.
        Expression::Sum(left, right) => UcpExpr::add(
            expression_to_ucp_expr_with_enabled_selector_indices(
                left,
                region_begin,
                row,
                selector_indices,
                enabled_selector_indices,
            ),
            expression_to_ucp_expr_with_enabled_selector_indices(
                right,
                region_begin,
                row,
                selector_indices,
                enabled_selector_indices,
            ),
        ),
        // A szorzat tényezőit rekurzívan UCP-re fordítja.
        Expression::Product(left, right) => UcpExpr::mul(
            expression_to_ucp_expr_with_enabled_selector_indices(
                left,
                region_begin,
                row,
                selector_indices,
                enabled_selector_indices,
            ),
            expression_to_ucp_expr_with_enabled_selector_indices(
                right,
                region_begin,
                row,
                selector_indices,
                enabled_selector_indices,
            ),
        ),
        // Nulla skálázásnál azonnal nulla kifejezést állít elő.
        Expression::Scaled(inner, scale) => {
            if bool::from(scale.is_zero()) {
                UcpExpr::zero()
            } else {
                UcpExpr::scale_by(
                    expression_to_ucp_expr_with_enabled_selector_indices(
                        inner,
                        region_begin,
                        row,
                        selector_indices,
                        enabled_selector_indices,
                    ),
                    UcpScalar::known(field_to_bigint(scale)),
                )
            }
        }
        #[cfg(any(
            feature = "use_pse_halo2_proofs",
            feature = "use_axiom_halo2_proofs",
            feature = "use_scroll_halo2_proofs"
        ))]
        // A kihívásértéket itt absztrakt konstansként kezeli, konkrét értéket nem feltételez.
        Expression::Challenge(_) => UcpExpr::constant(),
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
// Aktív szelektorhoz 1, inaktív szelektorhoz 0 UCP-konstanst készít.
fn selector_constant(selector_index: usize, enabled_selector_indices: &HashSet<usize>) -> UcpExpr {
    if enabled_selector_indices.contains(&selector_index) {
        UcpExpr::known_constant_i64(1)
    } else {
        UcpExpr::zero()
    }
}

// Az ismert fixed értékekkel és a hívó által megadott absztrakt szelektorskalárral fordít.
pub fn expression_to_ucp_expr_with_fixed_values_and_selector_scalar<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
    fixed_values: &[Vec<CellValue<F>>],
    selector_scalar: UcpScalar,
) -> UcpExpr {
    match expr {
        // A konstans értékét UCP-konstansként adja tovább.
        Expression::Constant(value) => field_to_ucp_constant(value),
        // A nyers szelektort a tömörítés előtti kifejezés részeként kezeli.
        Expression::Selector(_) => UcpExpr::scalar_constant(selector_scalar.clone()),
        // Ismert fixed értéket konstansra cserél; máskor fixed cellahivatkozást tart meg.
        Expression::Fixed(query) => fixed_query_value(query, region_begin, row, fixed_values)
            .unwrap_or_else(|| {
                UcpExpr::var(CellId::fixed(
                    query.column_index,
                    absolute_row(region_begin, row, query.rotation),
                ))
            }),
        // Az advice lekérdezést konkrét UCP-cellahivatkozásra fordítja.
        Expression::Advice(query) => UcpExpr::var(CellId::advice(
            query.column_index,
            absolute_row(region_begin, row, query.rotation),
        )),
        // Az instance lekérdezést konkrét UCP-cellahivatkozásra fordítja.
        Expression::Instance(query) => UcpExpr::var(CellId::instance(
            query.column_index,
            absolute_row(region_begin, row, query.rotation),
        )),
        // A negálás belső kifejezését rekurzívan UCP-re fordítja.
        Expression::Negated(inner) => UcpExpr::neg(
            expression_to_ucp_expr_with_fixed_values_and_selector_scalar(
                inner,
                region_begin,
                row,
                fixed_values,
                selector_scalar.clone(),
            ),
        ),
        // Az összeg tagjait rekurzívan UCP-re fordítja.
        Expression::Sum(left, right) => UcpExpr::add(
            expression_to_ucp_expr_with_fixed_values_and_selector_scalar(
                left,
                region_begin,
                row,
                fixed_values,
                selector_scalar.clone(),
            ),
            expression_to_ucp_expr_with_fixed_values_and_selector_scalar(
                right,
                region_begin,
                row,
                fixed_values,
                selector_scalar.clone(),
            ),
        ),
        // A szorzat tényezőit rekurzívan UCP-re fordítja.
        Expression::Product(left, right) => UcpExpr::mul(
            expression_to_ucp_expr_with_fixed_values_and_selector_scalar(
                left,
                region_begin,
                row,
                fixed_values,
                selector_scalar.clone(),
            ),
            expression_to_ucp_expr_with_fixed_values_and_selector_scalar(
                right,
                region_begin,
                row,
                fixed_values,
                selector_scalar.clone(),
            ),
        ),
        // Nulla skálázásnál azonnal nulla kifejezést állít elő.
        Expression::Scaled(inner, scale) => UcpExpr::scale_by(
            expression_to_ucp_expr_with_fixed_values_and_selector_scalar(
                inner,
                region_begin,
                row,
                fixed_values,
                selector_scalar.clone(),
            ),
            UcpScalar::known(field_to_bigint(scale)),
        ),
        #[cfg(any(
            feature = "use_pse_halo2_proofs",
            feature = "use_axiom_halo2_proofs",
            feature = "use_scroll_halo2_proofs"
        ))]
        // A kihívásértéket itt absztrakt konstansként kezeli, konkrét értéket nem feltételez.
        Expression::Challenge(_) => UcpExpr::constant(),
    }
}

// A hívó által megadott absztrakt szelektorskalárral fordítja a kifejezést.
pub fn expression_to_ucp_expr_with_selector_scalar<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
    selector_indices: &HashSet<usize>,
    selector_scalar: UcpScalar,
) -> UcpExpr {
    match expr {
        // A konstans értékét UCP-konstansként adja tovább.
        Expression::Constant(value) => field_to_ucp_constant(value),
        // A szelektort a hívó által megadott absztrakt skalárral helyettesíti.
        Expression::Selector(_) => UcpExpr::scalar_constant(selector_scalar.clone()),
        // A fixed hivatkozásnál megkülönbözteti a szelektoroszlopot és a szokásos fixed cellát.
        Expression::Fixed(query) => {
            if selector_indices.contains(&query.column_index) {
                UcpExpr::scalar_constant(selector_scalar.clone())
            } else {
                UcpExpr::var(CellId::fixed(
                    query.column_index,
                    absolute_row(region_begin, row, query.rotation),
                ))
            }
        }
        // Az advice lekérdezést konkrét UCP-cellahivatkozásra fordítja.
        Expression::Advice(query) => UcpExpr::var(CellId::advice(
            query.column_index,
            absolute_row(region_begin, row, query.rotation),
        )),
        // Az instance lekérdezést konkrét UCP-cellahivatkozásra fordítja.
        Expression::Instance(query) => UcpExpr::var(CellId::instance(
            query.column_index,
            absolute_row(region_begin, row, query.rotation),
        )),
        // A negálás belső kifejezését rekurzívan UCP-re fordítja.
        Expression::Negated(inner) => UcpExpr::neg(expression_to_ucp_expr_with_selector_scalar(
            inner,
            region_begin,
            row,
            selector_indices,
            selector_scalar.clone(),
        )),
        // Az összeg tagjait rekurzívan UCP-re fordítja.
        Expression::Sum(left, right) => UcpExpr::add(
            expression_to_ucp_expr_with_selector_scalar(
                left,
                region_begin,
                row,
                selector_indices,
                selector_scalar.clone(),
            ),
            expression_to_ucp_expr_with_selector_scalar(
                right,
                region_begin,
                row,
                selector_indices,
                selector_scalar.clone(),
            ),
        ),
        // A szorzat tényezőit rekurzívan UCP-re fordítja.
        Expression::Product(left, right) => UcpExpr::mul(
            expression_to_ucp_expr_with_selector_scalar(
                left,
                region_begin,
                row,
                selector_indices,
                selector_scalar.clone(),
            ),
            expression_to_ucp_expr_with_selector_scalar(
                right,
                region_begin,
                row,
                selector_indices,
                selector_scalar.clone(),
            ),
        ),
        // Nulla skálázásnál azonnal nulla kifejezést állít elő.
        Expression::Scaled(inner, scale) => {
            if bool::from(scale.is_zero()) {
                UcpExpr::zero()
            } else {
                UcpExpr::scale_by(
                    expression_to_ucp_expr_with_selector_scalar(
                        inner,
                        region_begin,
                        row,
                        selector_indices,
                        selector_scalar.clone(),
                    ),
                    UcpScalar::known(field_to_bigint(scale)),
                )
            }
        }
        #[cfg(any(
            feature = "use_pse_halo2_proofs",
            feature = "use_axiom_halo2_proofs",
            feature = "use_scroll_halo2_proofs"
        ))]
        // A kihívásértéket itt absztrakt konstansként kezeli, konkrét értéket nem feltételez.
        Expression::Challenge(_) => UcpExpr::constant(),
    }
}

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod tests {
    use super::*;
    use crate::circuit_analyzer::ucp::cell::CellId;

    // A teszt segédfüggvénye összegyűjti a kifejezés cellahivatkozásait.
    fn collect_vars(expr: &UcpExpr, vars: &mut HashSet<CellId>) {
        match expr {
            UcpExpr::Var(cell) => {
                vars.insert(cell.clone());
            }
            UcpExpr::Const(_) => {}
            UcpExpr::Neg(inner) | UcpExpr::Scale(inner, _) => collect_vars(inner, vars),
            UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
                collect_vars(left, vars);
                collect_vars(right, vars);
            }
        }
    }

    // A teszt ellenőrzi az advice, instance és fixed lekérdezések abszolút cellára fordítását.
    #[test]
    fn converts_plonkish_queries_to_absolute_ucp_cells() {
        let mut cs = ConstraintSystem::<Fr>::default();
        let advice = cs.advice_column();
        let instance = cs.instance_column();
        let fixed = cs.fixed_column();
        let selector = cs.selector();

        cs.create_gate("ucp conversion", |meta| {
            let s = meta.query_selector(selector);
            let advice_cur = meta.query_advice(advice, Rotation::cur());
            let instance_prev = meta.query_instance(instance, Rotation::prev());
            let fixed_cur = meta.query_fixed(fixed);

            vec![s * (advice_cur + instance_prev) * (fixed_cur - Expression::Constant(Fr::from(7)))]
        });

        let ucp_expr = expression_to_ucp_expr(&cs.gates[0].polys[0], 10, 2);
        let mut vars = HashSet::new();
        collect_vars(&ucp_expr, &mut vars);

        assert_eq!(vars.len(), 3);
        assert!(vars.contains(&CellId::advice(0, 12)));
        assert!(vars.contains(&CellId::instance(0, 11)));
        assert!(vars.contains(&CellId::fixed(0, 12)));
    }

    // A teszt ellenőrzi, hogy nullával skálázásnál nulla UCP-konstanst készít.
    #[test]
    fn zero_scaled_expression_is_constant_for_ucp() {
        let expr = Expression::Scaled(Box::new(Expression::Constant(Fr::from(9))), Fr::zero());

        assert_eq!(expression_to_ucp_expr(&expr, 0, 0), UcpExpr::zero());
    }

    // A teszt ellenőrzi, hogy a mintakapu összes advice celláját megőrzi a fordítás.
    #[test]
    fn converts_sample_circuit_gate_expression() {
        let mut cs = ConstraintSystem::<Fr>::default();
        let b0 = cs.advice_column();
        let b1 = cs.advice_column();
        let x = cs.advice_column();
        let s = cs.selector();

        cs.create_gate("two bit equality", |meta| {
            let selector = meta.query_selector(s);
            let b0 = meta.query_advice(b0, Rotation::cur());
            let b1 = meta.query_advice(b1, Rotation::cur());
            let x = meta.query_advice(x, Rotation::cur());

            vec![selector * (b0 + Expression::Constant(Fr::from(2)) * b1 - x)]
        });

        let ucp_expr = expression_to_ucp_expr(&cs.gates[0].polys[0], 0, 0);
        let mut vars = HashSet::new();
        collect_vars(&ucp_expr, &mut vars);

        assert!(vars.contains(&CellId::advice(0, 0)));
        assert!(vars.contains(&CellId::advice(1, 0)));
        assert!(vars.contains(&CellId::advice(2, 0)));
        assert_eq!(vars.len(), 3);
    }

    // A teszt ellenőrzi az aktív szelektorral vezérelt értékadási kényszer propagációját.
    #[test]
    fn active_selector_conversion_allows_assign_propagation() {
        use crate::circuit_analyzer::ucp::engine::analyze_expressions;
        use crate::circuit_analyzer::ucp::facts::initial_facts;

        let mut cs = ConstraintSystem::<Fr>::default();
        let advice = cs.advice_column();
        let instance = cs.instance_column();
        let selector = cs.selector();

        cs.create_gate("selected assignment", |meta| {
            let selector = meta.query_selector(selector);
            let advice = meta.query_advice(advice, Rotation::cur());
            let public = meta.query_instance(instance, Rotation::cur());

            vec![selector * (advice + public - Expression::Constant(Fr::from(5)))]
        });

        let default_expr = expression_to_ucp_expr(&cs.gates[0].polys[0], 0, 0);
        let default_result =
            analyze_expressions(&[default_expr], initial_facts([CellId::instance(0, 0)], []));

        assert!(!default_result.facts.is_unique(&CellId::advice(0, 0)));
        assert!(!default_result.all_expressions_unique());

        let active_expr = expression_to_ucp_expr_with_active_selectors(
            &cs.gates[0].polys[0],
            0,
            0,
            &HashSet::new(),
        );
        let active_result =
            analyze_expressions(&[active_expr], initial_facts([CellId::instance(0, 0)], []));

        assert!(active_result.facts.is_unique(&CellId::advice(0, 0)));
        assert!(active_result.all_expressions_unique());
    }

    // A teszt ellenőrzi, hogy inaktív szelektor mellett nem igazol advice-egyértelműséget.
    #[test]
    fn inactive_selector_conversion_does_not_propagate_assignment() {
        use crate::circuit_analyzer::ucp::engine::analyze_expressions;
        use crate::circuit_analyzer::ucp::facts::initial_facts;

        let mut cs = ConstraintSystem::<Fr>::default();
        let advice = cs.advice_column();
        let instance = cs.instance_column();
        let selector = cs.selector();

        cs.create_gate("inactive selected assignment", |meta| {
            let selector = meta.query_selector(selector);
            let advice = meta.query_advice(advice, Rotation::cur());
            let public = meta.query_instance(instance, Rotation::cur());

            vec![selector * (advice + public - Expression::Constant(Fr::from(5)))]
        });

        let inactive_expr = expression_to_ucp_expr_with_inactive_selectors(
            &cs.gates[0].polys[0],
            0,
            0,
            &HashSet::new(),
        );
        let inactive_result = analyze_expressions(
            &[inactive_expr],
            initial_facts([CellId::instance(0, 0)], []),
        );

        assert!(!inactive_result.facts.is_unique(&CellId::advice(0, 0)));
        assert!(inactive_result.all_expressions_unique());
    }

    // A teszt ellenőrzi, hogy az 1 értékű fixed szelektort konstansként kezeli.
    #[test]
    fn fixed_value_conversion_uses_assigned_one_selector() {
        use crate::circuit_analyzer::ucp::engine::analyze_expressions;
        use crate::circuit_analyzer::ucp::facts::initial_facts;

        let mut cs = ConstraintSystem::<Fr>::default();
        let selector_fixed = cs.fixed_column();
        let advice = cs.advice_column();
        let instance = cs.instance_column();

        cs.create_gate("fixed selected assignment", |meta| {
            let selector = meta.query_fixed(selector_fixed);
            let advice = meta.query_advice(advice, Rotation::cur());
            let public = meta.query_instance(instance, Rotation::cur());

            vec![selector * (advice + public - Expression::Constant(Fr::from(5)))]
        });

        let fixed_values = vec![vec![CellValue::Assigned(Fr::from(1))]];
        let expr =
            expression_to_ucp_expr_with_fixed_values(&cs.gates[0].polys[0], 0, 0, &fixed_values);
        let result = analyze_expressions(&[expr], initial_facts([CellId::instance(0, 0)], []));

        assert!(result.facts.is_unique(&CellId::advice(0, 0)));
        assert!(result.all_expressions_unique());
    }

    // A teszt ellenőrzi, hogy a 0 értékű fixed szelektor a teljes kényszert lenullázza.
    #[test]
    fn fixed_value_conversion_uses_assigned_zero_selector() {
        use crate::circuit_analyzer::ucp::{
            engine::analyze_expressions_with_values_and_modulus,
            facts::initial_facts,
            value::{UcpValueDomain, UcpValueFacts},
        };
        use num_bigint::BigInt;

        let mut cs = ConstraintSystem::<Fr>::default();
        let selector_fixed = cs.fixed_column();
        let x = cs.instance_column();
        let b0 = cs.advice_column();
        let b1 = cs.advice_column();

        cs.create_gate("inactive fixed selected base conv", |meta| {
            let selector = meta.query_fixed(selector_fixed);
            let x = meta.query_instance(x, Rotation::cur());
            let b0 = meta.query_advice(b0, Rotation::cur());
            let b1 = meta.query_advice(b1, Rotation::cur());

            vec![selector * (b0 + Expression::Constant(Fr::from(2)) * b1 - x)]
        });

        let fixed_values = vec![vec![CellValue::Assigned(Fr::from(0))]];
        let expr =
            expression_to_ucp_expr_with_fixed_values(&cs.gates[0].polys[0], 0, 0, &fixed_values);
        let mut value_facts = UcpValueFacts::new();
        let boolean_domain =
            UcpValueDomain::finite_set([BigInt::from(0), BigInt::from(1)]).unwrap();
        value_facts.mark_domain(CellId::advice(0, 0), boolean_domain.clone());
        value_facts.mark_domain(CellId::advice(1, 0), boolean_domain);

        let result = analyze_expressions_with_values_and_modulus(
            &[expr],
            initial_facts([CellId::instance(0, 0)], []),
            value_facts,
            &BigInt::from(101),
        );

        assert!(!result.facts.is_unique(&CellId::advice(0, 0)));
        assert!(!result.facts.is_unique(&CellId::advice(1, 0)));
        assert!(result.all_expressions_unique());
    }
}
