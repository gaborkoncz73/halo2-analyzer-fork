use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
};
use crate::circuit_analyzer::{analyzable::AnalyzableField, halo2_proofs_libs::*};
use num::{BigInt, Num};
use std::collections::HashSet;

fn absolute_row(region_begin: usize, row: i32, rotation: Rotation) -> i32 {
    let region_begin =
        i32::try_from(region_begin).expect("region_begin does not fit into i32 for UCP");

    region_begin
        .checked_add(row)
        .and_then(|base| base.checked_add(rotation.0))
        .expect("absolute UCP row overflowed i32")
}

fn field_to_bigint<F: AnalyzableField>(value: &F) -> BigInt {
    BigInt::from_str_radix(format!("{:?}", value).strip_prefix("0x").unwrap(), 16).unwrap()
}

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
pub fn expression_to_ucp_expr_with_enabled_selector_indices<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
    selector_indices: &HashSet<usize>,
    enabled_selector_indices: &HashSet<usize>,
) -> UcpExpr {
    match expr {
        Expression::Constant(value) => {
            if bool::from(value.is_zero()) {
                UcpExpr::zero()
            } else {
                UcpExpr::known_constant(field_to_bigint(value))
            }
        }
        Expression::Selector(selector) => selector_constant(selector.0, enabled_selector_indices),
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
        Expression::Advice(query) => UcpExpr::var(CellId::advice(
            query.column_index,
            absolute_row(region_begin, row, query.rotation),
        )),
        Expression::Instance(query) => UcpExpr::var(CellId::instance(
            query.column_index,
            absolute_row(region_begin, row, query.rotation),
        )),
        Expression::Negated(inner) => {
            UcpExpr::neg(expression_to_ucp_expr_with_enabled_selector_indices(
                inner,
                region_begin,
                row,
                selector_indices,
                enabled_selector_indices,
            ))
        }
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
        Expression::Challenge(_) => UcpExpr::constant(),
    }
}

#[cfg(not(feature = "use_pse_v1_halo2_proofs"))]
fn selector_constant(selector_index: usize, enabled_selector_indices: &HashSet<usize>) -> UcpExpr {
    if enabled_selector_indices.contains(&selector_index) {
        UcpExpr::non_zero_constant()
    } else {
        UcpExpr::zero()
    }
}

pub fn expression_to_ucp_expr_with_selector_scalar<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
    selector_indices: &HashSet<usize>,
    selector_scalar: UcpScalar,
) -> UcpExpr {
    match expr {
        Expression::Constant(value) => {
            if bool::from(value.is_zero()) {
                UcpExpr::zero()
            } else {
                UcpExpr::known_constant(field_to_bigint(value))
            }
        }
        // Selectors are row-fixed control signals. The caller decides which
        // rows a gate is active on; once a row is chosen, the selector value is
        // uniquely determined.
        Expression::Selector(_) => UcpExpr::scalar_constant(selector_scalar.clone()),
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
        Expression::Advice(query) => UcpExpr::var(CellId::advice(
            query.column_index,
            absolute_row(region_begin, row, query.rotation),
        )),
        Expression::Instance(query) => UcpExpr::var(CellId::instance(
            query.column_index,
            absolute_row(region_begin, row, query.rotation),
        )),
        Expression::Negated(inner) => UcpExpr::neg(expression_to_ucp_expr_with_selector_scalar(
            inner,
            region_begin,
            row,
            selector_indices,
            selector_scalar.clone(),
        )),
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
        Expression::Challenge(_) => UcpExpr::constant(),
    }
}

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod tests {
    use super::*;
    use crate::circuit_analyzer::ucp::cell::CellId;

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

    #[test]
    fn zero_scaled_expression_is_constant_for_ucp() {
        let expr = Expression::Scaled(Box::new(Expression::Constant(Fr::from(9))), Fr::zero());

        assert_eq!(expression_to_ucp_expr(&expr, 0, 0), UcpExpr::zero());
    }

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
}
