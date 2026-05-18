use super::{cell::CellId, expr::UcpExpr};
use crate::circuit_analyzer::{analyzable::AnalyzableField, halo2_proofs_libs::*};
use std::collections::HashSet;

fn absolute_row(region_begin: usize, row: i32, rotation: Rotation) -> i32 {
    let region_begin =
        i32::try_from(region_begin).expect("region_begin does not fit into i32 for UCP");

    region_begin
        .checked_add(row)
        .and_then(|base| base.checked_add(rotation.0))
        .expect("absolute UCP row overflowed i32")
}

pub fn expression_to_ucp_expr<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
) -> UcpExpr {
    expression_to_ucp_expr_with_selector_indices(expr, region_begin, row, &HashSet::new())
}

pub fn expression_to_ucp_expr_with_selector_indices<F: AnalyzableField>(
    expr: &Expression<F>,
    region_begin: usize,
    row: i32,
    selector_indices: &HashSet<usize>,
) -> UcpExpr {
    match expr {
        Expression::Constant(_) => UcpExpr::constant(),
        // Selectors are row-fixed control signals. The caller decides which
        // rows a gate is active on; once a row is chosen, the selector value is
        // uniquely determined.
        Expression::Selector(_) => UcpExpr::constant(),
        Expression::Fixed(query) => {
            if selector_indices.contains(&query.column_index) {
                UcpExpr::constant()
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
            UcpExpr::neg(expression_to_ucp_expr_with_selector_indices(
                inner,
                region_begin,
                row,
                selector_indices,
            ))
        }
        Expression::Sum(left, right) => UcpExpr::add(
            expression_to_ucp_expr_with_selector_indices(left, region_begin, row, selector_indices),
            expression_to_ucp_expr_with_selector_indices(right, region_begin, row, selector_indices),
        ),
        Expression::Product(left, right) => UcpExpr::mul(
            expression_to_ucp_expr_with_selector_indices(left, region_begin, row, selector_indices),
            expression_to_ucp_expr_with_selector_indices(right, region_begin, row, selector_indices),
        ),
        Expression::Scaled(inner, scale) => {
            if bool::from(scale.is_zero()) {
                UcpExpr::constant()
            } else {
                UcpExpr::scale(expression_to_ucp_expr_with_selector_indices(
                    inner,
                    region_begin,
                    row,
                    selector_indices,
                ))
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
            UcpExpr::Const => {}
            UcpExpr::Neg(inner) | UcpExpr::Scale(inner) => collect_vars(inner, vars),
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

            vec![
                s * (advice_cur + instance_prev)
                    * (fixed_cur - Expression::Constant(Fr::from(7))),
            ]
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
        let expr = Expression::Scaled(
            Box::new(Expression::Constant(Fr::from(9))),
            Fr::zero(),
        );

        assert_eq!(expression_to_ucp_expr(&expr, 0, 0), UcpExpr::constant());
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
}
