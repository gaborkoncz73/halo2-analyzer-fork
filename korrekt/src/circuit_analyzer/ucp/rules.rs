use super::{expr::UcpExpr, facts::UcpFacts};

/// Implements the expression-level UCP judgment from the paper:
/// Var, Const, and Op. This only proves that an expression is uniquely
/// determined by the current known-unique cells; it does not add new cells.
pub fn expression_is_unique(expr: &UcpExpr, facts: &UcpFacts) -> bool {
    match expr {
        UcpExpr::Var(cell) => facts.is_unique(cell),
        UcpExpr::Const => true,
        UcpExpr::Neg(inner) | UcpExpr::Scale(inner) => expression_is_unique(inner, facts),
        UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
            expression_is_unique(left, facts) && expression_is_unique(right, facts)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit_analyzer::ucp::cell::CellId;

    #[test]
    fn const_rule_marks_constants_unique() {
        let facts = UcpFacts::new();

        assert!(expression_is_unique(&UcpExpr::constant(), &facts));
    }

    #[test]
    fn var_rule_uses_known_unique_cells() {
        let known = CellId::advice(0, 3);
        let unknown = CellId::advice(1, 3);
        let facts = UcpFacts::from_iter([known.clone()]);

        assert!(expression_is_unique(&UcpExpr::var(known), &facts));
        assert!(!expression_is_unique(&UcpExpr::var(unknown), &facts));
    }

    #[test]
    fn op_rule_requires_all_operands_to_be_unique() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let facts = UcpFacts::from_iter([x.clone()]);

        let unique_expr = UcpExpr::add(UcpExpr::var(x), UcpExpr::constant());
        let non_unique_expr = UcpExpr::mul(unique_expr.clone(), UcpExpr::var(y));

        assert!(expression_is_unique(&unique_expr, &facts));
        assert!(!expression_is_unique(&non_unique_expr, &facts));
    }

    #[test]
    fn unary_ops_preserve_uniqueness() {
        let x = CellId::instance(0, 0);
        let facts = UcpFacts::from_iter([x.clone()]);
        let expr = UcpExpr::neg(UcpExpr::scale(UcpExpr::var(x)));

        assert!(expression_is_unique(&expr, &facts));
    }
}
