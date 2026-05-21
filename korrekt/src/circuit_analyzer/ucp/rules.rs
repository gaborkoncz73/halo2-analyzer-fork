use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
    facts::UcpFacts,
};

/// Implements the expression-level UCP judgment from the paper Fig. 7:
/// Var, Const, and Op. This only proves that an expression is uniquely
/// determined by the current known-unique cells.
pub fn expression_is_unique(expr: &UcpExpr, facts: &UcpFacts) -> bool {
    match expr {
        UcpExpr::Var(cell) => facts.is_unique(cell),
        UcpExpr::Const(_) => true,
        UcpExpr::Neg(inner) => expression_is_unique(inner, facts),
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => true,
            UcpScalar::NonZero | UcpScalar::Unknown | UcpScalar::Known(_) => {
                expression_is_unique(inner, facts)
            }
        },
        UcpExpr::Add(left, right) => {
            expression_is_unique(left, facts) && expression_is_unique(right, facts)
        }
        UcpExpr::Mul(left, right) => {
            is_zero_constant(left)
                || is_zero_constant(right)
                || (expression_is_unique(left, facts) && expression_is_unique(right, facts))
        }
    }
}

/// Implements the first equation-level UCP propagation rule:
/// if a zero equation contains exactly one unknown cell linearly, with a
/// statically non-zero scalar coefficient, then that cell is unique.
pub fn infer_assigned_cell_from_zero_equation(expr: &UcpExpr, facts: &UcpFacts) -> Option<CellId> {
    let analysis = analyze_assign_candidate(expr, facts);

    if analysis.valid {
        analysis.candidate
    } else {
        None
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AssignAnalysis {
    candidate: Option<CellId>,
    valid: bool,
}

impl AssignAnalysis {
    fn none() -> Self {
        Self {
            candidate: None,
            valid: true,
        }
    }

    fn candidate(cell: CellId) -> Self {
        Self {
            candidate: Some(cell),
            valid: true,
        }
    }

    fn invalid() -> Self {
        Self {
            candidate: None,
            valid: false,
        }
    }

    fn merge_add(self, other: Self) -> Self {
        if !self.valid || !other.valid {
            return Self::invalid();
        }

        match (self.candidate, other.candidate) {
            (None, None) => Self::none(),
            (Some(cell), None) | (None, Some(cell)) => Self::candidate(cell),
            (Some(_), Some(_)) => Self::invalid(),
        }
    }
}

fn analyze_assign_candidate(expr: &UcpExpr, facts: &UcpFacts) -> AssignAnalysis {
    if expression_is_unique(expr, facts) {
        return AssignAnalysis::none();
    }

    match expr {
        UcpExpr::Var(cell) => AssignAnalysis::candidate(cell.clone()),
        UcpExpr::Const(_) => AssignAnalysis::none(),
        UcpExpr::Neg(inner) => analyze_assign_candidate(inner, facts),
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => AssignAnalysis::none(),
            UcpScalar::NonZero | UcpScalar::Known(_) => analyze_assign_candidate(inner, facts),
            UcpScalar::Unknown => AssignAnalysis::invalid(),
        },
        UcpExpr::Add(left, right) => {
            analyze_assign_candidate(left, facts).merge_add(analyze_assign_candidate(right, facts))
        }
        UcpExpr::Mul(left, right) => analyze_product_assign_candidate(left, right, facts),
    }
}

fn analyze_product_assign_candidate(
    left: &UcpExpr,
    right: &UcpExpr,
    facts: &UcpFacts,
) -> AssignAnalysis {
    if is_zero_constant(left) || is_zero_constant(right) {
        return AssignAnalysis::none();
    }

    if expression_is_unique(left, facts) && expression_is_unique(right, facts) {
        return AssignAnalysis::none();
    }

    if is_non_zero_constant(left) {
        return analyze_assign_candidate(right, facts);
    }

    if is_non_zero_constant(right) {
        return analyze_assign_candidate(left, facts);
    }

    AssignAnalysis::invalid()
}

fn is_zero_constant(expr: &UcpExpr) -> bool {
    matches!(expr, UcpExpr::Const(UcpScalar::Zero))
}

fn is_non_zero_constant(expr: &UcpExpr) -> bool {
    matches!(
        expr,
        UcpExpr::Const(UcpScalar::NonZero | UcpScalar::Known(_))
    )
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
    fn zero_product_is_unique() {
        let x = CellId::advice(0, 0);
        let facts = UcpFacts::new();
        let expr = UcpExpr::mul(UcpExpr::zero(), UcpExpr::var(x));

        assert!(expression_is_unique(&expr, &facts));
    }

    #[test]
    fn unary_ops_preserve_uniqueness() {
        let x = CellId::instance(0, 0);
        let facts = UcpFacts::from_iter([x.clone()]);
        let expr = UcpExpr::neg(UcpExpr::scale(UcpExpr::var(x)));

        assert!(expression_is_unique(&expr, &facts));
    }

    #[test]
    fn assign_rule_infers_single_linear_unknown() {
        let public = CellId::instance(0, 0);
        let advice = CellId::advice(0, 0);
        let facts = UcpFacts::from_iter([public.clone()]);
        let expr = UcpExpr::add(
            UcpExpr::scale_by(UcpExpr::var(advice.clone()), UcpScalar::NonZero),
            UcpExpr::var(public),
        );

        assert_eq!(
            infer_assigned_cell_from_zero_equation(&expr, &facts),
            Some(advice)
        );
    }

    #[test]
    fn assign_rule_rejects_unknown_scalar() {
        let advice = CellId::advice(0, 0);
        let facts = UcpFacts::new();
        let expr = UcpExpr::scale_by(UcpExpr::var(advice), UcpScalar::Unknown);

        assert_eq!(infer_assigned_cell_from_zero_equation(&expr, &facts), None);
    }

    #[test]
    fn assign_rule_rejects_multiple_unknowns() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let facts = UcpFacts::new();
        let expr = UcpExpr::add(UcpExpr::var(x), UcpExpr::var(y));

        assert_eq!(infer_assigned_cell_from_zero_equation(&expr, &facts), None);
    }
}
