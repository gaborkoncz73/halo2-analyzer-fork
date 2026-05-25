use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
    facts::UcpFacts,
};

//A cikk Fig. 7 szerinti expression-level uniqueness szabályait valósítja meg
pub fn expression_is_unique(expr: &UcpExpr, facts: &UcpFacts) -> bool {
    match expr {
        //Változó akkor unique, ha szerepel a K halmazban
        UcpExpr::Var(cell) => facts.is_unique(cell),
        //Konstans mindig unique
        UcpExpr::Const(_) => true,
        //Negálás nem változtatja meg a uniqueness-t
        UcpExpr::Neg(inner) => expression_is_unique(inner, facts),
        //Nullával skálázás mindig unique, különben a belső expressiontől függ
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => true,
            UcpScalar::NonZero | UcpScalar::Unknown | UcpScalar::Known(_) => {
                expression_is_unique(inner, facts)
            }
        },
        //Összeadás akkor unique, ha mindkét oldal unique
        UcpExpr::Add(left, right) => {
            expression_is_unique(left, facts) && expression_is_unique(right, facts)
        }
        //Szorzás akkor unique, ha valamelyik oldal nulla, vagy mindkét oldal unique
        UcpExpr::Mul(left, right) => {
            is_zero_constant(left)
                || is_zero_constant(right)
                || (expression_is_unique(left, facts) && expression_is_unique(right, facts))
        }
    }
}

//Assign-szerű szabály: zero equationből egyetlen ismeretlen cellát próbál unique-nak bizonyítani
pub fn infer_assigned_cell_from_zero_equation(expr: &UcpExpr, facts: &UcpFacts) -> Option<CellId> {
    let analysis = analyze_assign_candidate(expr, facts);

    if analysis.valid {
        analysis.candidate
    } else {
        None
    }
}

//Az assign elemzés eredménye: van-e egyetlen candidate, és biztonságos-e a következtetés
#[derive(Clone, Debug, Eq, PartialEq)]
struct AssignAnalysis {
    candidate: Option<CellId>,
    valid: bool,
}

impl AssignAnalysis {
    //Nincs ismeretlen candidate, de az elemzés érvényes
    fn none() -> Self {
        Self {
            candidate: None,
            valid: true,
        }
    }

    //Pontosan egy lehetséges candidate cellát találtunk
    fn candidate(cell: CellId) -> Self {
        Self {
            candidate: Some(cell),
            valid: true,
        }
    }

    //Érvénytelen elemzés, mert nem biztonságos belőle következtetni
    fn invalid() -> Self {
        Self {
            candidate: None,
            valid: false,
        }
    }

    //Összeadás két oldalának assign elemzését egyesíti
    fn merge_add(self, other: Self) -> Self {
        if !self.valid || !other.valid {
            return Self::invalid();
        }

        match (self.candidate, other.candidate) {
            //Egyik oldalon sincs ismeretlen candidate
            (None, None) => Self::none(),
            //Pontosan az egyik oldalon van candidate
            (Some(cell), None) | (None, Some(cell)) => Self::candidate(cell),
            //Mindkét oldalon van candidate, ez már több ismeretlen, ezért nem biztonságos
            (Some(_), Some(_)) => Self::invalid(),
        }
    }
}

//Megkeresi, hogy az expressionben pontosan egy lineáris ismeretlen cella van-e
fn analyze_assign_candidate(expr: &UcpExpr, facts: &UcpFacts) -> AssignAnalysis {
    //Ha az egész expression már unique, nincs új candidate
    if expression_is_unique(expr, facts) {
        return AssignAnalysis::none();
    }

    match expr {
        //Nem unique változó candidate lehet
        UcpExpr::Var(cell) => AssignAnalysis::candidate(cell.clone()),
        //Konstansból nem lesz candidate
        UcpExpr::Const(_) => AssignAnalysis::none(),
        //Negálás nem változtatja meg a candidate-et
        UcpExpr::Neg(inner) => analyze_assign_candidate(inner, facts),
        //Skálázásnál csak biztosan nem nulla skála mellett lehet továbbmenni
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => AssignAnalysis::none(),
            UcpScalar::NonZero | UcpScalar::Known(_) => analyze_assign_candidate(inner, facts),
            UcpScalar::Unknown => AssignAnalysis::invalid(),
        },
        //Összeadásnál a két oldal candidate-jeit össze kell fésülni
        UcpExpr::Add(left, right) => {
            analyze_assign_candidate(left, facts).merge_add(analyze_assign_candidate(right, facts))
        }
        //Szorzásnál csak speciális, biztonságos esetekből tanulunk
        UcpExpr::Mul(left, right) => analyze_product_assign_candidate(left, right, facts),
    }
}

//Szorzatból próbál assign candidate-et kinyerni
fn analyze_product_assign_candidate(
    left: &UcpExpr,
    right: &UcpExpr,
    facts: &UcpFacts,
) -> AssignAnalysis {
    //Ha valamelyik oldal nulla, a szorzatból nincs új információ
    if is_zero_constant(left) || is_zero_constant(right) {
        return AssignAnalysis::none();
    }

    //Ha mindkét oldal unique, nincs új candidate
    if expression_is_unique(left, facts) && expression_is_unique(right, facts) {
        return AssignAnalysis::none();
    }

    //Nem nulla konstanssal szorzás mellett a másik oldal candidate-je számít
    if is_non_zero_constant(left) {
        return analyze_assign_candidate(right, facts);
    }

    //Nem nulla konstanssal szorzás mellett a másik oldal candidate-je számít
    if is_non_zero_constant(right) {
        return analyze_assign_candidate(left, facts);
    }

    //Általános szorzatból nem következtetünk, mert nem biztonságos
    AssignAnalysis::invalid()
}

//Ellenőrzi, hogy az expression biztosan nulla konstans-e
fn is_zero_constant(expr: &UcpExpr) -> bool {
    matches!(expr, UcpExpr::Const(UcpScalar::Zero))
}

//Ellenőrzi, hogy az expression biztosan nem nulla konstans-e
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

    //Azt ellenőrzi, hogy a konstans expression mindig unique
    #[test]
    fn const_rule_marks_constants_unique() {
        let facts = UcpFacts::new();

        assert!(expression_is_unique(&UcpExpr::constant(), &facts));
    }

    //Azt ellenőrzi, hogy változó csak akkor unique, ha szerepel a K halmazban
    #[test]
    fn var_rule_uses_known_unique_cells() {
        let known = CellId::advice(0, 3);
        let unknown = CellId::advice(1, 3);
        let facts = UcpFacts::from_iter([known.clone()]);

        assert!(expression_is_unique(&UcpExpr::var(known), &facts));
        assert!(!expression_is_unique(&UcpExpr::var(unknown), &facts));
    }

    //Azt ellenőrzi, hogy művelet csak unique operandusokból lesz unique
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

    //Azt ellenőrzi, hogy nulla szorzat unique akkor is, ha a másik oldal nem unique
    #[test]
    fn zero_product_is_unique() {
        let x = CellId::advice(0, 0);
        let facts = UcpFacts::new();
        let expr = UcpExpr::mul(UcpExpr::zero(), UcpExpr::var(x));

        assert!(expression_is_unique(&expr, &facts));
    }

    //Azt ellenőrzi, hogy negálás és nem nulla skálázás megőrzi a uniqueness-t
    #[test]
    fn unary_ops_preserve_uniqueness() {
        let x = CellId::instance(0, 0);
        let facts = UcpFacts::from_iter([x.clone()]);
        let expr = UcpExpr::neg(UcpExpr::scale(UcpExpr::var(x)));

        assert!(expression_is_unique(&expr, &facts));
    }

    //Azt ellenőrzi, hogy egyetlen lineáris ismeretlen cella assign szabállyal kikövetkeztethető
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

    //Azt ellenőrzi, hogy ismeretlen skalár mellett az assign szabály nem következtet
    #[test]
    fn assign_rule_rejects_unknown_scalar() {
        let advice = CellId::advice(0, 0);
        let facts = UcpFacts::new();
        let expr = UcpExpr::scale_by(UcpExpr::var(advice), UcpScalar::Unknown);

        assert_eq!(infer_assigned_cell_from_zero_equation(&expr, &facts), None);
    }

    //Azt ellenőrzi, hogy több ismeretlen cella esetén nincs biztonságos assign következtetés
    #[test]
    fn assign_rule_rejects_multiple_unknowns() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let facts = UcpFacts::new();
        let expr = UcpExpr::add(UcpExpr::var(x), UcpExpr::var(y));

        assert_eq!(infer_assigned_cell_from_zero_equation(&expr, &facts), None);
    }
}
