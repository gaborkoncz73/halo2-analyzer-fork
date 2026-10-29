// A K alapján ellenőrzi az egyértelműséget; konkrét értéket nem számít, és K-t nem módosítja.

use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
    facts::UcpFacts,
};
use num_bigint::BigInt;

// A QED² kifejezésszintű egyértelműségi szabályait alkalmazza.
//A true igazolt egyértelműséget jelent; a false csak azt, hogy ezek a szabályok nem igazolták.
pub fn expression_is_unique(expr: &UcpExpr, facts: &UcpFacts) -> bool {
    match expr {
        // A változót akkor tekinti egyértelműnek, ha szerepel K-ban.
        UcpExpr::Var(cell) => facts.is_unique(cell),
        //A konstans értéke rögzített, akkor is, ha az elemző a konkrét számát nem ismeri.
        UcpExpr::Const(_) => true,
        // Negálásnál megőrzi a belső kifejezés egyértelműségét.
        UcpExpr::Neg(inner) => expression_is_unique(inner, facts),
        // Nullával skálázásnál egyértelműséget jelez; máskor a belső kifejezést vizsgálja.
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => true,
            UcpScalar::Known(value) if value == &BigInt::from(0) => true,
            UcpScalar::NonZero | UcpScalar::Unknown | UcpScalar::Known(_) => {
                expression_is_unique(inner, facts)
            }
        },
        // Összegnél mindkét oldal egyértelműségét megköveteli.
        UcpExpr::Add(left, right) => {
            expression_is_unique(left, facts) && expression_is_unique(right, facts)
        }
        // Szorzatnál nullatényező vagy két egyértelmű tényező esetén jelez egyértelműséget.
        UcpExpr::Mul(left, right) => {
            is_zero_constant(left)
                || is_zero_constant(right)
                || (expression_is_unique(left, facts) && expression_is_unique(right, facts))
        }
    }
}

// Az Assign szabállyal egy nullával egyenlő kifejezés egyetlen ismeretlen celláját keresi.
//A hívó adja a premisszát, hogy expr = 0 kényszer. A visszaadott cellát az engine teheti K-ba.
pub fn infer_assigned_cell_from_zero_equation(expr: &UcpExpr, facts: &UcpFacts) -> Option<CellId> {
    infer_assigned_cell_with_optional_modulus(expr, facts, None)
}

pub fn infer_assigned_cell_from_zero_equation_with_modulus(
    expr: &UcpExpr,
    facts: &UcpFacts,
    modulus: &BigInt,
) -> Option<CellId> {
    if modulus <= &BigInt::from(1) {
        return None;
    }
    infer_assigned_cell_with_optional_modulus(expr, facts, Some(modulus))
}

fn infer_assigned_cell_with_optional_modulus(
    expr: &UcpExpr,
    facts: &UcpFacts,
    modulus: Option<&BigInt>,
) -> Option<CellId> {
    let analysis = analyze_assign_candidate(expr, facts, modulus);

    if analysis.valid {
        analysis.candidate
    } else {
        None
    }
}

// Az Assign-elemzés érvényességét és esetleges jelöltcelláját tárolja.
//candidate=None, valid=true: nincs új cella; valid=false: a minta nem kezelhető biztonságosan.
#[derive(Clone, Debug, Eq, PartialEq)]
struct AssignAnalysis {
    candidate: Option<CellId>,
    valid: bool,
}

impl AssignAnalysis {
    // Új jelölt nélküli, érvényes elemzési eredményt készít.
    fn none() -> Self {
        Self {
            candidate: None,
            valid: true,
        }
    }

    // Pontosan egy jelöltcellát rögzítő eredményt készít.
    fn candidate(cell: CellId) -> Self {
        Self {
            candidate: Some(cell),
            valid: true,
        }
    }

    // Érvénytelen mintát jelez, amelyből nem következtet.
    fn invalid() -> Self {
        Self {
            candidate: None,
            valid: false,
        }
    }

    // Összeadásnál egyesíti a két oldal Assign-elemzését.
    fn merge_add(self, other: Self) -> Self {
        if !self.valid || !other.valid {
            return Self::invalid();
        }

        match (self.candidate, other.candidate) {
            // Új jelölt nélküli eredményt ad, ha egyik oldal sem tartalmaz ismeretlent.
            (None, None) => Self::none(),
            // Megtartja az egyetlen jelöltet, ha csak az egyik oldalon talál ilyet.
            (Some(cell), None) | (None, Some(cell)) => Self::candidate(cell),
            // Két jelöltelőfordulást nem von össze, akkor sem, ha ugyanaz a cella szerepel kétszer.
            (Some(_), Some(_)) => Self::invalid(),
        }
    }
}

// A kifejezésben egyetlen lineáris ismeretlen cellát keres.
fn analyze_assign_candidate(
    expr: &UcpExpr,
    facts: &UcpFacts,
    modulus: Option<&BigInt>,
) -> AssignAnalysis {
    // Az egészében egyértelmű kifejezésből nem keres új jelöltet.
    //Például a*x + e = 0 alakban e lehet egyértelmű konkrétan ismert érték nélkül is.
    if expression_is_unique(expr, facts) {
        return AssignAnalysis::none();
    }

    match expr {
        // A nem igazoltan egyértelmű változót jelöltként kezeli.
        UcpExpr::Var(cell) => AssignAnalysis::candidate(cell.clone()),
        // Konstansból nem képez jelöltet.
        UcpExpr::Const(_) => AssignAnalysis::none(),
        // Negálásnál a belső jelöltet tartja meg.
        UcpExpr::Neg(inner) => analyze_assign_candidate(inner, facts, modulus),
        //Skálázásnál csak biztosan nem nulla skála mellett lehet továbbmenni
        UcpExpr::Scale(inner, scalar) => {
            if scalar.is_non_zero_with_modulus(modulus) {
                analyze_assign_candidate(inner, facts, modulus)
            } else if matches!(scalar, UcpScalar::Unknown) {
                AssignAnalysis::invalid()
            } else {
                AssignAnalysis::none()
            }
        }
        // Összeadásnál egyesíti a két oldal jelöltjeit.
        UcpExpr::Add(left, right) => analyze_assign_candidate(left, facts, modulus)
            .merge_add(analyze_assign_candidate(right, facts, modulus)),
        // Szorzásnál csak a biztonságosan visszafordítható esetekből következtet.
        UcpExpr::Mul(left, right) => analyze_product_assign_candidate(left, right, facts, modulus),
    }
}

// Szorzatból próbál Assign-jelöltet kinyerni.
fn analyze_product_assign_candidate(
    left: &UcpExpr,
    right: &UcpExpr,
    facts: &UcpFacts,
    modulus: Option<&BigInt>,
) -> AssignAnalysis {
    //Ha valamelyik oldal nulla, a szorzatból nincs új információ
    if is_zero_constant(left) || is_zero_constant(right) {
        return AssignAnalysis::none();
    }

    // Két egyértelmű tényezőből nem keres új jelöltet.
    if expression_is_unique(left, facts) && expression_is_unique(right, facts) {
        return AssignAnalysis::none();
    }

    //Biztosan nem nulla konstanssal a szorzás visszafordítható; a modulusos vizsgálat is szükséges.
    if is_non_zero_constant(left, modulus) {
        return analyze_assign_candidate(right, facts, modulus);
    }

    // Nemnulla konstans tényező mellett a másik oldal jelöltjét vizsgálja.
    if is_non_zero_constant(right, modulus) {
        return analyze_assign_candidate(left, facts, modulus);
    }

    //A K-tagság önmagában nem garantál nemnullaságot: egy egyértelmű szorzó értéke lehet nulla.
    AssignAnalysis::invalid()
}

// Ellenőrzi, hogy a kifejezés biztosan nulla konstans-e.
fn is_zero_constant(expr: &UcpExpr) -> bool {
    matches!(expr, UcpExpr::Const(scalar) if scalar.is_zero())
}

// Ellenőrzi, hogy a kifejezés biztosan nemnulla konstans-e.
fn is_non_zero_constant(expr: &UcpExpr, modulus: Option<&BigInt>) -> bool {
    matches!(expr, UcpExpr::Const(scalar) if scalar.is_non_zero_with_modulus(modulus))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit_analyzer::ucp::cell::CellId;

    // A teszt ellenőrzi, hogy a konstanskifejezést egyértelműnek tekinti.
    #[test]
    fn const_rule_marks_constants_unique() {
        let facts = UcpFacts::new();

        assert!(expression_is_unique(&UcpExpr::constant(), &facts));
    }

    // A teszt ellenőrzi, hogy a változót csak K-tagság mellett tekinti egyértelműnek.
    #[test]
    fn var_rule_uses_known_unique_cells() {
        let known = CellId::advice(0, 3);
        let unknown = CellId::advice(1, 3);
        let facts = UcpFacts::from_iter([known.clone()]);

        assert!(expression_is_unique(&UcpExpr::var(known), &facts));
        assert!(!expression_is_unique(&UcpExpr::var(unknown), &facts));
    }

    // A teszt ellenőrzi az egyértelmű operandusokból történő következtetést.
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

    // A teszt ellenőrzi, hogy nullatényező mellett a szorzatot egyértelműnek tekinti.
    #[test]
    fn zero_product_is_unique() {
        let x = CellId::advice(0, 0);
        let facts = UcpFacts::new();
        let expr = UcpExpr::mul(UcpExpr::zero(), UcpExpr::var(x));

        assert!(expression_is_unique(&expr, &facts));
    }

    // A teszt ellenőrzi, hogy a negálás és a nemnulla skálázás megőrzi az egyértelműséget.
    #[test]
    fn unary_ops_preserve_uniqueness() {
        let x = CellId::instance(0, 0);
        let facts = UcpFacts::from_iter([x.clone()]);
        let expr = UcpExpr::neg(UcpExpr::scale(UcpExpr::var(x)));

        assert!(expression_is_unique(&expr, &facts));
    }

    // A teszt ellenőrzi az egyetlen lineáris ismeretlen kikövetkeztetését az Assign szabállyal.
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

    // A teszt ellenőrzi, hogy ismeretlen skálánál az Assign szabály nem következtet.
    #[test]
    fn assign_rule_rejects_unknown_scalar() {
        let advice = CellId::advice(0, 0);
        let facts = UcpFacts::new();
        let expr = UcpExpr::scale_by(UcpExpr::var(advice), UcpScalar::Unknown);

        assert_eq!(infer_assigned_cell_from_zero_equation(&expr, &facts), None);
    }

    // A teszt ellenőrzi, hogy több ismeretlen esetén az Assign szabály nem ad jelöltet.
    #[test]
    fn assign_rule_rejects_multiple_unknowns() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let facts = UcpFacts::new();
        let expr = UcpExpr::add(UcpExpr::var(x), UcpExpr::var(y));

        assert_eq!(infer_assigned_cell_from_zero_equation(&expr, &facts), None);
    }
}
