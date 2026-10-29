use super::{
    cell::{CellId, CellKind},
    expr::UcpExpr,
};
use std::collections::HashSet;

// A dolgozatbeli K halmazban az igazoltan egyértelmű cellákat tárolja.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UcpFacts {
    unique_cells: HashSet<CellId>,
}

impl UcpFacts {
    // Üres K halmazt hoz létre.
    pub fn new() -> Self {
        Self::default()
    }

    // A cellát egyértelműként jelöli; új elem bejegyzésekor igazat ad vissza.
    pub fn mark_unique(&mut self, cell: CellId) -> bool {
        self.unique_cells.insert(cell)
    }

    //Kezdeti K-ba csak instance és fixed cella kerülhet, advice-ot bizonyítani kell
    pub fn mark_initial_unique(&mut self, cell: CellId) -> bool {
        match cell.kind {
            CellKind::Instance | CellKind::Fixed => self.mark_unique(cell),
            CellKind::Advice => false,
        }
    }

    //Ellenőrzi, hogy egy cella szerepel-e a K halmazban
    pub fn is_unique(&self, cell: &CellId) -> bool {
        self.unique_cells.contains(cell)
    }

    // Visszaadja az összes igazoltan egyértelmű cellát.
    pub fn unique_cells(&self) -> &HashSet<CellId> {
        &self.unique_cells
    }
}

//Instance és fixed cellákból létrehozza a kezdeti K halmazt
pub fn initial_facts<I, F>(instance_cells: I, fixed_cells: F) -> UcpFacts
where
    I: IntoIterator<Item = CellId>,
    F: IntoIterator<Item = CellId>,
{
    let mut facts = UcpFacts::new();

    for cell in instance_cells {
        facts.mark_initial_unique(cell);
    }

    for cell in fixed_cells {
        facts.mark_initial_unique(cell);
    }

    facts
}

// A kifejezésekből kigyűjti a kezdeti K-ba felvehető instance és fixed cellákat.
pub fn initial_facts_from_expressions<'a, I>(expressions: I) -> UcpFacts
where
    I: IntoIterator<Item = &'a UcpExpr>,
{
    let mut facts = UcpFacts::new();

    for expr in expressions {
        collect_initial_facts(expr, &mut facts);
    }

    facts
}

// Rekurzívan bejárja a kifejezést, és csak a kezdetben egyértelmű cellákat gyűjti ki.
fn collect_initial_facts(expr: &UcpExpr, facts: &mut UcpFacts) {
    match expr {
        UcpExpr::Var(cell) => {
            facts.mark_initial_unique(cell.clone());
        }
        UcpExpr::Const(_) => {}
        UcpExpr::Neg(inner) | UcpExpr::Scale(inner, _) => collect_initial_facts(inner, facts),
        UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
            collect_initial_facts(left, facts);
            collect_initial_facts(right, facts);
        }
    }
}

//Lehetővé teszi, hogy cellalistából közvetlenül UcpFacts készüljön
impl FromIterator<CellId> for UcpFacts {
    fn from_iter<T: IntoIterator<Item = CellId>>(iter: T) -> Self {
        Self {
            unique_cells: HashSet::from_iter(iter),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    //Azt ellenőrzi, hogy az instance és fixed cellák bekerülnek a kezdeti K halmazba
    #[test]
    fn initial_facts_include_instance_and_fixed_cells() {
        let instance = CellId::instance(0, 0);
        let fixed = CellId::fixed(1, 2);

        let facts = initial_facts([instance.clone()], [fixed.clone()]);

        assert!(facts.is_unique(&instance));
        assert!(facts.is_unique(&fixed));
        assert_eq!(facts.unique_cells().len(), 2);
    }

    //Azt ellenőrzi, hogy advice cella nem kerül be automatikusan a kezdeti K-ba
    #[test]
    fn initial_facts_ignore_advice_cells() {
        let advice = CellId::advice(0, 0);
        let fixed = CellId::fixed(0, 0);

        let facts = initial_facts([advice.clone()], [fixed.clone()]);

        assert!(!facts.is_unique(&advice));
        assert!(facts.is_unique(&fixed));
        assert_eq!(facts.unique_cells().len(), 1);
    }

    // A teszt ellenőrzi, hogy a kifejezésekből csak instance és fixed cellát vesz fel kezdeti tényként.
    #[test]
    fn initial_facts_from_expressions_collect_instance_and_fixed_only() {
        let instance = CellId::instance(0, 0);
        let fixed = CellId::fixed(1, 0);
        let advice = CellId::advice(2, 0);
        let expressions = vec![UcpExpr::add(
            UcpExpr::var(instance.clone()),
            UcpExpr::mul(UcpExpr::var(fixed.clone()), UcpExpr::var(advice.clone())),
        )];

        let facts = initial_facts_from_expressions(&expressions);

        assert!(facts.is_unique(&instance));
        assert!(facts.is_unique(&fixed));
        assert!(!facts.is_unique(&advice));
        assert_eq!(facts.unique_cells().len(), 2);
    }
}
