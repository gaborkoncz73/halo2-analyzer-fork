use super::cell::{CellId, CellKind};
use std::collections::HashSet;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UcpFacts {
    unique_cells: HashSet<CellId>,
}

impl UcpFacts {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn mark_unique(&mut self, cell: CellId) -> bool {
        self.unique_cells.insert(cell)
    }

    /// Adds a cell to the initial UCP fact set if it is part of the public
    /// environment: public instance input or fixed circuit data. Advice cells
    /// are intentionally ignored because UCP must prove those from the inputs.
    pub fn mark_initial_unique(&mut self, cell: CellId) -> bool {
        match cell.kind {
            CellKind::Instance | CellKind::Fixed => self.mark_unique(cell),
            CellKind::Advice => false,
        }
    }

    pub fn is_unique(&self, cell: &CellId) -> bool {
        self.unique_cells.contains(cell)
    }

    pub fn unique_cells(&self) -> &HashSet<CellId> {
        &self.unique_cells
    }
}

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

    #[test]
    fn initial_facts_include_instance_and_fixed_cells() {
        let instance = CellId::instance(0, 0);
        let fixed = CellId::fixed(1, 2);

        let facts = initial_facts([instance.clone()], [fixed.clone()]);

        assert!(facts.is_unique(&instance));
        assert!(facts.is_unique(&fixed));
        assert_eq!(facts.unique_cells().len(), 2);
    }

    #[test]
    fn initial_facts_ignore_advice_cells() {
        let advice = CellId::advice(0, 0);
        let fixed = CellId::fixed(0, 0);

        let facts = initial_facts([advice.clone()], [fixed.clone()]);

        assert!(!facts.is_unique(&advice));
        assert!(facts.is_unique(&fixed));
        assert_eq!(facts.unique_cells().len(), 1);
    }
}
