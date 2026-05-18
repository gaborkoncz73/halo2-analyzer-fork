use std::fmt;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CellKind {
    Advice,
    Instance,
    Fixed,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CellId {
    pub kind: CellKind,
    pub column: usize,
    pub row: i32,
}

impl CellId {
    pub fn advice(column: usize, row: i32) -> Self {
        Self {
            kind: CellKind::Advice,
            column,
            row,
        }
    }

    pub fn instance(column: usize, row: i32) -> Self {
        Self {
            kind: CellKind::Instance,
            column,
            row,
        }
    }

    pub fn fixed(column: usize, row: i32) -> Self {
        Self {
            kind: CellKind::Fixed,
            column,
            row,
        }
    }
}

impl fmt::Display for CellId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = match self.kind {
            CellKind::Advice => "A",
            CellKind::Instance => "I",
            CellKind::Fixed => "F",
        };
        write!(f, "{}-{}-{}", prefix, self.column, self.row)
    }
}
