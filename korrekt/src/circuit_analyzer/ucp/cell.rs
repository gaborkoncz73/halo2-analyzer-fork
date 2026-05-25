use std::fmt;

//A Halo2 cella típusát jelöli
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CellKind {
    //Witness/advice cella, amit bizonyítani kell
    Advice,
    //Public input cella, kezdetben unique-nak tekinthető
    Instance,
    //Fix oszlop cella, a circuit része, kezdetben unique-nak tekinthető
    Fixed,
}

//Egy konkrét cella azonosítója: típus, oszlop és sor
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CellId {
    pub kind: CellKind,
    pub column: usize,
    pub row: i32,
}

impl CellId {
    //Advice cella létrehozása
    pub fn advice(column: usize, row: i32) -> Self {
        Self {
            kind: CellKind::Advice,
            column,
            row,
        }
    }

    //Instance cella létrehozása
    pub fn instance(column: usize, row: i32) -> Self {
        Self {
            kind: CellKind::Instance,
            column,
            row,
        }
    }

    //Fixed cella létrehozása
    pub fn fixed(column: usize, row: i32) -> Self {
        Self {
            kind: CellKind::Fixed,
            column,
            row,
        }
    }
}

impl fmt::Display for CellId {
    //String alak: A-0-0, I-0-0 vagy F-0-0
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = match self.kind {
            CellKind::Advice => "A",
            CellKind::Instance => "I",
            CellKind::Fixed => "F",
        };
        write!(f, "{}-{}-{}", prefix, self.column, self.row)
    }
}
