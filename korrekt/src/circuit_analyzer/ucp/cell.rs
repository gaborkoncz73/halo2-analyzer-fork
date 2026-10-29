// A cellákat az értéküktől függetlenül azonosítja.

use std::fmt;

//A Halo2 cella típusát jelöli
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CellKind {
    // Az advice cellát jelöli; a szintézisben hozzárendelt privát értéket nem tekinti elemzési ténynek.
    Advice,
    //Publikus megfigyelés helye: bemenet, kimenet vagy publikált köztes eredmény is lehet.
    Instance,
    // A kapcsolás rögzített oszlopát jelöli; a ténylegesen hozzárendelt értéket nyilvános konstansként kezeli.
    Fixed,
}

//Egy konkrét cella azonosítója: típus, oszlop és sor
//Az Eq/Hash a teljes hármast használja, az Ord determinisztikus rendezést ad a tárolókban.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CellId {
    pub kind: CellKind,
    pub column: usize,
    //A rotáció feloldását és a sortartományra normalizálást nem ez a típus végzi.
    pub row: i32,
}

impl CellId {
    //Csak azonosítót készít: nem foglal Halo2-oszlopot és nem rendel cellaértéket.
    pub fn advice(column: usize, row: i32) -> Self {
        Self {
            kind: CellKind::Advice,
            column,
            row,
        }
    }

    //Instance cella azonosítója
    pub fn instance(column: usize, row: i32) -> Self {
        Self {
            kind: CellKind::Instance,
            column,
            row,
        }
    }

    //Fixed cella azonosítója
    pub fn fixed(column: usize, row: i32) -> Self {
        Self {
            kind: CellKind::Fixed,
            column,
            row,
        }
    }
}

impl fmt::Display for CellId {
    //Olvasható pozíciójelölés: A-0-0, I-0-0 vagy F-0-0; nem a tárolt érték.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = match self.kind {
            CellKind::Advice => "A",
            CellKind::Instance => "I",
            CellKind::Fixed => "F",
        };
        write!(f, "{}-{}-{}", prefix, self.column, self.row)
    }
}
