use super::cell::CellId;
use num_bigint::BigInt;

//Skalár/konstans érték absztrakt reprezentációja UCP-hez
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpScalar {
    //Biztosan nulla érték
    Zero,
    //Biztosan nem nulla, de a konkrét érték nem ismert
    NonZero,
    //Nem tudjuk, hogy nulla-e vagy nem nulla
    Unknown,
    //Konkrétan ismert kis integer érték
    Known(BigInt),
}

impl UcpScalar {
    //Konkrét értékből UcpScalar-t készít, a nullát külön Zero-ként tárolva
    pub fn known(value: BigInt) -> Self {
        if value == BigInt::from(0) {
            Self::Zero
        } else {
            Self::Known(value)
        }
    }

    //Kényelmi függvény i64 értékből ismert skalár létrehozására
    pub fn known_i64(value: i64) -> Self {
        Self::known(BigInt::from(value))
    }

    //Visszaadja a konkrét értéket, ha ténylegesen ismert
    pub fn as_known(&self) -> Option<BigInt> {
        match self {
            Self::Zero => Some(BigInt::from(0)),
            Self::Known(value) => Some(value.clone()),
            Self::NonZero | Self::Unknown => None,
        }
    }

    //Azt jelzi, hogy a skalár statikusan biztosan nem nulla-e
    pub fn is_statically_non_zero(&self) -> bool {
        matches!(self, Self::NonZero | Self::Known(_))
    }
}

//A Halo2 expressionökből képzett egyszerű UCP expression fa
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpExpr {
    //Cella/változó hivatkozás
    Var(CellId),
    //Konstans vagy absztrakt skalár érték
    Const(UcpScalar),
    //Negált expression
    Neg(Box<UcpExpr>),
    //Összeadás
    Add(Box<UcpExpr>, Box<UcpExpr>),
    //Szorzás
    Mul(Box<UcpExpr>, Box<UcpExpr>),
    //Expression skálázása egy skalárral
    Scale(Box<UcpExpr>, UcpScalar),
}

impl UcpExpr {
    //Változó expression létrehozása cellából
    pub fn var(cell: CellId) -> Self {
        Self::Var(cell)
    }

    //Ismeretlen konstans létrehozása
    pub fn constant() -> Self {
        Self::Const(UcpScalar::Unknown)
    }

    //Nulla konstans létrehozása
    pub fn zero() -> Self {
        Self::Const(UcpScalar::Zero)
    }

    //Nem nulla, de konkrétan nem ismert konstans létrehozása
    pub fn non_zero_constant() -> Self {
        Self::Const(UcpScalar::NonZero)
    }

    //Konkrét ismert konstans létrehozása
    pub fn known_constant(value: BigInt) -> Self {
        Self::Const(UcpScalar::known(value))
    }

    //Kényelmi függvény i64 konstans létrehozására
    pub fn known_constant_i64(value: i64) -> Self {
        Self::known_constant(BigInt::from(value))
    }

    //Tetszőleges UcpScalar-ból konstans expressiont készít
    pub fn scalar_constant(scalar: UcpScalar) -> Self {
        Self::Const(scalar)
    }

    //Negált expression létrehozása
    pub fn neg(expr: UcpExpr) -> Self {
        match expr {
            Self::Const(UcpScalar::Zero) => Self::zero(),
            Self::Const(UcpScalar::Known(value)) => Self::known_constant(-value),
            expr => Self::Neg(Box::new(expr)),
        }
    }

    //Két expression összeadásának létrehozása
    pub fn add(left: UcpExpr, right: UcpExpr) -> Self {
        match (left, right) {
            (Self::Const(UcpScalar::Zero), right) => right,
            (left, Self::Const(UcpScalar::Zero)) => left,
            (Self::Const(left), Self::Const(right)) => match (left.as_known(), right.as_known()) {
                (Some(left), Some(right)) => Self::known_constant(left + right),
                _ => Self::Add(Box::new(Self::Const(left)), Box::new(Self::Const(right))),
            },
            (left, right) => Self::Add(Box::new(left), Box::new(right)),
        }
    }

    //Két expression szorzatának létrehozása
    pub fn mul(left: UcpExpr, right: UcpExpr) -> Self {
        match (left, right) {
            (Self::Const(UcpScalar::Zero), _) | (_, Self::Const(UcpScalar::Zero)) => Self::zero(),
            (Self::Const(UcpScalar::Known(value)), expr) if value == BigInt::from(1) => expr,
            (expr, Self::Const(UcpScalar::Known(value))) if value == BigInt::from(1) => expr,
            (Self::Const(UcpScalar::Known(value)), expr) if value == BigInt::from(-1) => {
                Self::neg(expr)
            }
            (expr, Self::Const(UcpScalar::Known(value))) if value == BigInt::from(-1) => {
                Self::neg(expr)
            }
            (Self::Const(left), Self::Const(right)) => match (left.as_known(), right.as_known()) {
                (Some(left), Some(right)) => Self::known_constant(left * right),
                _ => Self::Mul(Box::new(Self::Const(left)), Box::new(Self::Const(right))),
            },
            (left, right) => Self::Mul(Box::new(left), Box::new(right)),
        }
    }

    //Nem nulla, de konkrétan nem ismert skálával szoroz
    pub fn scale(expr: UcpExpr) -> Self {
        Self::scale_by(expr, UcpScalar::NonZero)
    }

    //Expression skálázása, nulla skála esetén azonnal nulla expression lesz
    pub fn scale_by(expr: UcpExpr, scalar: UcpScalar) -> Self {
        match scalar {
            UcpScalar::Zero => Self::zero(),
            UcpScalar::Known(value) if value == BigInt::from(1) => expr,
            UcpScalar::Known(value) if value == BigInt::from(-1) => Self::neg(expr),
            UcpScalar::NonZero | UcpScalar::Unknown | UcpScalar::Known(_) => {
                Self::Scale(Box::new(expr), scalar)
            }
        }
    }
}
