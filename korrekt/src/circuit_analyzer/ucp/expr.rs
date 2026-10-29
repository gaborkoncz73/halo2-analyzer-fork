//Kifejezésfák és skalártulajdonságok; a kiértékelés és a következtetés más modulok feladata.

use super::cell::CellId;
use num_bigint::BigInt;

//Skalár/konstans érték absztrakt reprezentációja UCP-hez
//A NonZero csak tulajdonságot közöl, a Known konkrét számot is. Ez nem celladomain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpScalar {
    //Biztosan nulla érték
    Zero,
    //Biztosan nem nulla, de a konkrét érték nem ismert
    NonZero,
    // A rendszer nem ismeri a skalár nulla vagy nemnulla voltát.
    Unknown,
    //Konkrétan ismert BigInt érték
    Known(BigInt),
}

impl UcpScalar {
    //Konkrét értékből UcpScalar-t készít, a nullát külön Zero-ként tárolva
    //Itt még nincs testmodulus
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
    //A None nem nullát jelent, hanem azt, hogy nincs kiolvasható konkrét szám.
    pub fn as_known(&self) -> Option<BigInt> {
        match self {
            Self::Zero => Some(BigInt::from(0)),
            Self::Known(value) => Some(value.clone()),
            Self::NonZero | Self::Unknown => None,
        }
    }

    //Azt jelzi, hogy a skalár statikusan biztosan nem nulla-e
    //A Known értékét egész számként vizsgálja; testbeli egyszerűsítéshez a modulusos változat kell.
    pub fn is_statically_non_zero(&self) -> bool {
        match self {
            Self::NonZero => true,
            Self::Known(value) => value != &BigInt::from(0),
            Self::Zero | Self::Unknown => false,
        }
    }

    pub(crate) fn is_zero(&self) -> bool {
        matches!(self, Self::Zero)
            || matches!(self, Self::Known(value) if value == &BigInt::from(0))
    }

    //Known(p)-vel nem szabad osztani a p modulusú testben, mert ott az értéke nulla.
    pub(crate) fn is_non_zero_with_modulus(&self, modulus: Option<&BigInt>) -> bool {
        match (self, modulus) {
            (Self::Known(value), Some(modulus)) => {
                modulus > &BigInt::from(1) && value % modulus != BigInt::from(0)
            }
            _ => self.is_statically_non_zero(),
        }
    }
}

// A Halo2-kifejezéseket egyszerű UCP-kifejezésfával reprezentálja.
//A Box miatt a csomópont tárolhat újabb UcpExpr-t anélkül, hogy a típus mérete végtelen lenne.
//Például 2*x + y egy Add csomópont, benne egy skálázott Var(x) és egy Var(y).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpExpr {
    //Cella/változó hivatkozás
    Var(CellId),
    //Konstans vagy absztrakt skalár érték
    Const(UcpScalar),
    // A belső kifejezés negáltját jelöli.
    Neg(Box<UcpExpr>),
    //Összeadás
    Add(Box<UcpExpr>, Box<UcpExpr>),
    //Szorzás
    Mul(Box<UcpExpr>, Box<UcpExpr>),
    //A Mul két részfát szoroz; a Scale külön kezeli a skalár együtthatót.
    Scale(Box<UcpExpr>, UcpScalar),
}

impl UcpExpr {
    //Az építőfüggvények csak helyi azonosságokat egyszerűsítenek, nem oldanak meg egyenleteket.
    // Cellahivatkozásból változókifejezést készít.
    pub fn var(cell: CellId) -> Self {
        Self::Var(cell)
    }

    //Ismeretlen értékű konstans, nem új advice változó.
    pub fn constant() -> Self {
        Self::Const(UcpScalar::Unknown)
    }

    // Nulla értékű konstanscsomópontot készít.
    pub fn zero() -> Self {
        Self::Const(UcpScalar::Zero)
    }

    // Nemnulla, de konkrétan ismeretlen konstanscsomópontot készít.
    pub fn non_zero_constant() -> Self {
        Self::Const(UcpScalar::NonZero)
    }

    // Konkrét ismert értékből konstanscsomópontot készít.
    pub fn known_constant(value: BigInt) -> Self {
        Self::Const(UcpScalar::known(value))
    }

    // i64 értékből konstanscsomópontot készít.
    pub fn known_constant_i64(value: i64) -> Self {
        Self::known_constant(BigInt::from(value))
    }

    // Tetszőleges UcpScalar értékből konstanskifejezést készít.
    pub fn scalar_constant(scalar: UcpScalar) -> Self {
        if scalar.is_zero() {
            Self::zero()
        } else {
            Self::Const(scalar)
        }
    }

    // A megadott kifejezés negáltját készíti el.
    pub fn neg(expr: UcpExpr) -> Self {
        match expr {
            Self::Const(UcpScalar::Zero) => Self::zero(),
            expr => Self::Neg(Box::new(expr)),
        }
    }

    // Két kifejezés összegét készíti el.
    pub fn add(left: UcpExpr, right: UcpExpr) -> Self {
        match (left, right) {
            (Self::Const(UcpScalar::Zero), right) => right,
            (left, Self::Const(UcpScalar::Zero)) => left,
            (left, right) => Self::Add(Box::new(left), Box::new(right)),
        }
    }

    // Két kifejezés szorzatát készíti el.
    //A 0*e, 1*e és (-1)*e alakokat rögtön rövidebb fára cseréli; más szorzatot megtart.
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
            (left, right) => Self::Mul(Box::new(left), Box::new(right)),
        }
    }

    //Nem nulla, de konkrétan nem ismert skálával szoroz
    //Ez nem egységgel szorzás: a tényleges együttható ismeretlen marad.
    pub fn scale(expr: UcpExpr) -> Self {
        Self::scale_by(expr, UcpScalar::NonZero)
    }

    // Skálázott kifejezést készít; nulla együtthatónál azonnal nullára egyszerűsít.
    pub fn scale_by(expr: UcpExpr, scalar: UcpScalar) -> Self {
        if scalar.is_zero() {
            return Self::zero();
        }
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
