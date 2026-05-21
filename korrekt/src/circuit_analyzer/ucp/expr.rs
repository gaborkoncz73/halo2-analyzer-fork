use super::cell::CellId;
use num_bigint::BigInt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpScalar {
    Zero,
    NonZero,
    Unknown,
    Known(BigInt),
}

impl UcpScalar {
    pub fn known(value: BigInt) -> Self {
        if value == BigInt::from(0) {
            Self::Zero
        } else {
            Self::Known(value)
        }
    }

    pub fn known_i64(value: i64) -> Self {
        Self::known(BigInt::from(value))
    }

    pub fn as_known(&self) -> Option<BigInt> {
        match self {
            Self::Zero => Some(BigInt::from(0)),
            Self::Known(value) => Some(value.clone()),
            Self::NonZero | Self::Unknown => None,
        }
    }

    pub fn is_statically_non_zero(&self) -> bool {
        matches!(self, Self::NonZero | Self::Known(_))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpExpr {
    Var(CellId),
    Const(UcpScalar),
    Neg(Box<UcpExpr>),
    Add(Box<UcpExpr>, Box<UcpExpr>),
    Mul(Box<UcpExpr>, Box<UcpExpr>),
    Scale(Box<UcpExpr>, UcpScalar),
}

impl UcpExpr {
    pub fn var(cell: CellId) -> Self {
        Self::Var(cell)
    }

    pub fn constant() -> Self {
        Self::Const(UcpScalar::Unknown)
    }

    pub fn zero() -> Self {
        Self::Const(UcpScalar::Zero)
    }

    pub fn non_zero_constant() -> Self {
        Self::Const(UcpScalar::NonZero)
    }

    pub fn known_constant(value: BigInt) -> Self {
        Self::Const(UcpScalar::known(value))
    }

    pub fn known_constant_i64(value: i64) -> Self {
        Self::known_constant(BigInt::from(value))
    }

    pub fn scalar_constant(scalar: UcpScalar) -> Self {
        Self::Const(scalar)
    }

    pub fn neg(expr: UcpExpr) -> Self {
        Self::Neg(Box::new(expr))
    }

    pub fn add(left: UcpExpr, right: UcpExpr) -> Self {
        Self::Add(Box::new(left), Box::new(right))
    }

    pub fn mul(left: UcpExpr, right: UcpExpr) -> Self {
        Self::Mul(Box::new(left), Box::new(right))
    }

    pub fn scale(expr: UcpExpr) -> Self {
        Self::scale_by(expr, UcpScalar::NonZero)
    }

    pub fn scale_by(expr: UcpExpr, scalar: UcpScalar) -> Self {
        match scalar {
            UcpScalar::Zero => Self::zero(),
            UcpScalar::NonZero | UcpScalar::Unknown | UcpScalar::Known(_) => {
                Self::Scale(Box::new(expr), scalar)
            }
        }
    }
}
