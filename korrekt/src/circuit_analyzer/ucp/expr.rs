use super::cell::CellId;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UcpScalar {
    Zero,
    NonZero,
    Unknown,
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
            UcpScalar::NonZero | UcpScalar::Unknown => Self::Scale(Box::new(expr), scalar),
        }
    }
}
