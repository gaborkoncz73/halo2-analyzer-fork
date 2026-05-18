use super::cell::CellId;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpExpr {
    Var(CellId),
    Const,
    Neg(Box<UcpExpr>),
    Add(Box<UcpExpr>, Box<UcpExpr>),
    Mul(Box<UcpExpr>, Box<UcpExpr>),
    Scale(Box<UcpExpr>),
}

impl UcpExpr {
    pub fn var(cell: CellId) -> Self {
        Self::Var(cell)
    }

    pub fn constant() -> Self {
        Self::Const
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
        Self::Scale(Box::new(expr))
    }
}
