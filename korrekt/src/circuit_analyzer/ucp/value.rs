use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
};
use num_bigint::BigInt;
use std::collections::{BTreeSet, HashMap};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpValueDomain {
    Exact(BigInt),
    FiniteSet(BTreeSet<BigInt>),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UcpValueFacts {
    domains: HashMap<CellId, UcpValueDomain>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueKind {
    Zero,
    NonZero,
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearExpr {
    constant: BigInt,
    terms: HashMap<CellId, BigInt>,
}

impl UcpValueDomain {
    pub fn exact(value: BigInt) -> Self {
        Self::Exact(value)
    }

    pub fn finite_set<I>(values: I) -> Option<Self>
    where
        I: IntoIterator<Item = BigInt>,
    {
        let mut set = BTreeSet::new();

        for value in values {
            set.insert(bounded_value(value)?);
        }

        match set.len() {
            0 => None,
            1 => Some(Self::Exact(set.into_iter().next().unwrap())),
            _ => Some(Self::FiniteSet(set)),
        }
    }

    pub fn exact_value(&self) -> Option<&BigInt> {
        match self {
            Self::Exact(value) => Some(value),
            Self::FiniteSet(_) => None,
        }
    }

    pub fn is_singleton(&self) -> bool {
        matches!(self, Self::Exact(_))
    }

    fn intersect(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::Exact(left), Self::Exact(right)) if left == right => {
                Some(Self::Exact(left.clone()))
            }
            (Self::Exact(value), Self::FiniteSet(set))
            | (Self::FiniteSet(set), Self::Exact(value))
                if set.contains(value) =>
            {
                Some(Self::Exact(value.clone()))
            }
            (Self::FiniteSet(left), Self::FiniteSet(right)) => {
                Self::finite_set(left.intersection(right).cloned())
            }
            _ => None,
        }
    }

    fn value_kind(&self) -> ValueKind {
        match self {
            Self::Exact(value) if value == &BigInt::from(0) => ValueKind::Zero,
            Self::Exact(_) => ValueKind::NonZero,
            Self::FiniteSet(values) if values.iter().all(|value| value != &BigInt::from(0)) => {
                ValueKind::NonZero
            }
            _ => ValueKind::Unknown,
        }
    }
}

impl UcpValueFacts {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn mark_known(&mut self, cell: CellId, value: BigInt) -> bool {
        self.mark_domain(cell, UcpValueDomain::exact(value))
    }

    pub fn mark_domain(&mut self, cell: CellId, domain: UcpValueDomain) -> bool {
        let domain = match domain {
            UcpValueDomain::Exact(value) => UcpValueDomain::Exact(match bounded_value(value) {
                Some(value) => value,
                None => return false,
            }),
            UcpValueDomain::FiniteSet(values) => {
                let Some(domain) = UcpValueDomain::finite_set(values) else {
                    return false;
                };
                domain
            }
        };

        match self.domains.get(&cell) {
            Some(existing) => {
                let Some(intersection) = existing.intersect(&domain) else {
                    return false;
                };
                if &intersection == existing {
                    false
                } else {
                    self.domains.insert(cell, intersection);
                    true
                }
            }
            None => {
                self.domains.insert(cell, domain);
                true
            }
        }
    }

    pub fn known_value(&self, cell: &CellId) -> Option<&BigInt> {
        self.domains.get(cell)?.exact_value()
    }

    pub fn domain(&self, cell: &CellId) -> Option<&UcpValueDomain> {
        self.domains.get(cell)
    }

    pub fn domains(&self) -> &HashMap<CellId, UcpValueDomain> {
        &self.domains
    }

    pub fn known_values(&self) -> HashMap<CellId, BigInt> {
        self.domains
            .iter()
            .filter_map(|(cell, domain)| {
                domain
                    .exact_value()
                    .map(|value| (cell.clone(), value.clone()))
            })
            .collect()
    }
}

pub fn initial_values_from_instance_cells<'a, I>(instance_cells: I) -> UcpValueFacts
where
    I: IntoIterator<Item = (&'a String, &'a i64)>,
{
    let mut values = UcpValueFacts::new();

    for (name, value) in instance_cells {
        if let Some(cell) = parse_cell_id(name) {
            values.mark_known(cell, BigInt::from(*value));
        }
    }

    values
}

pub fn evaluate_expr(expr: &UcpExpr, values: &UcpValueFacts) -> Option<BigInt> {
    match expr {
        UcpExpr::Var(cell) => bounded_value(values.known_value(cell)?.clone()),
        UcpExpr::Const(scalar) => bounded_value(scalar.as_known()?),
        UcpExpr::Neg(inner) => bounded_value(-evaluate_expr(inner, values)?),
        UcpExpr::Add(left, right) => {
            bounded_value(evaluate_expr(left, values)? + evaluate_expr(right, values)?)
        }
        UcpExpr::Mul(left, right) => {
            bounded_value(evaluate_expr(left, values)? * evaluate_expr(right, values)?)
        }
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => Some(BigInt::from(0)),
            UcpScalar::Known(scale) => bounded_value(evaluate_expr(inner, values)? * scale),
            UcpScalar::NonZero | UcpScalar::Unknown => {
                let inner_value = evaluate_expr(inner, values)?;
                if inner_value == BigInt::from(0) {
                    Some(BigInt::from(0))
                } else {
                    None
                }
            }
        },
    }
}

fn bounded_value(value: BigInt) -> Option<BigInt> {
    if value == BigInt::from(0)
        || (value >= BigInt::from(i64::MIN) && value <= BigInt::from(i64::MAX))
    {
        Some(value)
    } else {
        None
    }
}

pub fn value_kind(expr: &UcpExpr, values: &UcpValueFacts) -> ValueKind {
    if let Some(value) = evaluate_expr(expr, values) {
        if value == BigInt::from(0) {
            ValueKind::Zero
        } else {
            ValueKind::NonZero
        }
    } else {
        match expr {
            UcpExpr::Var(cell) => values
                .domain(cell)
                .map(UcpValueDomain::value_kind)
                .unwrap_or(ValueKind::Unknown),
            UcpExpr::Const(UcpScalar::Zero) => ValueKind::Zero,
            UcpExpr::Const(UcpScalar::NonZero | UcpScalar::Known(_)) => ValueKind::NonZero,
            UcpExpr::Scale(_, UcpScalar::Zero) => ValueKind::Zero,
            UcpExpr::Mul(left, right) => {
                match (value_kind(left, values), value_kind(right, values)) {
                    (ValueKind::Zero, _) | (_, ValueKind::Zero) => ValueKind::Zero,
                    (ValueKind::NonZero, ValueKind::NonZero) => ValueKind::NonZero,
                    _ => ValueKind::Unknown,
                }
            }
            _ => ValueKind::Unknown,
        }
    }
}

pub fn infer_value_domains_from_zero_equation(
    expr: &UcpExpr,
    values: &UcpValueFacts,
) -> Vec<(CellId, UcpValueDomain)> {
    let mut inferences = Vec::new();

    if let Some((cell, domain)) = infer_root_domain(expr, values) {
        inferences.push((cell, domain));
    }

    if let Some((cell, value)) = infer_from_zero_expr(expr, values) {
        inferences.push((cell, UcpValueDomain::exact(value)));
    }

    inferences
}

pub fn infer_value_assignments_from_zero_equation(
    expr: &UcpExpr,
    values: &UcpValueFacts,
) -> Vec<(CellId, BigInt)> {
    infer_value_domains_from_zero_equation(expr, values)
        .into_iter()
        .filter_map(|(cell, domain)| match domain {
            UcpValueDomain::Exact(value) => Some((cell, value)),
            UcpValueDomain::FiniteSet(_) => None,
        })
        .collect()
}

fn infer_root_domain(expr: &UcpExpr, values: &UcpValueFacts) -> Option<(CellId, UcpValueDomain)> {
    let mut factors = Vec::new();
    collect_product_factors(expr, &mut factors);

    if factors.len() < 2 {
        return None;
    }

    let mut inferred_cell = None;
    let mut roots = BTreeSet::new();

    for factor in factors {
        let (cell, root) = factor_root(factor, values)?;

        match &inferred_cell {
            Some(existing) if existing != &cell => return None,
            None => inferred_cell = Some(cell),
            _ => {}
        }

        roots.insert(root);
    }

    Some((inferred_cell?, UcpValueDomain::finite_set(roots)?))
}

fn collect_product_factors<'a>(expr: &'a UcpExpr, factors: &mut Vec<&'a UcpExpr>) {
    match expr {
        UcpExpr::Mul(left, right) => {
            collect_product_factors(left, factors);
            collect_product_factors(right, factors);
        }
        UcpExpr::Neg(inner) => collect_product_factors(inner, factors),
        UcpExpr::Scale(inner, scalar) if scalar.is_statically_non_zero() => {
            collect_product_factors(inner, factors)
        }
        UcpExpr::Scale(_, UcpScalar::Zero) => {}
        _ => factors.push(expr),
    }
}

fn factor_root(factor: &UcpExpr, values: &UcpValueFacts) -> Option<(CellId, BigInt)> {
    let linear = linearize(factor, values)?;
    if linear.terms.len() != 1 {
        return None;
    }

    let (cell, coefficient) = linear.terms.into_iter().next().unwrap();
    if coefficient != BigInt::from(1) && coefficient != BigInt::from(-1) {
        return None;
    }

    let numerator = -linear.constant;
    if &numerator % &coefficient != BigInt::from(0) {
        return None;
    }

    Some((cell, bounded_value(numerator / coefficient)?))
}

fn infer_from_zero_expr(expr: &UcpExpr, values: &UcpValueFacts) -> Option<(CellId, BigInt)> {
    match expr {
        UcpExpr::Mul(left, right) => match (value_kind(left, values), value_kind(right, values)) {
            (ValueKind::NonZero, _) => infer_from_zero_expr(right, values),
            (_, ValueKind::NonZero) => infer_from_zero_expr(left, values),
            (ValueKind::Zero, _) | (_, ValueKind::Zero) => None,
            _ => infer_linear_assignment(expr, values),
        },
        UcpExpr::Scale(inner, scalar) if scalar.is_statically_non_zero() => {
            infer_from_zero_expr(inner, values)
        }
        UcpExpr::Scale(_, UcpScalar::Zero) => None,
        _ => infer_linear_assignment(expr, values),
    }
}

fn infer_linear_assignment(expr: &UcpExpr, values: &UcpValueFacts) -> Option<(CellId, BigInt)> {
    let linear = linearize(expr, values)?;

    if linear.terms.len() != 1 {
        return None;
    }

    let (cell, coefficient) = linear.terms.into_iter().next().unwrap();
    if coefficient == BigInt::from(0) {
        return None;
    }

    let numerator = -linear.constant;
    if &numerator % &coefficient != BigInt::from(0) {
        return None;
    }

    Some((cell, bounded_value(numerator / coefficient)?))
}

fn linearize(expr: &UcpExpr, values: &UcpValueFacts) -> Option<LinearExpr> {
    if let Some(value) = evaluate_expr(expr, values) {
        return Some(LinearExpr::constant(value));
    }

    match expr {
        UcpExpr::Var(cell) => Some(LinearExpr::term(cell.clone(), BigInt::from(1))),
        UcpExpr::Const(_) => None,
        UcpExpr::Neg(inner) => {
            linearize(inner, values).map(|linear| linear.scale(BigInt::from(-1)))
        }
        UcpExpr::Add(left, right) => Some(linearize(left, values)?.add(linearize(right, values)?)),
        UcpExpr::Mul(left, right) => {
            if let Some(value) = evaluate_expr(left, values) {
                return Some(linearize(right, values)?.scale(value));
            }
            if let Some(value) = evaluate_expr(right, values) {
                return Some(linearize(left, values)?.scale(value));
            }
            None
        }
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => Some(LinearExpr::constant(BigInt::from(0))),
            UcpScalar::Known(scale) => {
                Some(linearize(inner, values)?.scale(bounded_value(scale.clone())?))
            }
            UcpScalar::NonZero | UcpScalar::Unknown => None,
        },
    }
}

fn parse_cell_id(name: &str) -> Option<CellId> {
    let mut parts = name.split('-');
    let kind = parts.next()?;
    let column = parts.next()?.parse::<usize>().ok()?;
    let row = parts.next()?.parse::<i32>().ok()?;
    if parts.next().is_some() {
        return None;
    }

    match kind {
        "A" => Some(CellId::advice(column, row)),
        "I" => Some(CellId::instance(column, row)),
        "F" => Some(CellId::fixed(column, row)),
        _ => None,
    }
}

impl LinearExpr {
    fn constant(value: BigInt) -> Self {
        Self {
            constant: value,
            terms: HashMap::new(),
        }
    }

    fn term(cell: CellId, coefficient: BigInt) -> Self {
        Self {
            constant: BigInt::from(0),
            terms: HashMap::from([(cell, coefficient)]),
        }
    }

    fn add(mut self, other: Self) -> Self {
        self.constant += other.constant;
        for (cell, coefficient) in other.terms {
            let entry = self.terms.entry(cell).or_insert_with(|| BigInt::from(0));
            *entry += coefficient;
        }
        self.terms
            .retain(|_, coefficient| coefficient != &BigInt::from(0));
        self
    }

    fn scale(mut self, scalar: BigInt) -> Self {
        self.constant *= &scalar;
        for coefficient in self.terms.values_mut() {
            *coefficient *= &scalar;
        }
        self.terms
            .retain(|_, coefficient| coefficient != &BigInt::from(0));
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn finite_domain(values: &[i64]) -> UcpValueDomain {
        UcpValueDomain::finite_set(values.iter().map(|value| BigInt::from(*value))).unwrap()
    }

    #[test]
    fn evaluates_known_arithmetic_expression() {
        let x = CellId::instance(0, 0);
        let mut values = UcpValueFacts::new();
        values.mark_known(x.clone(), BigInt::from(2));
        let expr = UcpExpr::add(UcpExpr::var(x), UcpExpr::known_constant_i64(-1));

        assert_eq!(evaluate_expr(&expr, &values), Some(BigInt::from(1)));
        assert_eq!(value_kind(&expr, &values), ValueKind::NonZero);
    }

    #[test]
    fn learns_zero_from_nonzero_product_equation() {
        let x = CellId::instance(0, 0);
        let y = CellId::advice(1, 0);
        let mut values = UcpValueFacts::new();
        values.mark_known(x.clone(), BigInt::from(2));
        let nonzero = UcpExpr::add(UcpExpr::var(x), UcpExpr::known_constant_i64(-1));
        let expr = UcpExpr::mul(nonzero, UcpExpr::var(y.clone()));

        assert_eq!(
            infer_value_assignments_from_zero_equation(&expr, &values),
            vec![(y, BigInt::from(0))]
        );
    }

    #[test]
    fn learns_linear_assignment_value() {
        let x = CellId::advice(0, 0);
        let expr = UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(-5));

        assert_eq!(
            infer_value_assignments_from_zero_equation(&expr, &UcpValueFacts::new()),
            vec![(x, BigInt::from(5))]
        );
    }

    #[test]
    fn root_rule_learns_boolean_domain() {
        let b = CellId::advice(0, 0);
        let expr = UcpExpr::mul(
            UcpExpr::var(b.clone()),
            UcpExpr::add(UcpExpr::var(b.clone()), UcpExpr::known_constant_i64(-1)),
        );

        let inferences = infer_value_domains_from_zero_equation(&expr, &UcpValueFacts::new());

        assert_eq!(inferences, vec![(b, finite_domain(&[0, 1]))]);
    }

    #[test]
    fn root_rule_learns_exact_zero_from_square_zero() {
        let x = CellId::advice(0, 0);
        let expr = UcpExpr::mul(UcpExpr::var(x.clone()), UcpExpr::var(x.clone()));

        let inferences = infer_value_domains_from_zero_equation(&expr, &UcpValueFacts::new());

        assert_eq!(
            inferences,
            vec![(x, UcpValueDomain::exact(BigInt::from(0)))]
        );
    }

    #[test]
    fn intersecting_domain_can_refine_boolean_to_exact_value() {
        let b = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();

        assert!(values.mark_domain(b.clone(), finite_domain(&[0, 1])));
        assert!(values.mark_known(b.clone(), BigInt::from(1)));

        assert_eq!(values.known_value(&b), Some(&BigInt::from(1)));
    }
}
