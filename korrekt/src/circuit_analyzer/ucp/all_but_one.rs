use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
    facts::UcpFacts,
    value::{evaluate_expr, UcpValueFacts},
};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AllButOneInference {
    pub cell: CellId,
    pub value: Option<BigInt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProductConstraint {
    y: CellId,
    x: CellId,
    root: BigInt,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SumConstraint {
    y_cells: Vec<CellId>,
    e_value: Option<BigInt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearExpr {
    constant: BigInt,
    terms: BTreeMap<CellId, BigInt>,
}

/// Implements the paper's All-But-One-0 UCP rule over the whole constraint set.
///
/// This is a multi-equation pattern:
/// - one sum equation: `sum(y_i) = e`, with `e` already unique;
/// - one zero-product equation per output: `y_i * (x - i) = 0`;
/// - `x` is already unique.
///
/// If those hold, every `y_i` is unique. When `x` and `e` also have exact
/// values in `Delta`, the inference carries exact values for `y_i` too.
pub fn infer_all_but_one_zero(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    values: &UcpValueFacts,
) -> Vec<AllButOneInference> {
    let product_constraints = collect_product_constraints(expressions, facts);
    let sum_constraints = collect_sum_constraints(expressions, facts, values);
    let mut inferences = BTreeMap::new();

    for sum in sum_constraints {
        for (x, products_by_y) in &product_constraints {
            let Some(root_by_y) = roots_for_sum(&sum, products_by_y) else {
                continue;
            };

            let x_value = values.known_value(x).cloned();

            for (cell, root) in root_by_y {
                let value = x_value.as_ref().and_then(|x_value| {
                    if &root == x_value {
                        sum.e_value.clone()
                    } else {
                        Some(BigInt::from(0))
                    }
                });

                inferences.entry(cell.clone()).or_insert(value);
            }
        }
    }

    inferences
        .into_iter()
        .map(|(cell, value)| AllButOneInference { cell, value })
        .collect()
}

fn collect_product_constraints(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
) -> HashMap<CellId, HashMap<CellId, BTreeSet<BigInt>>> {
    let mut constraints: HashMap<CellId, HashMap<CellId, BTreeSet<BigInt>>> = HashMap::new();

    for expr in expressions {
        let Some(product) = parse_product_constraint(expr) else {
            continue;
        };

        if !facts.is_unique(&product.x) {
            continue;
        }

        constraints
            .entry(product.x)
            .or_default()
            .entry(product.y)
            .or_default()
            .insert(product.root);
    }

    constraints
}

fn collect_sum_constraints(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    values: &UcpValueFacts,
) -> Vec<SumConstraint> {
    expressions
        .iter()
        .filter_map(|expr| parse_sum_constraint(expr, facts, values))
        .collect()
}

fn roots_for_sum(
    sum: &SumConstraint,
    products_by_y: &HashMap<CellId, BTreeSet<BigInt>>,
) -> Option<BTreeMap<CellId, BigInt>> {
    let mut root_by_y = BTreeMap::new();
    let mut roots = BTreeSet::new();

    for y in &sum.y_cells {
        let product_roots = products_by_y.get(y)?;
        if product_roots.len() != 1 {
            return None;
        }

        let root = product_roots.iter().next()?.clone();
        if !roots.insert(root.clone()) {
            return None;
        }

        root_by_y.insert(y.clone(), root);
    }

    Some(root_by_y)
}

fn parse_product_constraint(expr: &UcpExpr) -> Option<ProductConstraint> {
    let factors = meaningful_product_factors(expr);
    if factors.len() != 2 {
        return None;
    }

    parse_product_pair(factors[0], factors[1])
        .or_else(|| parse_product_pair(factors[1], factors[0]))
}

fn parse_product_pair(y_expr: &UcpExpr, root_expr: &UcpExpr) -> Option<ProductConstraint> {
    let y = parse_plain_var(y_expr)?;
    let (x, root) = parse_root_factor(root_expr)?;

    Some(ProductConstraint { y, x, root })
}

fn parse_sum_constraint(
    expr: &UcpExpr,
    facts: &UcpFacts,
    values: &UcpValueFacts,
) -> Option<SumConstraint> {
    let linear = linearize_zero_equation(expr, values)?;
    if linear.terms.len() < 2 {
        return None;
    }

    if linear
        .terms
        .values()
        .any(|coefficient| coefficient != &BigInt::from(1) && coefficient != &BigInt::from(-1))
    {
        return None;
    }

    let positive: Vec<CellId> = linear
        .terms
        .iter()
        .filter_map(|(cell, coefficient)| {
            if coefficient == &BigInt::from(1) {
                Some(cell.clone())
            } else {
                None
            }
        })
        .collect();
    let negative: Vec<CellId> = linear
        .terms
        .iter()
        .filter_map(|(cell, coefficient)| {
            if coefficient == &BigInt::from(-1) {
                Some(cell.clone())
            } else {
                None
            }
        })
        .collect();

    sum_from_signed_terms(positive, negative, linear.constant, facts, values)
}

fn sum_from_signed_terms(
    positive: Vec<CellId>,
    negative: Vec<CellId>,
    constant: BigInt,
    facts: &UcpFacts,
    values: &UcpValueFacts,
) -> Option<SumConstraint> {
    if positive.len() >= 2 && negative.is_empty() {
        return Some(SumConstraint {
            y_cells: positive,
            e_value: bounded_value(-constant),
        });
    }

    if negative.len() >= 2 && positive.is_empty() {
        return Some(SumConstraint {
            y_cells: negative,
            e_value: bounded_value(constant),
        });
    }

    if positive.len() >= 2 && negative.len() == 1 {
        let e = &negative[0];
        if !facts.is_unique(e) {
            return None;
        }

        let e_value = values
            .known_value(e)
            .and_then(|value| bounded_value(value - &constant));

        return Some(SumConstraint {
            y_cells: positive,
            e_value,
        });
    }

    if negative.len() >= 2 && positive.len() == 1 {
        let e = &positive[0];
        if !facts.is_unique(e) {
            return None;
        }

        let e_value = values
            .known_value(e)
            .and_then(|value| bounded_value(value + &constant));

        return Some(SumConstraint {
            y_cells: negative,
            e_value,
        });
    }

    None
}

fn meaningful_product_factors(expr: &UcpExpr) -> Vec<&UcpExpr> {
    let mut factors = Vec::new();
    collect_meaningful_product_factors(expr, &mut factors);
    factors
}

fn collect_meaningful_product_factors<'a>(expr: &'a UcpExpr, factors: &mut Vec<&'a UcpExpr>) {
    match expr {
        UcpExpr::Mul(left, right) => {
            collect_meaningful_product_factors(left, factors);
            collect_meaningful_product_factors(right, factors);
        }
        UcpExpr::Neg(inner) => collect_meaningful_product_factors(inner, factors),
        UcpExpr::Scale(inner, scalar) if scalar.is_statically_non_zero() => {
            collect_meaningful_product_factors(inner, factors)
        }
        UcpExpr::Const(UcpScalar::NonZero | UcpScalar::Known(_)) => {}
        UcpExpr::Scale(_, UcpScalar::Zero) | UcpExpr::Const(UcpScalar::Zero) => {}
        _ => factors.push(expr),
    }
}

fn parse_plain_var(expr: &UcpExpr) -> Option<CellId> {
    match expr {
        UcpExpr::Var(cell) => Some(cell.clone()),
        UcpExpr::Neg(inner) => parse_plain_var(inner),
        UcpExpr::Scale(inner, scalar) if scalar.is_statically_non_zero() => parse_plain_var(inner),
        _ => None,
    }
}

fn parse_root_factor(expr: &UcpExpr) -> Option<(CellId, BigInt)> {
    let linear = linearize_symbolic(expr)?;
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

fn linearize_symbolic(expr: &UcpExpr) -> Option<LinearExpr> {
    if let Some(value) = constant_expr_value(expr) {
        return Some(LinearExpr::constant(value));
    }

    match expr {
        UcpExpr::Var(cell) => Some(LinearExpr::term(cell.clone(), BigInt::from(1))),
        UcpExpr::Const(_) => None,
        UcpExpr::Neg(inner) => {
            linearize_symbolic(inner).map(|linear| linear.scale(BigInt::from(-1)))
        }
        UcpExpr::Add(left, right) => {
            Some(linearize_symbolic(left)?.add(linearize_symbolic(right)?))
        }
        UcpExpr::Mul(left, right) => {
            if let Some(value) = constant_expr_value(left) {
                return Some(linearize_symbolic(right)?.scale(value));
            }
            if let Some(value) = constant_expr_value(right) {
                return Some(linearize_symbolic(left)?.scale(value));
            }
            None
        }
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => Some(LinearExpr::constant(BigInt::from(0))),
            UcpScalar::Known(scale) => {
                Some(linearize_symbolic(inner)?.scale(bounded_value(scale.clone())?))
            }
            UcpScalar::NonZero | UcpScalar::Unknown => None,
        },
    }
}

fn constant_expr_value(expr: &UcpExpr) -> Option<BigInt> {
    match expr {
        UcpExpr::Var(_) => None,
        UcpExpr::Const(scalar) => bounded_value(scalar.as_known()?),
        UcpExpr::Neg(inner) => bounded_value(-constant_expr_value(inner)?),
        UcpExpr::Add(left, right) => {
            bounded_value(constant_expr_value(left)? + constant_expr_value(right)?)
        }
        UcpExpr::Mul(left, right) => {
            bounded_value(constant_expr_value(left)? * constant_expr_value(right)?)
        }
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => Some(BigInt::from(0)),
            UcpScalar::Known(scale) => bounded_value(constant_expr_value(inner)? * scale),
            UcpScalar::NonZero | UcpScalar::Unknown => None,
        },
    }
}

fn linearize_zero_equation(expr: &UcpExpr, values: &UcpValueFacts) -> Option<LinearExpr> {
    let factors = meaningful_product_factors(expr);
    if factors.len() == 1 {
        return linearize(factors[0], values);
    }

    linearize(expr, values)
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

fn bounded_value(value: BigInt) -> Option<BigInt> {
    if value == BigInt::from(0)
        || (value >= BigInt::from(i64::MIN) && value <= BigInt::from(i64::MAX))
    {
        Some(value)
    } else {
        None
    }
}

impl LinearExpr {
    fn constant(value: BigInt) -> Self {
        Self {
            constant: value,
            terms: BTreeMap::new(),
        }
    }

    fn term(cell: CellId, coefficient: BigInt) -> Self {
        Self {
            constant: BigInt::from(0),
            terms: BTreeMap::from([(cell, coefficient)]),
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

    fn product(y: &CellId, x: &CellId, root: i64) -> UcpExpr {
        UcpExpr::mul(
            UcpExpr::var(y.clone()),
            UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(-root)),
        )
    }

    #[test]
    fn infers_all_outputs_unique_from_one_hot_pattern() {
        let x = CellId::instance(0, 0);
        let e = CellId::instance(1, 0);
        let y0 = CellId::advice(0, 0);
        let y1 = CellId::advice(1, 0);
        let y2 = CellId::advice(2, 0);
        let expressions = vec![
            product(&y0, &x, 0),
            product(&y1, &x, 1),
            product(&y2, &x, 2),
            UcpExpr::add(
                UcpExpr::add(UcpExpr::var(y0.clone()), UcpExpr::var(y1.clone())),
                UcpExpr::add(
                    UcpExpr::var(y2.clone()),
                    UcpExpr::neg(UcpExpr::var(e.clone())),
                ),
            ),
        ];
        let facts = UcpFacts::from_iter([x.clone(), e.clone()]);
        let values = UcpValueFacts::new();

        let inferences = infer_all_but_one_zero(&expressions, &facts, &values);

        assert_eq!(
            inferences,
            vec![
                AllButOneInference {
                    cell: y0,
                    value: None
                },
                AllButOneInference {
                    cell: y1,
                    value: None
                },
                AllButOneInference {
                    cell: y2,
                    value: None
                },
            ]
        );
    }

    #[test]
    fn carries_exact_values_when_x_and_e_are_known() {
        let x = CellId::instance(0, 0);
        let e = CellId::instance(1, 0);
        let y0 = CellId::advice(0, 0);
        let y1 = CellId::advice(1, 0);
        let y2 = CellId::advice(2, 0);
        let expressions = vec![
            product(&y0, &x, 0),
            product(&y1, &x, 1),
            product(&y2, &x, 2),
            UcpExpr::add(
                UcpExpr::add(UcpExpr::var(y0.clone()), UcpExpr::var(y1.clone())),
                UcpExpr::add(
                    UcpExpr::var(y2.clone()),
                    UcpExpr::neg(UcpExpr::var(e.clone())),
                ),
            ),
        ];
        let facts = UcpFacts::from_iter([x.clone(), e.clone()]);
        let mut values = UcpValueFacts::new();
        values.mark_known(x, BigInt::from(1));
        values.mark_known(e, BigInt::from(1));

        let inferences = infer_all_but_one_zero(&expressions, &facts, &values);

        assert_eq!(
            inferences,
            vec![
                AllButOneInference {
                    cell: y0,
                    value: Some(BigInt::from(0))
                },
                AllButOneInference {
                    cell: y1,
                    value: Some(BigInt::from(1))
                },
                AllButOneInference {
                    cell: y2,
                    value: Some(BigInt::from(0))
                },
            ]
        );
    }

    #[test]
    fn does_not_fire_when_sum_target_is_not_unique() {
        let x = CellId::instance(0, 0);
        let e = CellId::advice(9, 0);
        let y0 = CellId::advice(0, 0);
        let y1 = CellId::advice(1, 0);
        let expressions = vec![
            product(&y0, &x, 0),
            product(&y1, &x, 1),
            UcpExpr::add(
                UcpExpr::var(e),
                UcpExpr::neg(UcpExpr::add(
                    UcpExpr::var(y0.clone()),
                    UcpExpr::var(y1.clone()),
                )),
            ),
        ];
        let facts = UcpFacts::from_iter([x]);
        let values = UcpValueFacts::new();

        assert!(infer_all_but_one_zero(&expressions, &facts, &values).is_empty());
    }

    #[test]
    fn does_not_fire_when_roots_are_duplicated() {
        let x = CellId::instance(0, 0);
        let e = CellId::instance(1, 0);
        let y0 = CellId::advice(0, 0);
        let y1 = CellId::advice(1, 0);
        let expressions = vec![
            product(&y0, &x, 0),
            product(&y1, &x, 0),
            UcpExpr::add(
                UcpExpr::add(UcpExpr::var(y0), UcpExpr::var(y1)),
                UcpExpr::neg(UcpExpr::var(e.clone())),
            ),
        ];
        let facts = UcpFacts::from_iter([x, e]);
        let values = UcpValueFacts::new();

        assert!(infer_all_but_one_zero(&expressions, &facts, &values).is_empty());
    }
}
