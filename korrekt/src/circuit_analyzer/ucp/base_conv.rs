use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
    facts::UcpFacts,
    value::UcpValueFacts,
};
use num_bigint::BigInt;
use std::collections::BTreeMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BaseConvInference {
    pub cell: CellId,
    pub value: Option<BigInt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct BaseConvCandidate {
    digits: Vec<CellId>,
    digit_values: Option<Vec<BigInt>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearExpr {
    constant: BigInt,
    terms: BTreeMap<CellId, BigInt>,
}

/// Implements the paper's Base-Conv uniqueness rule.
///
/// Shape recognized:
/// `x = y_0 + c*y_1 + c^2*y_2 + ...`
///
/// Requirements:
/// - `x` is already unique in `K`;
/// - every `y_i` has `Delta(y_i) subset [0, c - 1]`;
/// - coefficients are exactly `1, c, c^2, ...` for a base `c > 1`.
pub fn infer_base_conversions(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    values: &UcpValueFacts,
) -> Vec<BaseConvInference> {
    let mut inferences = BTreeMap::new();

    for expr in expressions {
        let Some(linear) = linearize_zero_equation(expr) else {
            continue;
        };

        for candidate in base_conversion_candidates(linear, facts, values) {
            for (index, digit) in candidate.digits.into_iter().enumerate() {
                let value = candidate
                    .digit_values
                    .as_ref()
                    .and_then(|values| values.get(index).cloned());
                inferences.entry(digit).or_insert(value);
            }
        }
    }

    inferences
        .into_iter()
        .map(|(cell, value)| BaseConvInference { cell, value })
        .collect()
}

fn base_conversion_candidates(
    linear: LinearExpr,
    facts: &UcpFacts,
    values: &UcpValueFacts,
) -> Vec<BaseConvCandidate> {
    let mut candidates = Vec::new();

    for (x, x_coefficient) in &linear.terms {
        if !facts.is_unique(x) || !is_plus_or_minus_one(x_coefficient) {
            continue;
        }

        let Some(candidate) = base_conversion_candidate(&linear, x, x_coefficient, values) else {
            continue;
        };
        candidates.push(candidate);
    }

    candidates
}

fn base_conversion_candidate(
    linear: &LinearExpr,
    x: &CellId,
    x_coefficient: &BigInt,
    values: &UcpValueFacts,
) -> Option<BaseConvCandidate> {
    if linear.constant != BigInt::from(0) {
        return None;
    }

    let mut digits_with_coefficients = Vec::new();

    for (cell, coefficient) in &linear.terms {
        if cell == x {
            continue;
        }

        let digit_coefficient = -coefficient * x_coefficient;
        if digit_coefficient <= BigInt::from(0) {
            return None;
        }

        digits_with_coefficients.push((cell.clone(), digit_coefficient));
    }

    let (base, digits) = parse_base_powers(digits_with_coefficients)?;
    let max_digit = &base - BigInt::from(1);

    if digits
        .iter()
        .any(|digit| !values.domain_is_subset_of_range(digit, &BigInt::from(0), &max_digit))
    {
        return None;
    }

    let digit_values = match values.known_value(x) {
        Some(x_value) => Some(exact_digits(x_value, &base, digits.len())?),
        None => None,
    };

    Some(BaseConvCandidate {
        digits,
        digit_values,
    })
}

fn parse_base_powers(
    mut digits_with_coefficients: Vec<(CellId, BigInt)>,
) -> Option<(BigInt, Vec<CellId>)> {
    if digits_with_coefficients.len() < 2 {
        return None;
    }

    digits_with_coefficients.sort_by(|left, right| left.1.cmp(&right.1).then(left.0.cmp(&right.0)));

    if digits_with_coefficients[0].1 != BigInt::from(1) {
        return None;
    }

    let base = digits_with_coefficients[1].1.clone();
    if base <= BigInt::from(1) {
        return None;
    }

    let mut expected = BigInt::from(1);
    let mut digits = Vec::with_capacity(digits_with_coefficients.len());

    for (digit, coefficient) in digits_with_coefficients {
        if coefficient != expected {
            return None;
        }

        digits.push(digit);
        expected *= &base;
    }

    Some((base, digits))
}

fn exact_digits(value: &BigInt, base: &BigInt, digit_count: usize) -> Option<Vec<BigInt>> {
    if value < &BigInt::from(0) {
        return None;
    }

    let mut remaining = value.clone();
    let mut digits = Vec::with_capacity(digit_count);

    for _ in 0..digit_count {
        digits.push(&remaining % base);
        remaining /= base;
    }

    if remaining == BigInt::from(0) {
        Some(digits)
    } else {
        None
    }
}

fn is_plus_or_minus_one(value: &BigInt) -> bool {
    value == &BigInt::from(1) || value == &BigInt::from(-1)
}

fn linearize_zero_equation(expr: &UcpExpr) -> Option<LinearExpr> {
    let factors = meaningful_product_factors(expr);
    if factors.len() == 1 {
        return linearize(factors[0]);
    }

    linearize(expr)
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

fn linearize(expr: &UcpExpr) -> Option<LinearExpr> {
    if let Some(value) = constant_expr_value(expr) {
        return Some(LinearExpr::constant(value));
    }

    match expr {
        UcpExpr::Var(cell) => Some(LinearExpr::term(cell.clone(), BigInt::from(1))),
        UcpExpr::Const(_) => None,
        UcpExpr::Neg(inner) => linearize(inner).map(|linear| linear.scale(BigInt::from(-1))),
        UcpExpr::Add(left, right) => Some(linearize(left)?.add(linearize(right)?)),
        UcpExpr::Mul(left, right) => {
            if let Some(value) = constant_expr_value(left) {
                return Some(linearize(right)?.scale(value));
            }
            if let Some(value) = constant_expr_value(right) {
                return Some(linearize(left)?.scale(value));
            }
            None
        }
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => Some(LinearExpr::constant(BigInt::from(0))),
            UcpScalar::Known(scale) => Some(linearize(inner)?.scale(bounded_value(scale.clone())?)),
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
    use crate::circuit_analyzer::ucp::value::UcpValueDomain;

    fn boolean_domain() -> UcpValueDomain {
        UcpValueDomain::finite_set([BigInt::from(0), BigInt::from(1)]).unwrap()
    }

    fn mark_bits(values: &mut UcpValueFacts, bits: &[CellId]) {
        for bit in bits {
            values.mark_domain(bit.clone(), boolean_domain());
        }
    }

    #[test]
    fn infers_binary_decomposition_digits_from_exact_x() {
        let x = CellId::instance(0, 0);
        let b0 = CellId::advice(0, 0);
        let b1 = CellId::advice(1, 0);
        let b2 = CellId::advice(2, 0);
        let expr = UcpExpr::add(
            UcpExpr::add(
                UcpExpr::var(b0.clone()),
                UcpExpr::scale_by(UcpExpr::var(b1.clone()), UcpScalar::known_i64(2)),
            ),
            UcpExpr::add(
                UcpExpr::scale_by(UcpExpr::var(b2.clone()), UcpScalar::known_i64(4)),
                UcpExpr::neg(UcpExpr::var(x.clone())),
            ),
        );
        let facts = UcpFacts::from_iter([x.clone()]);
        let mut values = UcpValueFacts::new();
        values.mark_known(x, BigInt::from(5));
        mark_bits(&mut values, &[b0.clone(), b1.clone(), b2.clone()]);

        let inferences = infer_base_conversions(&[expr], &facts, &values);

        assert_eq!(
            inferences,
            vec![
                BaseConvInference {
                    cell: b0,
                    value: Some(BigInt::from(1))
                },
                BaseConvInference {
                    cell: b1,
                    value: Some(BigInt::from(0))
                },
                BaseConvInference {
                    cell: b2,
                    value: Some(BigInt::from(1))
                },
            ]
        );
    }

    #[test]
    fn infers_uniqueness_without_exact_x_value() {
        let x = CellId::instance(0, 0);
        let b0 = CellId::advice(0, 0);
        let b1 = CellId::advice(1, 0);
        let expr = UcpExpr::add(
            UcpExpr::add(
                UcpExpr::var(b0.clone()),
                UcpExpr::scale_by(UcpExpr::var(b1.clone()), UcpScalar::known_i64(2)),
            ),
            UcpExpr::neg(UcpExpr::var(x.clone())),
        );
        let facts = UcpFacts::from_iter([x]);
        let mut values = UcpValueFacts::new();
        mark_bits(&mut values, &[b0.clone(), b1.clone()]);

        let inferences = infer_base_conversions(&[expr], &facts, &values);

        assert_eq!(
            inferences,
            vec![
                BaseConvInference {
                    cell: b0,
                    value: None
                },
                BaseConvInference {
                    cell: b1,
                    value: None
                },
            ]
        );
    }

    #[test]
    fn does_not_fire_without_digit_domains() {
        let x = CellId::instance(0, 0);
        let b0 = CellId::advice(0, 0);
        let b1 = CellId::advice(1, 0);
        let expr = UcpExpr::add(
            UcpExpr::add(
                UcpExpr::var(b0),
                UcpExpr::scale_by(UcpExpr::var(b1), UcpScalar::known_i64(2)),
            ),
            UcpExpr::neg(UcpExpr::var(x.clone())),
        );
        let facts = UcpFacts::from_iter([x]);
        let values = UcpValueFacts::new();

        assert!(infer_base_conversions(&[expr], &facts, &values).is_empty());
    }

    #[test]
    fn does_not_fire_for_non_power_coefficients() {
        let x = CellId::instance(0, 0);
        let b0 = CellId::advice(0, 0);
        let b1 = CellId::advice(1, 0);
        let b2 = CellId::advice(2, 0);
        let expr = UcpExpr::add(
            UcpExpr::add(
                UcpExpr::var(b0.clone()),
                UcpExpr::scale_by(UcpExpr::var(b1.clone()), UcpScalar::known_i64(2)),
            ),
            UcpExpr::add(
                UcpExpr::scale_by(UcpExpr::var(b2.clone()), UcpScalar::known_i64(5)),
                UcpExpr::neg(UcpExpr::var(x.clone())),
            ),
        );
        let facts = UcpFacts::from_iter([x]);
        let mut values = UcpValueFacts::new();
        mark_bits(&mut values, &[b0, b1, b2]);

        assert!(infer_base_conversions(&[expr], &facts, &values).is_empty());
    }
}
