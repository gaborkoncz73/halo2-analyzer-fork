//! A részkifejezésenként egyszer számoló kiértékelőt a korábbi, közvetlen rekurzióval veti össze.
//! A referencia szándékosan a régi algoritmus: véletlen kifejezéseken azonos eredményt kell adnia.

use super::*;

fn legacy_kind(expr: &UcpExpr, values: &UcpValueFacts, modulus: Option<&BigInt>) -> ValueKind {
    if modulus.is_some_and(|modulus| modulus <= &BigInt::from(1)) {
        return ValueKind::Unknown;
    }
    if let Some(domain) = legacy_domain(expr, values, modulus) {
        domain.value_kind()
    } else {
        match expr {
            UcpExpr::Const(UcpScalar::Zero) => ValueKind::Zero,
            UcpExpr::Const(UcpScalar::NonZero) => ValueKind::NonZero,
            UcpExpr::Const(UcpScalar::Known(value)) => match modulus {
                Some(modulus) if value % modulus == BigInt::from(0) => ValueKind::Zero,
                Some(_) => ValueKind::NonZero,
                None => ValueKind::Unknown,
            },
            UcpExpr::Scale(inner, scalar) => {
                let inner_kind = legacy_kind(inner, values, modulus);
                if scalar.is_zero()
                    || matches!(scalar, UcpScalar::Known(value)
                        if modulus.is_some_and(|modulus| value % modulus == BigInt::from(0)))
                    || inner_kind == ValueKind::Zero
                {
                    ValueKind::Zero
                } else if scalar.is_non_zero_with_modulus(modulus) {
                    inner_kind
                } else {
                    ValueKind::Unknown
                }
            }
            UcpExpr::Neg(inner) => legacy_kind(inner, values, modulus),
            UcpExpr::Mul(left, right) => match (
                legacy_kind(left, values, modulus),
                legacy_kind(right, values, modulus),
            ) {
                (ValueKind::Zero, _) | (_, ValueKind::Zero) => ValueKind::Zero,
                (ValueKind::NonZero, ValueKind::NonZero) => ValueKind::NonZero,
                _ => ValueKind::Unknown,
            },
            _ => ValueKind::Unknown,
        }
    }
}

fn legacy_domain(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    modulus: Option<&BigInt>,
) -> Option<UcpValueDomain> {
    match expr {
        UcpExpr::Var(cell) => {
            let domain = values.domain(cell)?;
            match modulus {
                Some(_) => finite_domain_from_values(domain_values(domain), modulus),
                None => Some(domain.clone()),
            }
        }
        UcpExpr::Const(scalar) => finite_domain_from_values([scalar.as_known()?], modulus),
        UcpExpr::Neg(inner) => {
            let inner = legacy_domain(inner, values, modulus)?;
            map_domain_values(&inner, modulus, |value| -value)
        }
        UcpExpr::Add(left, right) => {
            let left = legacy_domain(left, values, modulus)?;
            let right = legacy_domain(right, values, modulus)?;
            combine_domain_values(&left, &right, modulus, |left, right| left + right)
        }
        UcpExpr::Mul(left, right) => {
            if legacy_kind(left, values, None) == ValueKind::Zero
                || legacy_kind(right, values, None) == ValueKind::Zero
            {
                return Some(UcpValueDomain::exact(BigInt::from(0)));
            }
            let left = legacy_domain(left, values, modulus)?;
            let right = legacy_domain(right, values, modulus)?;
            combine_domain_values(&left, &right, modulus, |left, right| left * right)
        }
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => Some(UcpValueDomain::exact(BigInt::from(0))),
            UcpScalar::Known(scale) => {
                let inner = legacy_domain(inner, values, modulus)?;
                map_domain_values(&inner, modulus, |value| value * scale)
            }
            UcpScalar::NonZero | UcpScalar::Unknown => {
                if legacy_kind(inner, values, None) == ValueKind::Zero {
                    Some(UcpValueDomain::exact(BigInt::from(0)))
                } else {
                    None
                }
            }
        },
    }
}

struct Random(u64);

impl Random {
    fn next(&mut self, bound: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % bound
    }
}

fn scalar(random: &mut Random) -> UcpScalar {
    match random.next(7) {
        0 => UcpScalar::Zero,
        1 => UcpScalar::NonZero,
        2 => UcpScalar::Unknown,
        3 => UcpScalar::Known(BigInt::from(0)),
        4 => UcpScalar::Known(BigInt::from(7)),
        5 => UcpScalar::Known(BigInt::from(-3)),
        _ => UcpScalar::Known(BigInt::from(random.next(20))),
    }
}

fn expression(random: &mut Random, depth: u32) -> UcpExpr {
    if depth == 0 || random.next(5) == 0 {
        return if random.next(2) == 0 {
            UcpExpr::Var(CellId::advice(random.next(5) as usize, 0))
        } else {
            UcpExpr::Const(scalar(random))
        };
    }
    match random.next(4) {
        0 => UcpExpr::Neg(Box::new(expression(random, depth - 1))),
        1 => UcpExpr::Add(
            Box::new(expression(random, depth - 1)),
            Box::new(expression(random, depth - 1)),
        ),
        2 => UcpExpr::Mul(
            Box::new(expression(random, depth - 1)),
            Box::new(expression(random, depth - 1)),
        ),
        _ => UcpExpr::Scale(Box::new(expression(random, depth - 1)), scalar(random)),
    }
}

// A 0..3 cellákhoz különböző alakú domaint ad, a 4. cella ismeretlen marad.
fn knowledge() -> UcpValueFacts {
    let mut values = UcpValueFacts::new();
    values.mark_domain(CellId::advice(0, 0), UcpValueDomain::exact(BigInt::from(0)));
    values.mark_domain(CellId::advice(1, 0), UcpValueDomain::exact(BigInt::from(5)));
    values.mark_domain(
        CellId::advice(2, 0),
        UcpValueDomain::finite_set([0, 1, 2, 7].map(BigInt::from)).unwrap(),
    );
    values.mark_domain(
        CellId::advice(3, 0),
        UcpValueDomain::finite_set([-1, 3, 16].map(BigInt::from)).unwrap(),
    );
    values
}

#[test]
fn single_pass_evaluation_matches_the_recursive_reference() {
    let values = knowledge();
    let moduli = [
        None,
        Some(BigInt::from(1)),
        Some(BigInt::from(2)),
        Some(BigInt::from(7)),
        Some(BigInt::from(17)),
        Some(BigInt::from(101)),
    ];
    let mut random = Random(0x9E37_79B9_7F4A_7C15);
    for _ in 0..20_000 {
        let expr = expression(&mut random, 6);
        for modulus in &moduli {
            assert_eq!(
                expression_domain_with_optional_modulus(&expr, &values, modulus.as_ref()),
                legacy_domain(&expr, &values, modulus.as_ref()),
                "domain mismatch for {expr:?} under {modulus:?}"
            );
            assert_eq!(
                value_kind_with_optional_modulus(&expr, &values, modulus.as_ref()),
                legacy_kind(&expr, &values, modulus.as_ref()),
                "kind mismatch for {expr:?} under {modulus:?}"
            );
        }
    }
}

// A régi kiértékelő itt legalább 2^60 részszámítást végezne, ezért a teszt a lefutással is bizonyít.
#[test]
fn deep_product_evaluation_is_not_exponential() {
    let cell = CellId::advice(0, 0);
    let mut values = UcpValueFacts::new();
    values.mark_domain(
        cell.clone(),
        UcpValueDomain::finite_set([0, 1, 2].map(BigInt::from)).unwrap(),
    );
    let modulus = BigInt::from(101);
    let mut expr = UcpExpr::Var(cell.clone());
    for root in 1..=60 {
        expr = UcpExpr::Mul(
            Box::new(expr),
            Box::new(UcpExpr::Add(
                Box::new(UcpExpr::Const(UcpScalar::known_i64(root))),
                Box::new(UcpExpr::Neg(Box::new(UcpExpr::Var(cell.clone())))),
            )),
        );
    }
    // A meretkorlat miatt a None is helyes eredmeny; itt a kiertekeles lefutasa a vizsgalt tulajdonsag.
    let _ = expression_domain_with_modulus(&expr, &values, &modulus);
    let _ = value_kind_with_optional_modulus(&expr, &values, Some(&modulus));
}
