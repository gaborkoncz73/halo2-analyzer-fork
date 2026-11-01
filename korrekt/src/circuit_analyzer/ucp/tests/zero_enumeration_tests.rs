//! A korlatos felsorolast es a nagy tablak szureset kimerito modellkereseshez hasonlitja.
//! Minden kis testbeli megoldasnak a kovetkeztetett domainekben kell maradnia.

use super::*;
use crate::circuit_analyzer::ucp::base_conv::{base_equations, infer_table_digits};
use std::collections::BTreeMap;

struct Random(u64);

impl Random {
    fn next(&mut self, bound: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % bound
    }
}

const CELLS: usize = 3;

fn cell(index: usize) -> CellId {
    CellId::advice(index, 0)
}

fn random_expression(random: &mut Random, depth: u32) -> UcpExpr {
    if depth == 0 || random.next(4) == 0 {
        return if random.next(3) > 0 {
            UcpExpr::Var(cell(random.next(CELLS as u64) as usize))
        } else {
            UcpExpr::Const(UcpScalar::known_i64(random.next(9) as i64 - 4))
        };
    }
    match random.next(4) {
        0 => UcpExpr::Neg(Box::new(random_expression(random, depth - 1))),
        1 => UcpExpr::Add(
            Box::new(random_expression(random, depth - 1)),
            Box::new(random_expression(random, depth - 1)),
        ),
        2 => UcpExpr::Mul(
            Box::new(random_expression(random, depth - 1)),
            Box::new(random_expression(random, depth - 1)),
        ),
        _ => UcpExpr::Scale(
            Box::new(random_expression(random, depth - 1)),
            UcpScalar::known_i64(random.next(7) as i64 - 3),
        ),
    }
}

fn evaluate(expr: &UcpExpr, assignment: &[i64; CELLS], modulus: i64) -> i64 {
    let value = match expr {
        UcpExpr::Var(target) => assignment[target.column],
        UcpExpr::Const(scalar) => i64::try_from(scalar.as_known().unwrap()).unwrap(),
        UcpExpr::Neg(inner) => -evaluate(inner, assignment, modulus),
        UcpExpr::Add(left, right) => {
            evaluate(left, assignment, modulus) + evaluate(right, assignment, modulus)
        }
        UcpExpr::Mul(left, right) => {
            evaluate(left, assignment, modulus) * evaluate(right, assignment, modulus)
        }
        UcpExpr::Scale(inner, scalar) => {
            evaluate(inner, assignment, modulus)
                * i64::try_from(scalar.as_known().unwrap()).unwrap()
        }
    };
    value.rem_euclid(modulus)
}

// Veletlen domaineket ad, de a teszt csak a domainekkel osszhangban levo megoldasokat kovetelheti meg.
fn random_values(random: &mut Random, modulus: i64) -> (UcpValueFacts, BTreeMap<usize, Vec<i64>>) {
    let mut values = UcpValueFacts::new();
    let mut allowed = BTreeMap::new();
    for index in 0..CELLS {
        if random.next(5) == 0 {
            continue;
        }
        let members: Vec<i64> = (0..modulus).filter(|_| random.next(2) == 0).collect();
        let domain = finite_domain_from_values(
            members.iter().map(|value| BigInt::from(*value)),
            Some(&BigInt::from(modulus)),
        );
        if let Some(domain) = domain {
            values.mark_domain(cell(index), domain);
            allowed.insert(index, members);
        }
    }
    (values, allowed)
}

#[test]
fn zero_equation_enumeration_keeps_every_solution_in_small_fields() {
    let mut random = Random(0xD1B5_4A32_D192_ED03);
    let mut narrowed = 0;
    for modulus in [2i64, 3, 5, 7, 11] {
        let field = BigInt::from(modulus);
        for _ in 0..4_000 {
            let expr = random_expression(&mut random, 4);
            let (values, allowed) = random_values(&mut random, modulus);
            let inferred =
                infer_value_domains_from_zero_equation_with_modulus(&expr, &values, &field);
            narrowed += usize::from(!inferred.is_empty());
            for a in 0..modulus {
                for b in 0..modulus {
                    for c in 0..modulus {
                        let assignment = [a, b, c];
                        let in_domains = allowed
                            .iter()
                            .all(|(index, members)| members.contains(&assignment[*index]));
                        if !in_domains || evaluate(&expr, &assignment, modulus) != 0 {
                            continue;
                        }
                        for (target, domain) in &inferred {
                            let value = normalize_field_value(
                                BigInt::from(assignment[target.column]),
                                &field,
                            )
                            .unwrap();
                            assert!(
                                domain_values(domain).contains(&value),
                                "{expr:?} excludes solution {assignment:?} via {target} {domain:?} mod {modulus}"
                            );
                        }
                    }
                }
            }
        }
    }
    assert!(
        narrowed > 1_000,
        "A veletlen minta nem vizsgalta a szabalyt"
    );
}

#[test]
fn enumeration_learns_nonzero_factors_and_excludes_their_roots() {
    let modulus = BigInt::from(101);
    let (x, inverse, delta) = (cell(0), cell(1), cell(2));
    let mut values = UcpValueFacts::new();
    values.mark_domain(
        x.clone(),
        UcpValueDomain::finite_set([1, 2, 3, 4].map(BigInt::from)).unwrap(),
    );
    // delta = (x-2)*(x-3)
    let factor = |root: i64| {
        Box::new(UcpExpr::Add(
            Box::new(UcpExpr::Var(x.clone())),
            Box::new(UcpExpr::Const(UcpScalar::known_i64(-root))),
        ))
    };
    let product = UcpExpr::Add(
        Box::new(UcpExpr::Mul(factor(2), factor(3))),
        Box::new(UcpExpr::Neg(Box::new(UcpExpr::Var(delta.clone())))),
    );
    for (cell, domain) in
        infer_value_domains_from_zero_equation_with_modulus(&product, &values, &modulus)
    {
        values.mark_domain(cell, domain);
    }
    // 1 - delta*inverse = 0, tehat delta nem lehet nulla.
    let nonzero = UcpExpr::Add(
        Box::new(UcpExpr::Const(UcpScalar::known_i64(1))),
        Box::new(UcpExpr::Neg(Box::new(UcpExpr::Mul(
            Box::new(UcpExpr::Var(delta.clone())),
            Box::new(UcpExpr::Var(inverse)),
        )))),
    );
    for (cell, domain) in
        infer_value_domains_from_zero_equation_with_modulus(&nonzero, &values, &modulus)
    {
        values.mark_domain(cell, domain);
    }
    for (cell, domain) in
        infer_value_domains_from_zero_equation_with_modulus(&product, &values, &modulus)
    {
        values.mark_domain(cell, domain);
    }
    assert_eq!(
        values.domain(&x),
        UcpValueDomain::finite_set([1, 4].map(BigInt::from)).as_ref()
    );
}

fn packed_equation(packed: &CellId, digits: &[CellId], base: i64) -> UcpExpr {
    let mut sum = UcpExpr::Neg(Box::new(UcpExpr::Var(packed.clone())));
    let mut weight = 1;
    for digit in digits {
        sum = UcpExpr::Add(
            Box::new(sum),
            Box::new(UcpExpr::Scale(
                Box::new(UcpExpr::Var(digit.clone())),
                UcpScalar::known_i64(weight),
            )),
        );
        weight *= base;
    }
    sum
}

#[test]
fn large_table_filter_projects_only_rows_compatible_with_digit_domains() {
    let modulus = BigInt::from(1_000_003);
    let (packed, low, high) = (cell(0), cell(1), cell(2));
    let mut values = UcpValueFacts::new();
    let digits = UcpValueDomain::finite_set((0..10).map(BigInt::from)).unwrap();
    values.mark_domain(low.clone(), digits.clone());
    values.mark_domain(
        high.clone(),
        UcpValueDomain::finite_set([1, 5, 9].map(BigInt::from)).unwrap(),
    );
    let table: Vec<_> = [12, 57, 99, 7, 23].map(BigInt::from).to_vec();
    let equations = base_equations(
        &[packed_equation(&packed, &[low.clone(), high.clone()], 10)],
        &modulus,
    );
    let inferred = infer_table_digits(
        &UcpExpr::Var(packed.clone()),
        &table,
        &equations,
        &values,
        &modulus,
    );
    let domain_of = |target: &CellId| {
        inferred
            .iter()
            .find(|(cell, _)| cell == target)
            .map(|(_, domain)| domain.clone())
    };
    // Csak a 12, 57 es 99 sor osszeegyeztetheto a magasabb helyiertek domainjevel.
    assert_eq!(
        domain_of(&low),
        UcpValueDomain::finite_set([2, 7, 9].map(BigInt::from))
    );
    assert_eq!(
        domain_of(&high),
        UcpValueDomain::finite_set([1, 5, 9].map(BigInt::from))
    );
    assert_eq!(
        domain_of(&packed),
        UcpValueDomain::finite_set([12, 57, 99].map(BigInt::from))
    );
}

#[test]
fn large_table_filter_requires_a_verified_digit_decomposition() {
    let modulus = BigInt::from(1_000_003);
    let (packed, low, high) = (cell(0), cell(1), cell(2));
    let table = vec![BigInt::from(12)];
    // Szamjegydomain nelkul a felbontas nem bizonyitott, ezert nem kovetkeztet.
    let values = UcpValueFacts::new();
    let equations = base_equations(
        &[packed_equation(&packed, &[low.clone(), high.clone()], 10)],
        &modulus,
    );
    assert!(infer_table_digits(
        &UcpExpr::Var(packed.clone()),
        &table,
        &equations,
        &values,
        &modulus
    )
    .is_empty());
    // A korbefordulast megengedo modulusnal sem kovetkeztet.
    let small = BigInt::from(13);
    let mut values = UcpValueFacts::new();
    let digits = UcpValueDomain::finite_set((0..10).map(BigInt::from)).unwrap();
    values.mark_domain(low.clone(), digits.clone());
    values.mark_domain(high.clone(), digits);
    let equations = base_equations(&[packed_equation(&packed, &[low, high], 10)], &small);
    assert!(
        infer_table_digits(&UcpExpr::Var(packed), &table, &equations, &values, &small).is_empty()
    );
}

// A gyorsitotar kulcsanak a domaint, a teljessegi jelolest es a modulust is tartalmaznia kell.
#[test]
fn cached_answers_depend_on_every_input_of_the_enumeration() {
    let x = cell(0);
    let expr = UcpExpr::mul(
        UcpExpr::var(x.clone()),
        UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(-1)),
    );
    let domain = |entries: &[i64]| {
        let mut values = UcpValueFacts::new();
        values.mark_domain(
            x.clone(),
            UcpValueDomain::finite_set(entries.iter().map(|v| BigInt::from(*v))).unwrap(),
        );
        values
    };
    let narrowed = UcpValueDomain::finite_set([0, 1].map(BigInt::from)).unwrap();
    let wide = domain(&[0, 1, 2]);
    let first = zero_enumeration::infer(&expr, &wide, &BigInt::from(5));
    assert_eq!(first, vec![(x.clone(), narrowed.clone())]);
    assert_eq!(zero_enumeration::infer(&expr, &wide, &BigInt::from(5)), first);
    // A 4 a 3 modulus szerint gyok, az 5 szerint nem: ugyanaz a bemenet mas valaszt ad.
    let spread = domain(&[0, 2, 4]);
    assert_ne!(
        zero_enumeration::infer(&expr, &spread, &BigInt::from(3)),
        zero_enumeration::infer(&expr, &spread, &BigInt::from(5))
    );
    assert_eq!(
        zero_enumeration::infer(&expr, &domain(&[0, 1, 3]), &BigInt::from(5)),
        vec![(x.clone(), narrowed)]
    );
    let mut complete = wide.clone();
    complete
        .mark_complete_from_samples(&x, &[0, 1, 2].map(BigInt::from).into(), &BigInt::from(5))
        .unwrap();
    assert!(zero_enumeration::infer(&expr, &complete, &BigInt::from(5)).is_empty());
}
