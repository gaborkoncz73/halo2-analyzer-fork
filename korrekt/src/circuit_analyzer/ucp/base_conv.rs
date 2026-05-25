// Ez a modul a cikk Base-Conv szabályát valósítja meg.
// A szabály olyan zero equationt keres, ahol egy unique x fel van írva c alapú számként:
//   x = y_0 + c*y_1 + c^2*y_2 + ... + c^n*y_n
// Ha minden digit y_i domainje [0, c-1]-ben van, x unique, és nincs modulo p átfordulás,
// akkor a base representation egyértelmű, ezért minden y_i unique lesz.
use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
    facts::UcpFacts,
    value::UcpValueFacts,
};
use crate::circuit_analyzer::halo2_proofs_libs::bn256;
use num::Num;
use num_bigint::BigInt;
use std::collections::BTreeMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BaseConvInference {
    //Az a digit cella, amiről a szabály kimondta, hogy unique
    pub cell: CellId,
    //Ha x konkrét értéke ismert, akkor a digit konkrét értékét is visszaadjuk
    pub value: Option<BigInt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct BaseConvCandidate {
    //A base-conv alakban szereplő y_i digit cellák, növekvő hatvány szerint
    digits: Vec<CellId>,
    //Ha x ismert, akkor a hozzá tartozó konkrét digitértékek
    digit_values: Option<Vec<BigInt>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearExpr {
    //A változóktól független konstans tag
    constant: BigInt,
    //A lineáris változótagok: cella -> együttható
    terms: BTreeMap<CellId, BigInt>,
}

//Base-Conv futtatása az alapértelmezett mezőmodulussal
pub fn infer_base_conversions(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    values: &UcpValueFacts,
) -> Vec<BaseConvInference> {
    infer_base_conversions_with_modulus(expressions, facts, values, &default_field_modulus())
}

//Base-Conv futtatása explicit p modulussal, hogy a cikk no-wrap feltételét is ellenőrizzük
pub fn infer_base_conversions_with_modulus(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> Vec<BaseConvInference> {
    let mut inferences = BTreeMap::new();

    for expr in expressions {
        //Csak lineáris zero equationökön tudjuk felismerni a base-conv alakot
        let Some(linear) = linearize_zero_equation(expr) else {
            continue;
        };

        for candidate in base_conversion_candidates(linear, facts, values, modulus) {
            for (index, digit) in candidate.digits.into_iter().enumerate() {
                //Ha vannak konkrét digitértékek, az index alapján a megfelelő y_i-hez kötjük őket
                let value = candidate
                    .digit_values
                    .as_ref()
                    .and_then(|values| values.get(index).cloned());
                inferences.entry(digit).or_insert(value);
            }
        }
    }

    //Deterministikus sorrendben adjuk vissza a megtanult digit cellákat
    inferences
        .into_iter()
        .map(|(cell, value)| BaseConvInference { cell, value })
        .collect()
}

fn base_conversion_candidates(
    linear: LinearExpr,
    facts: &UcpFacts,
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> Vec<BaseConvCandidate> {
    let mut candidates = Vec::new();

    //A lineáris egyenletben végigpróbáljuk, melyik cella lehet az x
    for (x, x_coefficient) in &linear.terms {
        //A cikk feltétele: K |= x. Emellett x együtthatója csak +1 vagy -1 lehet.
        if !facts.is_unique(x) || !is_plus_or_minus_one(x_coefficient) {
            continue;
        }

        let Some(candidate) = base_conversion_candidate(&linear, x, x_coefficient, values, modulus)
        else {
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
    modulus: &BigInt,
) -> Option<BaseConvCandidate> {
    //A képen lévő alak tiszta zero equation: nincs külön konstans eltolás
    if linear.constant != BigInt::from(0) {
        return None;
    }

    let mut digits_with_coefficients = Vec::new();

    for (cell, coefficient) in &linear.terms {
        //Az x nem digit, ezért kihagyjuk
        if cell == x {
            continue;
        }

        //Az x előjelétől függően normalizáljuk a digit együtthatókat pozitívra
        let digit_coefficient = -coefficient * x_coefficient;
        if digit_coefficient <= BigInt::from(0) {
            return None;
        }

        digits_with_coefficients.push((cell.clone(), digit_coefficient));
    }

    //Ellenőrzi, hogy az együtthatók pontosan 1, c, c^2, ... alakúak-e
    let (base, digits) = parse_base_powers(digits_with_coefficients)?;
    let max_digit = &base - BigInt::from(1);

    //A cikk Delta feltétele: minden digit domainje legyen [0, c-1]-ben
    if digits
        .iter()
        .any(|digit| !values.domain_is_subset_of_range(digit, &BigInt::from(0), &max_digit))
    {
        return None;
    }

    //A cikk modulus/no-wrap feltétele: y_n < p / c^n - 1
    if !highest_digit_satisfies_modulus_bound(&digits, &base, values, modulus) {
        return None;
    }

    //Ha x konkrét értéke ismert, akkor a base-c felbontás konkrét digitjeit is kiszámoljuk
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
    //Legalább y_0 és y_1 kell, mert ebből tudjuk meghatározni a base-t
    if digits_with_coefficients.len() < 2 {
        return None;
    }

    //Együttható szerint rendezzük, így y_0, y_1, ... sorrendet kapunk
    digits_with_coefficients.sort_by(|left, right| left.1.cmp(&right.1).then(left.0.cmp(&right.0)));

    //Az első együtthatónak 1-nek kell lennie: c^0
    if digits_with_coefficients[0].1 != BigInt::from(1) {
        return None;
    }

    //A második együttható adja a base-t: c^1
    let base = digits_with_coefficients[1].1.clone();
    if base <= BigInt::from(1) {
        return None;
    }

    let mut expected = BigInt::from(1);
    let mut digits = Vec::with_capacity(digits_with_coefficients.len());

    for (digit, coefficient) in digits_with_coefficients {
        //Minden következő együtthatónak pontosan az aktuális c^i-nek kell lennie
        if coefficient != expected {
            return None;
        }

        digits.push(digit);
        expected *= &base;
    }

    Some((base, digits))
}

fn highest_digit_satisfies_modulus_bound(
    digits: &[CellId],
    base: &BigInt,
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> bool {
    //A legfelső digit y_n
    let Some(highest_digit) = digits.last() else {
        return false;
    };
    //Domain nélkül nem tudjuk ellenőrizni a cikk feltételét, ezért nem következtetünk
    let Some(highest_domain) = values.domain(highest_digit) else {
        return false;
    };

    //c^n, ahol n a legfelső digit indexe
    let base_power = pow_bigint(base, digits.len() - 1);
    //A domain legnagyobb lehetséges y_n értéke
    let highest_max = highest_domain.max_value();

    //A cikk feltétele: y_n < p / c^n - 1.
    //Integer domainre biztonságos ekvivalens ellenőrzés: c^n * (max(y_n) + 1) < p.
    let highest_bound_witness = &base_power * (highest_max + BigInt::from(1));
    highest_bound_witness < modulus.clone()
}

fn pow_bigint(base: &BigInt, exponent: usize) -> BigInt {
    //Egyszerű BigInt hatványozás kis exponentekhez
    let mut result = BigInt::from(1);
    for _ in 0..exponent {
        result *= base;
    }
    result
}

fn exact_digits(value: &BigInt, base: &BigInt, digit_count: usize) -> Option<Vec<BigInt>> {
    //Negatív x-et nem bontunk fel base-c digitként
    if value < &BigInt::from(0) {
        return None;
    }

    let mut remaining = value.clone();
    let mut digits = Vec::with_capacity(digit_count);

    for _ in 0..digit_count {
        //Alsó digit: maradék base szerint
        digits.push(&remaining % base);
        //Következő digithez osztunk base-szel
        remaining /= base;
    }

    //Ha maradt még érték, akkor a megadott digit_count nem volt elég x reprezentálására
    if remaining == BigInt::from(0) {
        Some(digits)
    } else {
        None
    }
}

fn is_plus_or_minus_one(value: &BigInt) -> bool {
    //Az x lehet +x vagy -x oldalon is a zero equationben
    value == &BigInt::from(1) || value == &BigInt::from(-1)
}

fn linearize_zero_equation(expr: &UcpExpr) -> Option<LinearExpr> {
    //Ha egy szorzásban csak egy érdemi faktor marad, azt külön lineárisítjuk
    let factors = meaningful_product_factors(expr);
    if factors.len() == 1 {
        return linearize(factors[0]);
    }

    //Egyébként az egész expressiont próbáljuk lineáris alakra hozni
    linearize(expr)
}

fn meaningful_product_factors(expr: &UcpExpr) -> Vec<&UcpExpr> {
    let mut factors = Vec::new();
    collect_meaningful_product_factors(expr, &mut factors);
    factors
}

fn collect_meaningful_product_factors<'a>(expr: &'a UcpExpr, factors: &mut Vec<&'a UcpExpr>) {
    match expr {
        //A szorzásfát kilapítjuk faktorlistává
        UcpExpr::Mul(left, right) => {
            collect_meaningful_product_factors(left, factors);
            collect_meaningful_product_factors(right, factors);
        }
        //A mínusz előjel nem számít a faktorok felismerésénél
        UcpExpr::Neg(inner) => collect_meaningful_product_factors(inner, factors),
        //Nem nulla skálázás mellett ugyanaz marad az érdemi faktor
        UcpExpr::Scale(inner, scalar) if scalar.is_statically_non_zero() => {
            collect_meaningful_product_factors(inner, factors)
        }
        //Nem nulla konstans szorzó nem változtatja meg a zero equation megoldáshalmazát
        UcpExpr::Const(UcpScalar::NonZero | UcpScalar::Known(_)) => {}
        //Nullával szorzott rész nem ad base-conv információt
        UcpExpr::Scale(_, UcpScalar::Zero) | UcpExpr::Const(UcpScalar::Zero) => {}
        //Minden más valódi faktor marad
        _ => factors.push(expr),
    }
}

fn linearize(expr: &UcpExpr) -> Option<LinearExpr> {
    //Ha tiszta konstans, akkor konstans lineáris kifejezés lesz
    if let Some(value) = constant_expr_value(expr) {
        return Some(LinearExpr::constant(value));
    }

    match expr {
        //Egy változó lineárisan 1 * cell
        UcpExpr::Var(cell) => Some(LinearExpr::term(cell.clone(), BigInt::from(1))),
        //Ismeretlen konstansból nem tudunk pontos lineáris alakot képezni
        UcpExpr::Const(_) => None,
        UcpExpr::Neg(inner) => linearize(inner).map(|linear| linear.scale(BigInt::from(-1))),
        //Lineáris expressionök összege is lineáris
        UcpExpr::Add(left, right) => Some(linearize(left)?.add(linearize(right)?)),
        //Szorzás csak akkor marad lineáris, ha az egyik oldal konstans
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
            //Pontos lineáris alakhoz konkrét skála kell
            UcpScalar::NonZero | UcpScalar::Unknown => None,
        },
    }
}

fn constant_expr_value(expr: &UcpExpr) -> Option<BigInt> {
    match expr {
        //Változót tartalmazó expression nem konstans
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
    //Védőkorlát: csak kezelhető méretű integer értékekkel végzünk UCP value inference-t
    if value == BigInt::from(0)
        || (value >= BigInt::from(i64::MIN) && value <= BigInt::from(i64::MAX))
    {
        Some(value)
    } else {
        None
    }
}

fn default_field_modulus() -> BigInt {
    //A projekt jelenlegi alapértelmezett mezőmodulusa, ugyanaz, amit az analyzer SMT része is használ
    let without_prefix = bn256::fr::MODULUS_STR.trim_start_matches("0x");
    BigInt::from_str_radix(without_prefix, 16).expect("bn256 scalar modulus must parse")
}

impl LinearExpr {
    //Konstans lineáris kifejezést hoz létre
    fn constant(value: BigInt) -> Self {
        Self {
            constant: value,
            terms: BTreeMap::new(),
        }
    }

    //Egyetlen változótagból álló lineáris kifejezést hoz létre
    fn term(cell: CellId, coefficient: BigInt) -> Self {
        Self {
            constant: BigInt::from(0),
            terms: BTreeMap::from([(cell, coefficient)]),
        }
    }

    //Két lineáris kifejezést összead, az azonos cellák együtthatóit összevonva
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

    //Az egész lineáris kifejezést megszorozza egy konstanssal
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

    //Boolean digit domain: {0, 1}, vagyis base=2 esetén [0, c-1]
    fn boolean_domain() -> UcpValueDomain {
        UcpValueDomain::finite_set([BigInt::from(0), BigInt::from(1)]).unwrap()
    }

    //Több bit cellára beállítja a boolean domaint
    fn mark_bits(values: &mut UcpValueFacts, bits: &[CellId]) {
        for bit in bits {
            values.mark_domain(bit.clone(), boolean_domain());
        }
    }

    //Ellenőrzi, hogy ismert x esetén a konkrét binary digitértékeket is megtanuljuk
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

    //Ellenőrzi, hogy x konkrét értéke nélkül is unique-k lesznek a digit cellák
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

    //Ellenőrzi, hogy digit domain nélkül nem alkalmazzuk a Base-Conv szabályt
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

    //Ellenőrzi, hogy nem 1,c,c^2 alakú együtthatókra nem következtetünk
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

    //Ellenőrzi, hogy ha a legfelső digit modulo p átfordulást engedhet, akkor nem következtetünk
    #[test]
    fn does_not_fire_when_highest_digit_can_wrap_modulus() {
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
        mark_bits(&mut values, &[b0, b1]);

        assert!(
            infer_base_conversions_with_modulus(&[expr], &facts, &values, &BigInt::from(4))
                .is_empty()
        );
    }
}
