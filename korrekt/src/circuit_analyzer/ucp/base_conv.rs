// Ez a modul a QED² cikk Base-Conv szabályát valósítja meg.
// A szabály olyan nullával egyenlő kifejezést keres, amely egy egyértelmű x értéket c alapú számként ír fel:
//   x = y_0 + c*y_1 + c^2*y_2 + ... + c^n*y_n
// Ha minden y_i számjegy domainje [0,c-1]-ben van, x egyértelmű, és kizárható a moduláris körbefordulás,
// akkor igazolja a számjegyek egyértelműségét.
use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
    facts::UcpFacts,
    value::{bounded_value, UcpValueFacts},
};
use num_bigint::BigInt;
use std::collections::BTreeMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BaseConvInference {
    // Az a számjegycella, amelynek egyértelműségét a szabály igazolja.
    pub cell: CellId,
    // Ismert x esetén a számjegy konkrét értékét is visszaadja.
    pub value: Option<BigInt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct BaseConvCandidate {
    base: BigInt,
    // A felbontás y_i számjegycelláit növekvő helyiérték szerint tárolja.
    digits: Vec<CellId>,
    // Ismert x esetén a kiszámított számjegyértékeket tárolja.
    digit_values: Option<Vec<BigInt>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearExpr {
    //A változóktól független konstans tag
    constant: BigInt,
    //A lineáris változótagok: cella -> együttható
    terms: BTreeMap<CellId, BigInt>,
}

// A Base-Conv szabályt explicit p modulussal futtatja, és ellenőrzi a körbefordulás kizárását.
pub fn infer_base_conversions_with_modulus(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> Vec<BaseConvInference> {
    if modulus <= &BigInt::from(1) {
        return Vec::new();
    }
    let mut inferences = BTreeMap::new();

    for expr in expressions {
        // A számjegyes alakot csak lineáris, nullával egyenlő kifejezésekben ismeri fel.
        let Some(linear) = linearize_zero_equation(expr, modulus) else {
            continue;
        };

        for candidate in base_conversion_candidates(linear, facts, values, modulus) {
            for (index, digit) in candidate.digits.into_iter().enumerate() {
                // A kiszámított számjegyértékeket az indexük alapján a megfelelő y_i cellához rendeli.
                let value = candidate
                    .digit_values
                    .as_ref()
                    .and_then(|values| values.get(index).cloned());
                inferences.entry(digit).or_insert(value);
            }
        }
    }

    // Determinisztikus sorrendben adja vissza az igazolt számjegycellákat.
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

    //A lineáris egyenletben végigpróbálja, melyik cella lehet az x
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
    // A szabályhoz külön konstans eltolás nélküli, nullával egyenlő alakot követel meg.
    if linear.constant != BigInt::from(0) {
        return None;
    }

    let mut digits_with_coefficients = Vec::new();

    for (cell, coefficient) in &linear.terms {
        // Az x cellát kihagyja a számjegyek közül.
        if cell == x {
            continue;
        }

        // Az x előjele alapján pozitívra normalizálja a számjegyek együtthatóit.
        let digit_coefficient = -coefficient * x_coefficient;
        if digit_coefficient <= BigInt::from(0) {
            return None;
        }

        digits_with_coefficients.push((cell.clone(), digit_coefficient));
    }

    //Ellenőrzi, hogy az együtthatók pontosan 1, c, c^2, ... alakúak-e
    let (base, digits) = parse_base_powers(digits_with_coefficients)?;
    let max_digit = &base - BigInt::from(1);

    // Minden számjegy domainjét a [0,c-1] tartományba esőnek követeli meg.
    if digits
        .iter()
        .any(|digit| !values.domain_is_subset_of_range(digit, &BigInt::from(0), &max_digit))
    {
        return None;
    }

    // Ellenőrzi a körbefordulást kizáró y_n < p / c^n - 1 feltételt.
    if !highest_digit_satisfies_modulus_bound(&digits, &base, values, modulus) {
        return None;
    }

    // Ismert x esetén kiszámítja a c alapú felbontás konkrét számjegyeit.
    let digit_values = match values.known_value(x) {
        Some(x_value) => Some(exact_digits(x_value, &base, digits.len())?),
        None => None,
    };

    Some(BaseConvCandidate {
        base,
        digits,
        digit_values,
    })
}

pub(crate) struct FiniteBaseCandidate {
    pub packed: CellId,
    pub branches: Vec<(BigInt, Option<Vec<(CellId, BigInt)>>)>,
}

/// A csomagolt érték véges jelölthalmazának elemeit számjegyekre bontja,
/// ha a számjegykorlátok teljesülnek, és kizárható a moduláris körbefordulás.
pub(crate) fn finite_base_candidates(
    expressions: &[UcpExpr],
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> Vec<FiniteBaseCandidate> {
    if modulus <= &BigInt::from(1) {
        return Vec::new();
    }
    let mut candidates = BTreeMap::new();
    for expr in expressions {
        let Some(linear) = linearize_zero_equation(expr, modulus) else {
            continue;
        };
        for (packed, coefficient) in &linear.terms {
            if !is_plus_or_minus_one(coefficient) || values.domain_is_complete(packed) {
                continue;
            }
            let Some(super::value::UcpValueDomain::FiniteSet(domain)) = values.domain(packed)
            else {
                continue;
            };
            let Some(candidate) =
                base_conversion_candidate(&linear, packed, coefficient, values, modulus)
            else {
                continue;
            };
            // Minden jelöltet testbeli maradékra hoz, majd a bizonyítottan egyértelmű számjegyekre bont.
            // Sikertelen felbontásnál None ágat ad, amelyet a feltételes vizsgálat kizárhat.
            let branches = domain
                .iter()
                .map(|value| {
                    let residue = ((value % modulus) + modulus) % modulus;
                    let digits = exact_digits(&residue, &candidate.base, candidate.digits.len())
                        .map(|digits| candidate.digits.iter().cloned().zip(digits).collect());
                    (value.clone(), digits)
                })
                .collect();
            candidates
                .entry(packed.clone())
                .or_insert(FiniteBaseCandidate {
                    packed: packed.clone(),
                    branches,
                });
        }
    }
    let mut candidates: Vec<_> = candidates.into_values().collect();
    candidates.sort_by(|left, right| {
        right
            .branches
            .len()
            .cmp(&left.branches.len())
            .then(left.packed.cmp(&right.packed))
    });
    candidates
}

fn parse_base_powers(
    mut digits_with_coefficients: Vec<(CellId, BigInt)>,
) -> Option<(BigInt, Vec<CellId>)> {
    // Legalább két számjegyet követel meg, mert ezek súlyaiból állapítja meg a számrendszer alapját.
    if digits_with_coefficients.len() < 2 {
        return None;
    }

    // Együttható szerint rendezi a cellákat, így növekvő helyiérték szerinti sorrendet kap.
    digits_with_coefficients.sort_by(|left, right| left.1.cmp(&right.1).then(left.0.cmp(&right.0)));

    //Az első együtthatónak 1-nek kell lennie: c^0
    if digits_with_coefficients[0].1 != BigInt::from(1) {
        return None;
    }

    // A második együtthatóból határozza meg a c alapot.
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
    // A legfelső, y_n számjegy celláját választja ki.
    let Some(highest_digit) = digits.last() else {
        return false;
    };
    //Domain nélkül nem tudja ellenőrizni a cikk feltételét, ezért nem következtet
    let Some(highest_domain) = values.domain(highest_digit) else {
        return false;
    };

    // Kiszámítja a c^n súlyt, ahol n a legfelső számjegy indexe.
    let base_power = pow_bigint(base, digits.len() - 1);
    // Lekéri a legfelső számjegy domainjének legnagyobb értékét.
    let highest_max = highest_domain.max_value();

    //A cikk feltétele: y_n < p / c^n - 1.
    // Egész számjegydomainnél az ekvivalens c^n * (max(y_n) + 1) < p feltételt ellenőrzi.
    let highest_bound_witness = &base_power * (highest_max + BigInt::from(1));
    highest_bound_witness < modulus.clone()
}

fn pow_bigint(base: &BigInt, exponent: usize) -> BigInt {
    // BigInt-hatványozást végez a megadott nemnegatív kitevővel.
    let mut result = BigInt::from(1);
    for _ in 0..exponent {
        result *= base;
    }
    result
}

fn exact_digits(value: &BigInt, base: &BigInt, digit_count: usize) -> Option<Vec<BigInt>> {
    // Negatív x értéknél nem ad nemnegatív számjegyekből álló felbontást.
    if value < &BigInt::from(0) {
        return None;
    }

    let mut remaining = value.clone();
    let mut digits = Vec::with_capacity(digit_count);

    for _ in 0..digit_count {
        // Az aktuális maradékból kiszámítja a legalsó számjegyet.
        digits.push(&remaining % base);
        // A következő számjegyhez az alappal osztja a megmaradt értéket.
        remaining /= base;
    }

    // Ha marad feldolgozatlan érték, elutasítja a túl rövid számjegyfelbontást.
    if remaining == BigInt::from(0) {
        Some(digits)
    } else {
        None
    }
}

fn is_plus_or_minus_one(value: &BigInt) -> bool {
    // A nullával egyenlő kifejezésben x-et +1 és -1 együtthatóval is felismeri.
    value == &BigInt::from(1) || value == &BigInt::from(-1)
}

fn linearize_zero_equation(expr: &UcpExpr, modulus: &BigInt) -> Option<LinearExpr> {
    //Ha egy szorzásban csak egy érdemi faktor marad, azt külön lineárisítja
    let factors = meaningful_product_factors(expr, modulus);
    if factors.len() == 1 {
        return linearize(factors[0]);
    }

    // Egyébként a teljes kifejezést próbálja lineáris alakra hozni.
    linearize(expr)
}

fn meaningful_product_factors<'a>(expr: &'a UcpExpr, modulus: &BigInt) -> Vec<&'a UcpExpr> {
    let mut factors = Vec::new();
    collect_meaningful_product_factors(expr, &mut factors, modulus);
    factors
}

fn collect_meaningful_product_factors<'a>(
    expr: &'a UcpExpr,
    factors: &mut Vec<&'a UcpExpr>,
    modulus: &BigInt,
) {
    match expr {
        //A szorzásfát kilapítja faktorlistává
        UcpExpr::Mul(left, right) => {
            collect_meaningful_product_factors(left, factors, modulus);
            collect_meaningful_product_factors(right, factors, modulus);
        }
        //A mínusz előjel nem számít a faktorok felismerésénél
        UcpExpr::Neg(inner) => collect_meaningful_product_factors(inner, factors, modulus),
        //Nem nulla skálázás mellett ugyanaz marad az érdemi faktor
        UcpExpr::Scale(inner, scalar) if scalar.is_non_zero_with_modulus(Some(modulus)) => {
            collect_meaningful_product_factors(inner, factors, modulus)
        }
        // Az igazoltan nemnulla konstans tényezőt elhagyja, mert nem változtatja meg a nullhelyeket.
        UcpExpr::Const(scalar) if scalar.is_non_zero_with_modulus(Some(modulus)) => {}
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
        //Ismeretlen konstansból nem tud pontos lineáris alakot képezni
        UcpExpr::Const(_) => None,
        UcpExpr::Neg(inner) => linearize(inner).map(|linear| linear.scale(BigInt::from(-1))),
        // Lineáris kifejezések összegét szintén lineáris alakra hozza.
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
        // Változót tartalmazó kifejezést nem fogad el tiszta konstansként.
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

    // A teszt a bináris számjegyek {0,1} domainjét állítja elő.
    fn boolean_domain() -> UcpValueDomain {
        UcpValueDomain::finite_set([BigInt::from(0), BigInt::from(1)]).unwrap()
    }

    // A teszt több bitcellához beállítja a {0,1} domaint.
    fn mark_bits(values: &mut UcpValueFacts, bits: &[CellId]) {
        for bit in bits {
            values.mark_domain(bit.clone(), boolean_domain());
        }
    }

    fn modulus() -> BigInt {
        BigInt::from(101)
    }

    // A teszt ellenőrzi, hogy ismert x esetén a rendszer a bináris számjegyek értékét is kiszámítja.
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

        let inferences = infer_base_conversions_with_modulus(&[expr], &facts, &values, &modulus());

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

    // A teszt ellenőrzi, hogy a rendszer x konkrét értéke nélkül is igazolja a számjegyek egyértelműségét.
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

        let inferences = infer_base_conversions_with_modulus(&[expr], &facts, &values, &modulus());

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

    // A teszt ellenőrzi, hogy számjegydomain nélkül nem alkalmazza a Base-Conv szabályt.
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

        assert!(
            infer_base_conversions_with_modulus(&[expr], &facts, &values, &modulus()).is_empty()
        );
    }

    //Ellenőrzi, hogy nem 1,c,c^2 alakú együtthatókra nem következtet
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

        assert!(
            infer_base_conversions_with_modulus(&[expr], &facts, &values, &modulus()).is_empty()
        );
    }

    // A teszt ellenőrzi, hogy lehetséges moduláris körbefordulásnál nem következtet.
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
