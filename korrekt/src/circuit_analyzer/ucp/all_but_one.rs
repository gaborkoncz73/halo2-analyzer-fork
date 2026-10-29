// Ez a modul a cikk All-But-One-0 szabályát valósítja meg.
// A szabály több nullával egyenlő kifejezést vizsgál együtt:
//   sum(y_i) = e
//   y_i * (x - i) = 0 minden i-re 0..n között
// Ha x és e egyértelmű, és a gyökök pontosan 0..n értékűek, minden y_i egyértelmű.
// Ha x és e konkrét értéke is ismert, a megfelelő y_i értékeket is kiszámítja.
use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
    facts::UcpFacts,
    value::{bounded_value, evaluate_expr, normalize_field_value, UcpValueFacts},
};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AllButOneInference {
    // Az a cella, amelynek egyértelműségét a szabály igazolja.
    pub cell: CellId,
    // Ha a konkrét értéket is kiszámítja, ebben a mezőben adja vissza.
    pub value: Option<BigInt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProductConstraint {
    // A y_i cellát azonosítja a y_i * (x - root) = 0 alakban.
    y: CellId,
    // Az egyértelmű x cellát azonosítja, amely kiválasztja a nemnulla y_i tagot.
    x: CellId,
    //Az az érték, ahol az adott y_i nem kényszerül nullára
    root: BigInt,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SumConstraint {
    //Az összegben szereplő y_i cellák
    y_cells: Vec<CellId>,
    //Az e oldal konkrét értéke, ha Delta alapján ismert
    e_value: Option<BigInt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearExpr {
    //A változóktól független konstans tag
    constant: BigInt,
    //A lineáris változótagok: cella -> együttható
    terms: BTreeMap<CellId, BigInt>,
}

// Az All-But-One-0 szabályt alkalmazza a kinyert UCP-kifejezésekre.
pub fn infer_all_but_one_zero(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    values: &UcpValueFacts,
) -> Vec<AllButOneInference> {
    infer_all_but_one_with_optional_modulus(expressions, facts, values, None)
}

pub fn infer_all_but_one_zero_with_modulus(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> Vec<AllButOneInference> {
    if modulus <= &BigInt::from(1) {
        return Vec::new();
    }
    infer_all_but_one_with_optional_modulus(expressions, facts, values, Some(modulus))
}

fn infer_all_but_one_with_optional_modulus(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    values: &UcpValueFacts,
    modulus: Option<&BigInt>,
) -> Vec<AllButOneInference> {
    // Külön kigyűjti a y_i * (x - root_i) = 0 alakú kényszereket.
    let product_constraints = collect_product_constraints(expressions, facts, modulus);
    // Külön kigyűjti a sum(y_i) = e alakú kényszereket.
    let sum_constraints = collect_sum_constraints(expressions, facts, values, modulus);
    let mut inferences = BTreeMap::new();

    for sum in sum_constraints {
        // Ellenőrzi, hogy a 0..n gyökök a tényleges testben is különböznek.
        if modulus.is_some_and(|modulus| BigInt::from(sum.y_cells.len()) > *modulus) {
            continue;
        }
        for (x, products_by_y) in &product_constraints {
            // Csak akkor alkalmazza a szabályt, ha minden y_i-hez pontosan egy gyök tartozik,
            // és a gyökök együtt pontosan a szabályban szereplő 0..n értékeket adják.
            let Some(root_by_y) = roots_for_sum(&sum, products_by_y) else {
                continue;
            };

            // Ismert x esetén meghatározza, melyik y_i kapja e értékét, a többit nullának veszi.
            let x_value = values.known_value(x).cloned();

            for (cell, root) in root_by_y {
                let value = x_value.as_ref().and_then(|x_value| {
                    let matches = match modulus {
                        Some(modulus) => (&root - x_value) % modulus == BigInt::from(0),
                        None => &root == x_value,
                    };
                    if matches {
                        sum.e_value.clone().and_then(|value| match modulus {
                            Some(modulus) => normalize_field_value(value, modulus),
                            None => Some(value),
                        })
                    } else {
                        Some(BigInt::from(0))
                    }
                });

                // BTreeMap használatával determinisztikus sorrendben adja vissza az eredményeket.
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
    modulus: Option<&BigInt>,
) -> HashMap<CellId, HashMap<CellId, BTreeSet<BigInt>>> {
    // Az x -> y_i -> {gyökök} kapcsolatok szerint csoportosítja a szorzatkényszereket.
    let mut constraints: HashMap<CellId, HashMap<CellId, BTreeSet<BigInt>>> = HashMap::new();

    for expr in expressions {
        let Some(product) = parse_product_constraint(expr, modulus) else {
            continue;
        };

        // Csak akkor fogadja el a mintát, ha x egyértelműsége már igazolt.
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
    modulus: Option<&BigInt>,
) -> Vec<SumConstraint> {
    // Minden kifejezést megpróbál összegkényszerként értelmezni.
    expressions
        .iter()
        .filter_map(|expr| parse_sum_constraint(expr, facts, values, modulus))
        .collect()
}

fn roots_for_sum(
    sum: &SumConstraint,
    products_by_y: &HashMap<CellId, BTreeSet<BigInt>>,
) -> Option<BTreeMap<CellId, BigInt>> {
    let mut root_by_y = BTreeMap::new();
    let mut roots = BTreeSet::new();

    for y in &sum.y_cells {
        // Minden y_i-hez megköveteli a megfelelő szorzatkényszert.
        let product_roots = products_by_y.get(y)?;
        // Pontosan egy gyököt fogad el, hogy a kiválasztási szerkezet egyértelmű legyen.
        if product_roots.len() != 1 {
            return None;
        }

        let root = product_roots.iter().next()?.clone();
        // Különböző gyököket követel meg, így két y_i nem maradhat szabad ugyanannál az x-nél.
        if !roots.insert(root.clone()) {
            return None;
        }

        root_by_y.insert(y.clone(), root);
    }

    // A szabályt nem tetszőleges különböző gyökökre alkalmazza,
    // hanem kifejezetten a 0..n indexekből álló gyökhalmazra.
    let expected_roots: BTreeSet<BigInt> = (0..sum.y_cells.len()).map(BigInt::from).collect();
    if roots != expected_roots {
        return None;
    }

    Some(root_by_y)
}

fn parse_product_constraint(expr: &UcpExpr, modulus: Option<&BigInt>) -> Option<ProductConstraint> {
    // Elhagyja az igazoltan nemnulla konstans tényezőket, majd két érdemi tényezőt keres.
    let factors = meaningful_product_factors(expr, modulus);
    if factors.len() != 2 {
        return None;
    }

    // A y * (x-root) és (x-root) * y sorrendet egyaránt felismeri.
    parse_product_pair(factors[0], factors[1], modulus)
        .or_else(|| parse_product_pair(factors[1], factors[0], modulus))
}

fn parse_product_pair(
    y_expr: &UcpExpr,
    root_expr: &UcpExpr,
    modulus: Option<&BigInt>,
) -> Option<ProductConstraint> {
    // Az egyik tényezőben egyszerű y változót keres.
    let y = parse_plain_var(y_expr, modulus)?;
    // A másik tényezőben x - root vagy root - x alakot keres.
    let (x, root) = parse_root_factor(root_expr)?;

    Some(ProductConstraint { y, x, root })
}

fn parse_sum_constraint(
    expr: &UcpExpr,
    facts: &UcpFacts,
    values: &UcpValueFacts,
    modulus: Option<&BigInt>,
) -> Option<SumConstraint> {
    // A kifejezést lineáris, nullával egyenlő kényszerként értelmezi.
    let linear = linearize_zero_equation(expr, values, modulus)?;
    if linear.terms.len() < 2 {
        return None;
    }

    // Csak +1 és -1 együtthatós összegeket fogad el ehhez a mintához.
    if linear
        .terms
        .values()
        .any(|coefficient| coefficient != &BigInt::from(1) && coefficient != &BigInt::from(-1))
    {
        return None;
    }

    // Előjel szerint szétválasztja a bal és jobb oldalra kerülő tagokat.
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
    // A sum(y_i) + c = 0 alaknál e értékét konstansból számítja.
    if positive.len() >= 2 && negative.is_empty() {
        return Some(SumConstraint {
            y_cells: positive,
            e_value: bounded_value(-constant),
        });
    }

    // A -sum(y_i) + c = 0 alakot előjelcserével kezeli.
    if negative.len() >= 2 && positive.is_empty() {
        return Some(SumConstraint {
            y_cells: negative,
            e_value: bounded_value(constant),
        });
    }

    // A sum(y_i) - e + c = 0 alaknál megköveteli e egyértelműségét.
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

    // Az e - sum(y_i) + c = 0 alakot az ellenkező oldalra rendezett összegként kezeli.
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

fn meaningful_product_factors<'a>(expr: &'a UcpExpr, modulus: Option<&BigInt>) -> Vec<&'a UcpExpr> {
    let mut factors = Vec::new();
    collect_meaningful_product_factors(expr, &mut factors, modulus);
    factors
}

fn collect_meaningful_product_factors<'a>(
    expr: &'a UcpExpr,
    factors: &mut Vec<&'a UcpExpr>,
    modulus: Option<&BigInt>,
) {
    match expr {
        // A többszörös szorzást tényezőlistává lapítja.
        UcpExpr::Mul(left, right) => {
            collect_meaningful_product_factors(left, factors, modulus);
            collect_meaningful_product_factors(right, factors, modulus);
        }
        // Az előjelváltást elhagyja, mert nem változtatja meg a nullhelyeket.
        UcpExpr::Neg(inner) => collect_meaningful_product_factors(inner, factors, modulus),
        // Nemnulla skálázásnál megtartja a belső tényezőszerkezetet.
        UcpExpr::Scale(inner, scalar) if scalar.is_non_zero_with_modulus(modulus) => {
            collect_meaningful_product_factors(inner, factors, modulus)
        }
        // Az igazoltan nemnulla konstans tényezőt elhagyja a mintafelismerésből.
        UcpExpr::Const(scalar) if scalar.is_non_zero_with_modulus(modulus) => {}
        // Megtartja a nullatényezőt: elhagyásával azonosságból hamis korlátozást képezne.
        // Minden más érdemi tényezőt megtart.
        _ => factors.push(expr),
    }
}

fn parse_plain_var(expr: &UcpExpr, modulus: Option<&BigInt>) -> Option<CellId> {
    match expr {
        // Az egyszerű változó azonosítóját adja vissza.
        UcpExpr::Var(cell) => Some(cell.clone()),
        // Előjelváltás vagy nemnulla skálázás mellett a belső változót azonosítja.
        UcpExpr::Neg(inner) => parse_plain_var(inner, modulus),
        UcpExpr::Scale(inner, scalar) if scalar.is_non_zero_with_modulus(modulus) => {
            parse_plain_var(inner, modulus)
        }
        _ => None,
    }
}

fn parse_root_factor(expr: &UcpExpr) -> Option<(CellId, BigInt)> {
    // Lineáris alakban x - c vagy c - x tényezőt keres.
    let linear = linearize_symbolic(expr)?;
    if linear.terms.len() != 1 {
        return None;
    }

    let (cell, coefficient) = linear.terms.into_iter().next().unwrap();
    // Csak +1 vagy -1 együtthatót fogad el az x-c és c-x mintához.
    if coefficient != BigInt::from(1) && coefficient != BigInt::from(-1) {
        return None;
    }

    // A coefficient * x + constant = 0 egyenletből kiszámítja a gyököt.
    let numerator = -linear.constant;
    if &numerator % &coefficient != BigInt::from(0) {
        return None;
    }

    Some((cell, bounded_value(numerator / coefficient)?))
}

fn linearize_symbolic(expr: &UcpExpr) -> Option<LinearExpr> {
    //Ha az egész kifejezés tiszta konstans, akkor abból lineáris konstans lesz
    if let Some(value) = constant_expr_value(expr) {
        return Some(LinearExpr::constant(value));
    }

    match expr {
        //Egy cella lineárisan 1 * cell
        UcpExpr::Var(cell) => Some(LinearExpr::term(cell.clone(), BigInt::from(1))),
        // Ismeretlen értékű konstansból nem készít pontos lineáris alakot.
        UcpExpr::Const(_) => None,
        UcpExpr::Neg(inner) => {
            linearize_symbolic(inner).map(|linear| linear.scale(BigInt::from(-1)))
        }
        // A lineáris tagokat összeadja.
        UcpExpr::Add(left, right) => {
            Some(linearize_symbolic(left)?.add(linearize_symbolic(right)?))
        }
        //Szorzás csak akkor marad lineáris, ha az egyik oldal konstans
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
            // Absztrakt nemnulla vagy ismeretlen skála esetén nem állít elő pontos együtthatót.
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

fn linearize_zero_equation(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    modulus: Option<&BigInt>,
) -> Option<LinearExpr> {
    // Egyetlen érdemi tényezőt tartalmazó szorzatnál azt a tényezőt linearizálja.
    let factors = meaningful_product_factors(expr, modulus);
    if factors.len() == 1 {
        return linearize(factors[0], values);
    }

    // Egyébként a teljes nullával egyenlő kifejezést próbálja linearizálni.
    linearize(expr, values)
}

fn linearize(expr: &UcpExpr, values: &UcpValueFacts) -> Option<LinearExpr> {
    //Ha Delta alapján pontosan kiértékelhető, akkor konstans lineáris kifejezés lesz
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
        //Szorzás csak akkor kezelhető lineárisan, ha az egyik oldal ismert érték
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
            //Pontos lineáris alakot csak konkrét skálával készít.
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

    // A teszt y * (x - root) alakú szorzatkényszert állít elő.
    fn product(y: &CellId, x: &CellId, root: i64) -> UcpExpr {
        UcpExpr::mul(
            UcpExpr::var(y.clone()),
            UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(-root)),
        )
    }

    // A teszt ellenőrzi, hogy a kiválasztási minta konkrét értékek nélkül is igazolja y_i egyértelműségét.
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

    // A teszt ellenőrzi, hogy ismert x és e esetén a rendszer a konkrét y_i értékeket is visszaadja.
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

    // A teszt ellenőrzi, hogy a rendszer nem következtet, ha az összeg jobb oldala nem egyértelmű.
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

    // A teszt ellenőrzi, hogy ismétlődő gyökökre nem alkalmazza a szabályt.
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

    // A teszt ellenőrzi, hogy a 0..n halmaztól eltérő gyökökre nem alkalmazza a szabályt.
    #[test]
    fn does_not_fire_when_roots_are_distinct_but_not_zero_to_n() {
        let x = CellId::instance(0, 0);
        let e = CellId::instance(1, 0);
        let y0 = CellId::advice(0, 0);
        let y1 = CellId::advice(1, 0);
        let expressions = vec![
            product(&y0, &x, 4),
            product(&y1, &x, 5),
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
