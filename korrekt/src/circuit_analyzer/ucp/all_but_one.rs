// Ez a modul a cikk All-But-One-0 szabályát valósítja meg.
// A szabály több zero equationt egyszerre néz:
//   sum(y_i) = e
//   y_i * (x - i) = 0 minden i-re 0..n között
// Ha x és e már unique, és a rootok pontosan 0..n, akkor minden y_i unique.
// Ha x és e konkrét értéke is ismert, akkor konkrét y_i értékeket is tudunk tanulni.
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
    //Az a cella, amiről a szabály kimondta, hogy unique
    pub cell: CellId,
    //Ha nemcsak unique, hanem konkrét értéke is ismert, akkor itt adjuk vissza
    pub value: Option<BigInt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProductConstraint {
    //A y_i változó a y_i * (x - root) = 0 alakból
    y: CellId,
    //Az a unique változó, ami kiválasztja, melyik y_i lehet nem nulla
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

//Végigfuttatja az All-But-One-0 szabályt az összes már kinyert UCP expressionön
pub fn infer_all_but_one_zero(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    values: &UcpValueFacts,
) -> Vec<AllButOneInference> {
    //Külön kigyűjtjük a y_i * (x - root_i) = 0 típusú constraint-eket
    let product_constraints = collect_product_constraints(expressions, facts);
    //Külön kigyűjtjük a sum(y_i) = e típusú constraint-eket
    let sum_constraints = collect_sum_constraints(expressions, facts, values);
    let mut inferences = BTreeMap::new();

    for sum in sum_constraints {
        for (x, products_by_y) in &product_constraints {
            //Csak akkor illeszkedik a szabály, ha minden y_i-hez pontosan egy root tartozik,
            //és ezek a rootok pontosan a cikk szerinti 0..n értékek
            let Some(root_by_y) = roots_for_sum(&sum, products_by_y) else {
                continue;
            };

            //Ha x konkrét értéke ismert, akkor azt is meg tudjuk mondani, melyik y_i lesz e és melyik 0
            let x_value = values.known_value(x).cloned();

            for (cell, root) in root_by_y {
                let value = x_value.as_ref().and_then(|x_value| {
                    if &root == x_value {
                        sum.e_value.clone()
                    } else {
                        Some(BigInt::from(0))
                    }
                });

                //BTreeMap-et használunk, hogy determinisztikus sorrendben kapjuk vissza az eredményeket
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
    //Felépítés: x -> y_i -> {rootok}
    let mut constraints: HashMap<CellId, HashMap<CellId, BTreeSet<BigInt>>> = HashMap::new();

    for expr in expressions {
        let Some(product) = parse_product_constraint(expr) else {
            continue;
        };

        //A szabályhoz x-nek már unique-nak kell lennie
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
    //Minden expressiont megpróbálunk összeg-constraintként értelmezni
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
        //Minden y_i-hez kell tartoznia product constraintnek
        let product_roots = products_by_y.get(y)?;
        //És pontosan egy rootja lehet, különben nem tiszta one-hot szerkezet
        if product_roots.len() != 1 {
            return None;
        }

        let root = product_roots.iter().next()?.clone();
        //A rootoknak különbözniük kell, mert különben két y_i ugyanarra az x értékre nyílna ki
        if !roots.insert(root.clone()) {
            return None;
        }

        root_by_y.insert(y.clone(), root);
    }

    //A képen lévő szabály nem tetszőleges különböző rootokra szól,
    //hanem konkrétan i = 0..n értékekre.
    let expected_roots: BTreeSet<BigInt> = (0..sum.y_cells.len()).map(BigInt::from).collect();
    if roots != expected_roots {
        return None;
    }

    Some(root_by_y)
}

fn parse_product_constraint(expr: &UcpExpr) -> Option<ProductConstraint> {
    //A termékből kidobjuk a nem érdemi konstans szorzókat, és két tényleges faktort várunk
    let factors = meaningful_product_factors(expr);
    if factors.len() != 2 {
        return None;
    }

    //A két faktor sorrendje mindegy: y * (x-root) és (x-root) * y is jó
    parse_product_pair(factors[0], factors[1])
        .or_else(|| parse_product_pair(factors[1], factors[0]))
}

fn parse_product_pair(y_expr: &UcpExpr, root_expr: &UcpExpr) -> Option<ProductConstraint> {
    //Az egyik oldalnak egy sima y változónak kell lennie
    let y = parse_plain_var(y_expr)?;
    //A másik oldalnak x - root vagy root - x alakúnak kell lennie
    let (x, root) = parse_root_factor(root_expr)?;

    Some(ProductConstraint { y, x, root })
}

fn parse_sum_constraint(
    expr: &UcpExpr,
    facts: &UcpFacts,
    values: &UcpValueFacts,
) -> Option<SumConstraint> {
    //Az expressiont lineáris zero equationként próbáljuk olvasni
    let linear = linearize_zero_equation(expr, values)?;
    if linear.terms.len() < 2 {
        return None;
    }

    //Ebben a szabályban csak +1 és -1 együtthatós összegeket kezelünk
    if linear
        .terms
        .values()
        .any(|coefficient| coefficient != &BigInt::from(1) && coefficient != &BigInt::from(-1))
    {
        return None;
    }

    //Szétválasztjuk a bal/jobb oldalon lévő tagokat az előjelük alapján
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
    //sum(y_i) + c = 0 alak: itt e egy konstansként jön ki
    if positive.len() >= 2 && negative.is_empty() {
        return Some(SumConstraint {
            y_cells: positive,
            e_value: bounded_value(-constant),
        });
    }

    //-sum(y_i) + c = 0 alak: ugyanaz előjelcserével
    if negative.len() >= 2 && positive.is_empty() {
        return Some(SumConstraint {
            y_cells: negative,
            e_value: bounded_value(constant),
        });
    }

    //sum(y_i) - e + c = 0 alak: e-nek unique-nak kell lennie
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

    //e - sum(y_i) + c = 0 alak: ez az előző tükörképe
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
        //A többszörös szorzást kilapítjuk faktorlistává
        UcpExpr::Mul(left, right) => {
            collect_meaningful_product_factors(left, factors);
            collect_meaningful_product_factors(right, factors);
        }
        //A mínusz előjel nem változtatja meg, hogy melyik faktor érdemi
        UcpExpr::Neg(inner) => collect_meaningful_product_factors(inner, factors),
        //Nem nulla skálázás mellett ugyanaz a faktorstruktúra marad
        UcpExpr::Scale(inner, scalar) if scalar.is_statically_non_zero() => {
            collect_meaningful_product_factors(inner, factors)
        }
        //Nem nulla konstans szorzót elhagyhatunk a mintázat felismeréséhez
        UcpExpr::Const(UcpScalar::NonZero | UcpScalar::Known(_)) => {}
        //Nullával szorzott rész nem ad hasznos All-But-One információt
        UcpExpr::Scale(_, UcpScalar::Zero) | UcpExpr::Const(UcpScalar::Zero) => {}
        //Minden más valódi faktor marad
        _ => factors.push(expr),
    }
}

fn parse_plain_var(expr: &UcpExpr) -> Option<CellId> {
    match expr {
        //Sima változó
        UcpExpr::Var(cell) => Some(cell.clone()),
        //Előjel és nem nulla skálázás mellett is ugyanazt a változót nézzük
        UcpExpr::Neg(inner) => parse_plain_var(inner),
        UcpExpr::Scale(inner, scalar) if scalar.is_statically_non_zero() => parse_plain_var(inner),
        _ => None,
    }
}

fn parse_root_factor(expr: &UcpExpr) -> Option<(CellId, BigInt)> {
    //x - c vagy c - x alakot keresünk lineáris formában
    let linear = linearize_symbolic(expr)?;
    if linear.terms.len() != 1 {
        return None;
    }

    let (cell, coefficient) = linear.terms.into_iter().next().unwrap();
    //Csak x-c / c-x alakot engedünk, ezért az együttható csak +1 vagy -1 lehet
    if coefficient != BigInt::from(1) && coefficient != BigInt::from(-1) {
        return None;
    }

    //Megoldjuk a lineáris faktort nullára: coefficient * x + constant = 0
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
        //Ismeretlen konstansból nem tudunk pontos lineáris alakot csinálni
        UcpExpr::Const(_) => None,
        UcpExpr::Neg(inner) => {
            linearize_symbolic(inner).map(|linear| linear.scale(BigInt::from(-1)))
        }
        //Lineáris tagok összeadhatók
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
            //Ismeretlen vagy csak nonzero skálával nem tudunk pontos konstans szorzót számolni
            UcpScalar::NonZero | UcpScalar::Unknown => None,
        },
    }
}

fn constant_expr_value(expr: &UcpExpr) -> Option<BigInt> {
    match expr {
        //Változót tartalmazó expression nem tiszta konstans
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
    //Ha az expression valójában csak egy érdemi faktort tartalmaz, azt külön lineárisítjuk
    let factors = meaningful_product_factors(expr);
    if factors.len() == 1 {
        return linearize(factors[0], values);
    }

    //Egyébként az egész zero equationt próbáljuk lineáris alakra hozni
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
            //Pontos lineáris alakhoz itt konkrét skála kellene
            UcpScalar::NonZero | UcpScalar::Unknown => None,
        },
    }
}

fn bounded_value(value: BigInt) -> Option<BigInt> {
    //Védőkorlát: a mostani value inference csak kezelhető méretű integer értékeket tárol
    if value == BigInt::from(0)
        || (value >= BigInt::from(i64::MIN) && value <= BigInt::from(i64::MAX))
    {
        Some(value)
    } else {
        None
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

    //Segédfüggvény y * (x - root) alakú product equation építéséhez
    fn product(y: &CellId, x: &CellId, root: i64) -> UcpExpr {
        UcpExpr::mul(
            UcpExpr::var(y.clone()),
            UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(-root)),
        )
    }

    //Ellenőrzi, hogy a one-hot mintából konkrét értékek nélkül is unique-k lesznek a y_i-k
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

    //Ellenőrzi, hogy ismert x és e esetén a konkrét y_i értékeket is továbbvisszük
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

    //Ellenőrzi, hogy nem következtetünk, ha az összeg jobb oldala nem unique
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

    //Ellenőrzi, hogy duplikált rootoknál nem alkalmazzuk tévesen a szabályt
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

    //Ellenőrzi, hogy különböző, de nem 0..n rootokra nem alkalmazzuk a cikk konkrét szabályát
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
