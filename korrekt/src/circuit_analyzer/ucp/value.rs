use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
};
use num_bigint::BigInt;
use std::collections::{BTreeSet, HashMap};

//Enum a Domain konkrét értékeire (konkrét érték vagy tartomány)
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpValueDomain {
    Exact(BigInt),
    FiniteSet(BTreeSet<BigInt>),
}

//A cellákhoz rendelt domain-t tárolja
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UcpValueFacts {
    domains: HashMap<CellId, UcpValueDomain>,
}

//Enum az értékekhez
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueKind {
    Zero,
    NonZero,
    Unknown,
}

//Lineárisan felírható kifejezés
#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearExpr {
    constant: BigInt,
    terms: HashMap<CellId, BigInt>,
}

impl UcpValueDomain {
    //Domain létrehozása konkrét értékkel
    pub fn exact(value: BigInt) -> Self {
        Self::Exact(value)
    }

    //Domain létrehozása a megadott tartománnyal
    pub fn finite_set<I>(values: I) -> Option<Self>
    where
        I: IntoIterator<Item = BigInt>,
    {
        let mut set = BTreeSet::new();

        //Biztonsági ellenőrzés
        for value in values {
            set.insert(bounded_value(value)?);
        }

        match set.len() {
            0 => None,
            1 => Some(Self::Exact(set.into_iter().next().unwrap())),
            _ => Some(Self::FiniteSet(set)),
        }
    }

    //Konkrét értéket visszaadja ha van
    pub fn exact_value(&self) -> Option<&BigInt> {
        match self {
            Self::Exact(value) => Some(value),
            Self::FiniteSet(_) => None,
        }
    }

    //Megmondja, hogy tudjuk-e már biztosan
    pub fn is_singleton(&self) -> bool {
        matches!(self, Self::Exact(_))
    }

    //Ellenőrzi, hogy ha konkrét akkor az az érték, ha pedig tartomány, akkor meg az összes érték a min és max közé esik-e
    pub fn is_subset_of_range(&self, min: &BigInt, max: &BigInt) -> bool {
        match self {
            Self::Exact(value) => value >= min && value <= max,
            Self::FiniteSet(values) => values.iter().all(|value| value >= min && value <= max),
        }
    }

    //Visszaadja a domain legnagyobb lehetséges értékét, ha erre intervallumos feltételt akarunk ellenőrizni
    pub fn max_value(&self) -> &BigInt {
        match self {
            Self::Exact(value) => value,
            Self::FiniteSet(values) => values
                .iter()
                .next_back()
                .expect("finite_set never creates an empty set"),
        }
    }

    //Két domain metszetét adja vissza
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

    //Visszaadja, hogy milyen típusú a domain értéke
    fn value_kind(&self) -> ValueKind {
        match self {
            Self::Exact(value) if value == &BigInt::from(0) => ValueKind::Zero,
            Self::Exact(_) => ValueKind::NonZero,
            //Biztonsági okból, ha már domain szerint lehetséges a 0 akkor Unknown lesz
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

    //Kényelmi függvény a konkrét érték beállítására
    //Igazat ad vissza, ha tanultunk újat és menjen még UCP kör
    pub fn mark_known(&mut self, cell: CellId, value: BigInt) -> bool {
        self.mark_domain(cell, UcpValueDomain::exact(value))
    }

    //A domain beállítása
    //Igazat ad vissza, ha tanultunk újat és menjen még UCP kör
    pub fn mark_domain(&mut self, cell: CellId, domain: UcpValueDomain) -> bool {
        //A megadott domain ellenőrzése
        let domain = match domain {
            //A bounded_value-ba esik-e
            UcpValueDomain::Exact(value) => UcpValueDomain::Exact(match bounded_value(value) {
                Some(value) => value,
                None => return false,
            }),
            //Ellenőrzi, hogy tud-e érvényes domaint létrehozni
            UcpValueDomain::FiniteSet(values) => {
                let Some(domain) = UcpValueDomain::finite_set(values) else {
                    return false;
                };
                domain
            }
        };

        //Megnézi, hogy a korábbi cellának volt-e már domain-je
        match self.domains.get(&cell) {
            Some(existing) => {
                //Ha van megnézi a korábbi meg a mostani metszetét meg lehet-e határozni
                let Some(intersection) = existing.intersect(&domain) else {
                    return false;
                };
                //Ha meg lehet és megegyezik a kettő
                if &intersection == existing {
                    false
                } else {
                    //Felülírja a korábbit az új metszetre
                    self.domains.insert(cell, intersection);
                    true
                }
            }
            //Ha nem volt akkor a fent kapott lesz
            None => {
                self.domains.insert(cell, domain);
                true
            }
        }
    }

    //Visszaadja a konkrét értéket
    pub fn known_value(&self, cell: &CellId) -> Option<&BigInt> {
        self.domains.get(cell)?.exact_value()
    }

    //Visszaadja a tartományt
    pub fn domain(&self, cell: &CellId) -> Option<&UcpValueDomain> {
        self.domains.get(cell)
    }

    //Ellenőrzi, hogy a cellához tartozó domain teljesen a megadott intervallumba esik-e
    pub fn domain_is_subset_of_range(&self, cell: &CellId, min: &BigInt, max: &BigInt) -> bool {
        self.domain(cell)
            .map(|domain| domain.is_subset_of_range(min, max))
            .unwrap_or(false)
    }

    //Visszaadja az összes eddig ismert domain-t
    pub fn domains(&self) -> &HashMap<CellId, UcpValueDomain> {
        &self.domains
    }

    //Kiszedi azokat a cellákat, amelyeknek már konkrét értékük van
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

//Az analyzer input instance celláiból létrehozza a kezdeti Delta értékeket (Konkrét értékek)
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

//Megpróbál egy UCP expression-t konkrét értékre kiértékelni a már ismert Delta alapján
pub fn evaluate_expr(expr: &UcpExpr, values: &UcpValueFacts) -> Option<BigInt> {
    match expr {
        //Ha az adott cellához van konkrét érték, akkor megadja
        UcpExpr::Var(cell) => bounded_value(values.known_value(cell)?.clone()),
        //Ha a konstans konkrétan ismert, akkor visszaadja az értékét
        UcpExpr::Const(scalar) => bounded_value(scalar.as_known()?),
        //Ha a belső kifejezés kiértékelhető, akkor az ellentettjét adja
        UcpExpr::Neg(inner) => bounded_value(-evaluate_expr(inner, values)?),
        //Akkor értékelhető ki, ha mindkét oldal konkrétan kiértékelhető
        UcpExpr::Add(left, right) => {
            bounded_value(evaluate_expr(left, values)? + evaluate_expr(right, values)?)
        }
        //Akkor értékelhető ki, ha mindkét szorzótényező konkrétan kiértékelhető
        UcpExpr::Mul(left, right) => {
            bounded_value(evaluate_expr(left, values)? * evaluate_expr(right, values)?)
        }
        //Skálázásnál csak ismert skálával számolunk, kivéve ha a skála biztosan nulla
        UcpExpr::Scale(inner, scalar) => match scalar {
            //Nullával szorzás mindig nulla
            UcpScalar::Zero => Some(BigInt::from(0)),
            //Konkrét skálánál kiszámolja a belső érték és a skála szorzatát
            UcpScalar::Known(scale) => bounded_value(evaluate_expr(inner, values)? * scale),
            //Ismeretlen, de nem nulla skálánál csak akkor tudunk biztosat, ha a belső érték nulla
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

//Biztonsági szűrő: csak kis, integerként kezelhető értékekkel következtetünk
fn bounded_value(value: BigInt) -> Option<BigInt> {
    if value == BigInt::from(0)
        || (value >= BigInt::from(i64::MIN) && value <= BigInt::from(i64::MAX))
    {
        Some(value)
    } else {
        None
    }
}

//Megmondja, hogy egy expression biztosan nulla, biztosan nem nulla, vagy ismeretlen
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
            UcpExpr::Const(UcpScalar::NonZero) => ValueKind::NonZero,
            //Nagy field reprezentánsoknál modulus nélkül nem döntjük el integerből, hogy nonzero-e
            UcpExpr::Const(UcpScalar::Known(value)) => bounded_value(value.clone())
                .map(|value| {
                    if value == BigInt::from(0) {
                        ValueKind::Zero
                    } else {
                        ValueKind::NonZero
                    }
                })
                .unwrap_or(ValueKind::Unknown),
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

//Nullára kényszerített expressionből próbál új Delta domain-eket tanulni
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

//Csak a konkrét értékű következtetéseket adja vissza
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

//Root szabály: például b * (b - 1) = 0 alapján Delta(b) = {0, 1}
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

//Szorzatot faktorokra bont, hogy a root szabály felismerhető legyen
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

//Egy faktorból kinyeri, hogy melyik cellára milyen gyököt jelent
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

//Null-egyenletből konkrét cellaértéket próbál kikövetkeztetni
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

//Lineáris null-egyenletet old meg, ha pontosan egy ismeretlen cella marad
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

//UcpExpr-ből lineáris alakot készít: constant + coefficient * cell + ...
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

//String cellanévből CellId-t készít, például "I-0-0" -> instance(0, 0)
fn parse_cell_id(name: &str) -> Option<CellId> {
    let mut parts = name.split('-');
    let kind = parts.next()?;
    let column = parts.next()?.parse::<usize>().ok()?;
    let row = parts.next()?.parse::<i32>().ok()?;
    if parts.next().is_some() {
        return None;
    }

    //Meghívja a megfelelő konstruktort
    match kind {
        "A" => Some(CellId::advice(column, row)),
        "I" => Some(CellId::instance(column, row)),
        "F" => Some(CellId::fixed(column, row)),
        _ => None,
    }
}

impl LinearExpr {
    //Konstans lineáris kifejezést hoz létre
    fn constant(value: BigInt) -> Self {
        Self {
            constant: value,
            terms: HashMap::new(),
        }
    }

    //Egy darab cellatagot hoz létre a megadott együtthatóval
    fn term(cell: CellId, coefficient: BigInt) -> Self {
        Self {
            constant: BigInt::from(0),
            terms: HashMap::from([(cell, coefficient)]),
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

    //Lineáris kifejezést beszoroz egy skalárral
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

    //Azt ellenőrzi, hogy ismert értékekkel egy egyszerű aritmetikai expression kiértékelhető
    #[test]
    fn evaluates_known_arithmetic_expression() {
        let x = CellId::instance(0, 0);
        let mut values = UcpValueFacts::new();
        values.mark_known(x.clone(), BigInt::from(2));
        let expr = UcpExpr::add(UcpExpr::var(x), UcpExpr::known_constant_i64(-1));

        assert_eq!(evaluate_expr(&expr, &values), Some(BigInt::from(1)));
        assert_eq!(value_kind(&expr, &values), ValueKind::NonZero);
    }

    //Azt ellenőrzi, hogy nonzero * y = 0 alakból y = 0 következik
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

    //Azt ellenőrzi, hogy x - 5 = 0 alakból konkrétan x = 5 tanulható
    #[test]
    fn learns_linear_assignment_value() {
        let x = CellId::advice(0, 0);
        let expr = UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(-5));

        assert_eq!(
            infer_value_assignments_from_zero_equation(&expr, &UcpValueFacts::new()),
            vec![(x, BigInt::from(5))]
        );
    }

    //Azt ellenőrzi, hogy b * (b - 1) = 0 alapján Delta(b) = {0, 1}
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

    //Azt ellenőrzi, hogy x * x = 0 alapján konkrétan x = 0 tanulható
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

    //Azt ellenőrzi, hogy két domain metszete szűkítheti a boolean domaint konkrét értékre
    #[test]
    fn intersecting_domain_can_refine_boolean_to_exact_value() {
        let b = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();

        assert!(values.mark_domain(b.clone(), finite_domain(&[0, 1])));
        assert!(values.mark_known(b.clone(), BigInt::from(1)));

        assert_eq!(values.known_value(&b), Some(&BigInt::from(1)));
    }

    //Azt ellenőrzi, hogy egy finite domain teljesen beleesik-e egy adott intervallumba
    #[test]
    fn finite_domain_can_be_checked_against_digit_range() {
        let b = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();

        values.mark_domain(b.clone(), finite_domain(&[0, 1]));

        assert!(values.domain_is_subset_of_range(&b, &BigInt::from(0), &BigInt::from(1)));
        assert!(values.domain_is_subset_of_range(&b, &BigInt::from(0), &BigInt::from(9)));
        assert!(!values.domain_is_subset_of_range(&b, &BigInt::from(1), &BigInt::from(9)));
    }
}
