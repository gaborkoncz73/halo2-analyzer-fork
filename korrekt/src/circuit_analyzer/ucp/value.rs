use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
};
use num_bigint::BigInt;
use std::collections::{BTreeSet, HashMap};

const MAX_FINITE_DOMAIN_SIZE: usize = 256;

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

//Megpróbál egy expressionhöz teljes véges Delta domaint számolni modulus nélkül
pub fn expression_domain(expr: &UcpExpr, values: &UcpValueFacts) -> Option<UcpValueDomain> {
    expression_domain_with_optional_modulus(expr, values, None)
}

//Megpróbál egy expressionhöz teljes véges Delta domaint számolni a field modulus szerint
pub fn expression_domain_with_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: &BigInt,
) -> Option<UcpValueDomain> {
    expression_domain_with_optional_modulus(expr, values, Some(field_modulus))
}

fn expression_domain_with_optional_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Option<UcpValueDomain> {
    match expr {
        UcpExpr::Var(cell) => values.domain(cell).cloned(),
        UcpExpr::Const(scalar) => finite_domain_from_values([scalar.as_known()?], field_modulus),
        UcpExpr::Neg(inner) => {
            let inner = expression_domain_with_optional_modulus(inner, values, field_modulus)?;
            map_domain_values(&inner, field_modulus, |value| -value)
        }
        UcpExpr::Add(left, right) => {
            let left = expression_domain_with_optional_modulus(left, values, field_modulus)?;
            let right = expression_domain_with_optional_modulus(right, values, field_modulus)?;
            combine_domain_values(&left, &right, field_modulus, |left, right| left + right)
        }
        UcpExpr::Mul(left, right) => {
            if value_kind(left, values) == ValueKind::Zero
                || value_kind(right, values) == ValueKind::Zero
            {
                return Some(UcpValueDomain::exact(BigInt::from(0)));
            }

            let left = expression_domain_with_optional_modulus(left, values, field_modulus)?;
            let right = expression_domain_with_optional_modulus(right, values, field_modulus)?;
            combine_domain_values(&left, &right, field_modulus, |left, right| left * right)
        }
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => Some(UcpValueDomain::exact(BigInt::from(0))),
            UcpScalar::Known(scale) => {
                let inner = expression_domain_with_optional_modulus(inner, values, field_modulus)?;
                map_domain_values(&inner, field_modulus, |value| value * scale)
            }
            UcpScalar::NonZero | UcpScalar::Unknown => {
                if value_kind(inner, values) == ValueKind::Zero {
                    Some(UcpValueDomain::exact(BigInt::from(0)))
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

fn normalize_value(value: BigInt, field_modulus: Option<&BigInt>) -> Option<BigInt> {
    match field_modulus {
        Some(modulus) => normalize_field_value(value, modulus),
        None => bounded_value(value),
    }
}

fn normalize_field_value(value: BigInt, modulus: &BigInt) -> Option<BigInt> {
    if modulus <= &BigInt::from(1) {
        return None;
    }

    let mut normalized = value % modulus;
    if normalized < BigInt::from(0) {
        normalized += modulus;
    }

    //Kis signed reprezentánst használunk: p-1 például -1-ként tárolható,
    //az analyzer SMT bridge később ezt újra visszanormalizálja field elemre.
    if normalized > modulus / BigInt::from(2) {
        normalized -= modulus;
    }

    bounded_value(normalized)
}

fn finite_domain_from_values<I>(values: I, field_modulus: Option<&BigInt>) -> Option<UcpValueDomain>
where
    I: IntoIterator<Item = BigInt>,
{
    let mut set = BTreeSet::new();

    for value in values {
        let value = normalize_value(value, field_modulus)?;
        if !set.contains(&value) && set.len() >= MAX_FINITE_DOMAIN_SIZE {
            return None;
        }
        set.insert(value);
    }

    UcpValueDomain::finite_set(set)
}

fn domain_values(domain: &UcpValueDomain) -> Vec<BigInt> {
    match domain {
        UcpValueDomain::Exact(value) => vec![value.clone()],
        UcpValueDomain::FiniteSet(values) => values.iter().cloned().collect(),
    }
}

fn map_domain_values<F>(
    domain: &UcpValueDomain,
    field_modulus: Option<&BigInt>,
    mut op: F,
) -> Option<UcpValueDomain>
where
    F: FnMut(BigInt) -> BigInt,
{
    finite_domain_from_values(
        domain_values(domain).into_iter().map(|value| op(value)),
        field_modulus,
    )
}

fn combine_domain_values<F>(
    left: &UcpValueDomain,
    right: &UcpValueDomain,
    field_modulus: Option<&BigInt>,
    mut op: F,
) -> Option<UcpValueDomain>
where
    F: FnMut(BigInt, BigInt) -> BigInt,
{
    let left_values = domain_values(left);
    let right_values = domain_values(right);

    if left_values.len().saturating_mul(right_values.len()) > MAX_FINITE_DOMAIN_SIZE {
        return None;
    }

    let mut values = Vec::with_capacity(left_values.len() * right_values.len());
    for left in &left_values {
        for right in &right_values {
            values.push(op(left.clone(), right.clone()));
        }
    }

    finite_domain_from_values(values, field_modulus)
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
    infer_value_domains_from_zero_equation_with_optional_modulus(expr, values, None)
}

//Nullára kényszerített expressionből modulus-aware Delta domain-eket tanul
pub fn infer_value_domains_from_zero_equation_with_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: &BigInt,
) -> Vec<(CellId, UcpValueDomain)> {
    infer_value_domains_from_zero_equation_with_optional_modulus(expr, values, Some(field_modulus))
}

fn infer_value_domains_from_zero_equation_with_optional_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Vec<(CellId, UcpValueDomain)> {
    let mut inferences = Vec::new();

    if let Some((cell, domain)) = infer_root_domain(expr, values) {
        push_domain_inference(&mut inferences, cell, domain);
    }

    if let Some((cell, value)) = infer_from_zero_expr(expr, values) {
        push_domain_inference(&mut inferences, cell, UcpValueDomain::exact(value));
    }

    for (cell, domain) in infer_linear_domains(expr, values, field_modulus) {
        push_domain_inference(&mut inferences, cell, domain);
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

//Expression-domain feltételből tanul cella-domain-eket: ha e egy lookup táblában van, Delta(e) a tábla domainje
pub fn infer_domains_from_expression_domain(
    expr: &UcpExpr,
    expr_domain: &UcpValueDomain,
    values: &UcpValueFacts,
) -> Vec<(CellId, UcpValueDomain)> {
    infer_domains_from_expression_domain_with_optional_modulus(expr, expr_domain, values, None)
}

//Ugyanez field modulussal, hogy c*x inverzét fieldben tudjuk venni
pub fn infer_domains_from_expression_domain_with_modulus(
    expr: &UcpExpr,
    expr_domain: &UcpValueDomain,
    values: &UcpValueFacts,
    field_modulus: &BigInt,
) -> Vec<(CellId, UcpValueDomain)> {
    infer_domains_from_expression_domain_with_optional_modulus(
        expr,
        expr_domain,
        values,
        Some(field_modulus),
    )
}

fn infer_domains_from_expression_domain_with_optional_modulus(
    expr: &UcpExpr,
    expr_domain: &UcpValueDomain,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Vec<(CellId, UcpValueDomain)> {
    let Some(linear) = linearize(expr, values) else {
        return Vec::new();
    };

    let mut inferences = Vec::new();

    for (cell, coefficient) in &linear.terms {
        if coefficient == &BigInt::from(0) {
            continue;
        }

        let Some(domain) = solve_linear_domain_for_cell_with_rhs(
            &linear,
            cell,
            coefficient,
            expr_domain,
            values,
            field_modulus,
        ) else {
            continue;
        };

        push_domain_inference(&mut inferences, cell.clone(), domain);
    }

    inferences
}

fn push_domain_inference(
    inferences: &mut Vec<(CellId, UcpValueDomain)>,
    cell: CellId,
    domain: UcpValueDomain,
) {
    if let Some((_, existing_domain)) = inferences
        .iter_mut()
        .find(|(existing_cell, _)| existing_cell == &cell)
    {
        if let Some(intersection) = existing_domain.intersect(&domain) {
            *existing_domain = intersection;
        }
    } else {
        inferences.push((cell, domain));
    }
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

//Lineáris null-egyenletből domain-t tanul, ha egy cellán kívül minden más tagnak véges Delta domainje van
fn infer_linear_domains(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Vec<(CellId, UcpValueDomain)> {
    let Some(linear) = linearize(expr, values) else {
        return Vec::new();
    };

    let mut inferences = Vec::new();

    for (cell, coefficient) in &linear.terms {
        if coefficient == &BigInt::from(0) {
            continue;
        }

        let Some(domain) =
            solve_linear_domain_for_cell(&linear, cell, coefficient, values, field_modulus)
        else {
            continue;
        };

        inferences.push((cell.clone(), domain));
    }

    inferences
}

fn solve_linear_domain_for_cell(
    linear: &LinearExpr,
    target: &CellId,
    coefficient: &BigInt,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Option<UcpValueDomain> {
    solve_linear_domain_for_cell_with_rhs(
        linear,
        target,
        coefficient,
        &UcpValueDomain::exact(BigInt::from(0)),
        values,
        field_modulus,
    )
}

fn solve_linear_domain_for_cell_with_rhs(
    linear: &LinearExpr,
    target: &CellId,
    coefficient: &BigInt,
    rhs_domain: &UcpValueDomain,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Option<UcpValueDomain> {
    let mut rest_values = vec![normalize_value(linear.constant.clone(), field_modulus)?];

    for (cell, term_coefficient) in &linear.terms {
        if cell == target {
            continue;
        }

        let domain = values.domain(cell)?;
        let term_values = domain_values(domain);

        if rest_values.len().saturating_mul(term_values.len()) > MAX_FINITE_DOMAIN_SIZE {
            return None;
        }

        let mut next_values = Vec::with_capacity(rest_values.len() * term_values.len());
        for rest in &rest_values {
            for value in &term_values {
                next_values.push(normalize_value(
                    rest + term_coefficient * value,
                    field_modulus,
                )?);
            }
        }
        rest_values = next_values;
    }

    let rhs_values = domain_values(rhs_domain);
    if rhs_values.len().saturating_mul(rest_values.len()) > MAX_FINITE_DOMAIN_SIZE {
        return None;
    }

    let mut solved_values = Vec::with_capacity(rhs_values.len() * rest_values.len());
    for rhs in &rhs_values {
        for rest in &rest_values {
            solved_values.push(solve_linear_value(
                &(rhs - rest),
                coefficient,
                field_modulus,
            )?);
        }
    }

    finite_domain_from_values(solved_values, field_modulus)
}

fn solve_linear_value(
    numerator: &BigInt,
    coefficient: &BigInt,
    field_modulus: Option<&BigInt>,
) -> Option<BigInt> {
    match field_modulus {
        Some(modulus) => {
            let inverse = mod_inverse(coefficient, modulus)?;
            normalize_value(numerator * inverse, Some(modulus))
        }
        None => {
            if numerator % coefficient != BigInt::from(0) {
                return None;
            }
            bounded_value(numerator / coefficient)
        }
    }
}

fn mod_inverse(value: &BigInt, modulus: &BigInt) -> Option<BigInt> {
    let mut t = BigInt::from(0);
    let mut new_t = BigInt::from(1);
    let mut r = modulus.clone();
    let mut new_r = mod_field(value.clone(), modulus);

    while new_r != BigInt::from(0) {
        let quotient = &r / &new_r;

        let old_t = t;
        t = new_t.clone();
        new_t = old_t - &quotient * &new_t;

        let old_r = r;
        r = new_r.clone();
        new_r = old_r - quotient * new_r;
    }

    if r != BigInt::from(1) {
        return None;
    }

    Some(mod_field(t, modulus))
}

fn mod_field(value: BigInt, modulus: &BigInt) -> BigInt {
    let mut value = value % modulus;
    if value < BigInt::from(0) {
        value += modulus;
    }
    value
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

    //Azt ellenőrzi, hogy a Fig. 9 szerinti expression-domain szabályok működnek finite domainekkel
    #[test]
    fn expression_domain_combines_finite_sets() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let mut values = UcpValueFacts::new();
        values.mark_domain(x.clone(), finite_domain(&[0, 1]));
        values.mark_domain(y.clone(), finite_domain(&[2, 3]));

        let sum = UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::var(y.clone()));
        let product = UcpExpr::mul(UcpExpr::var(x), UcpExpr::var(y));

        assert_eq!(
            expression_domain(&sum, &values),
            Some(finite_domain(&[2, 3, 4]))
        );
        assert_eq!(
            expression_domain(&product, &values),
            Some(finite_domain(&[0, 2, 3]))
        );
    }

    //Azt ellenőrzi, hogy x - (b + 1) = 0 alapján Delta(b)={0,1} esetén Delta(x)={1,2}
    #[test]
    fn linear_equation_learns_domain_from_expression_domain() {
        let b = CellId::advice(0, 0);
        let x = CellId::advice(1, 0);
        let mut values = UcpValueFacts::new();
        values.mark_domain(b.clone(), finite_domain(&[0, 1]));

        let expr = UcpExpr::add(
            UcpExpr::var(x.clone()),
            UcpExpr::neg(UcpExpr::add(
                UcpExpr::var(b),
                UcpExpr::known_constant_i64(1),
            )),
        );

        let inferences = infer_value_domains_from_zero_equation(&expr, &values);

        assert_eq!(inferences, vec![(x, finite_domain(&[1, 2]))]);
    }

    //Azt ellenőrzi, hogy c*x - e = 0 esetén modulus mellett c inverzével számolunk
    #[test]
    fn scaled_linear_equation_uses_field_modulus_for_domain_division() {
        let b = CellId::advice(0, 0);
        let x = CellId::advice(1, 0);
        let mut values = UcpValueFacts::new();
        values.mark_domain(b.clone(), finite_domain(&[0, 2]));

        let expr = UcpExpr::add(
            UcpExpr::scale_by(UcpExpr::var(x.clone()), UcpScalar::known_i64(2)),
            UcpExpr::neg(UcpExpr::var(b)),
        );

        let inferences =
            infer_value_domains_from_zero_equation_with_modulus(&expr, &values, &BigInt::from(5));

        assert_eq!(inferences, vec![(x, finite_domain(&[0, 1]))]);
    }

    //Azt ellenőrzi, hogy lookup-szerű e in Omega feltételből is tudunk cella-domaint tanulni
    #[test]
    fn expression_membership_learns_affine_input_domain() {
        let x = CellId::advice(0, 0);
        let expr = UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(1));
        let table_domain = finite_domain(&[1, 2, 3]);

        let inferences =
            infer_domains_from_expression_domain(&expr, &table_domain, &UcpValueFacts::new());

        assert_eq!(inferences, vec![(x, finite_domain(&[0, 1, 2]))]);
    }
}
