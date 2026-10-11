use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

pub(crate) const MAX_FINITE_DOMAIN_SIZE: usize = 256;
/// Covers the supported Halo2 fields while keeping stored integers explicitly bounded.
pub const MAX_VALUE_BITS: u64 = 4096;
const MAX_LINEAR_SYSTEM_CELLS: usize = 64;
const MAX_LINEAR_SYSTEM_EQUATIONS: usize = 256;

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
            if set.len() > MAX_FINITE_DOMAIN_SIZE {
                return None;
            }
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
pub fn initial_values_from_instance_cells<'a, I, V>(instance_cells: I) -> UcpValueFacts
where
    I: IntoIterator<Item = (&'a String, &'a V)>,
    V: Clone + Into<BigInt> + 'a,
{
    let mut values = UcpValueFacts::new();

    for (name, value) in instance_cells {
        if let Some(cell) = parse_cell_id(name) {
            values.mark_known(cell, value.clone().into());
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

//Fig. 9 Var/Const/Op: expression véges Delta domainjét számolja modulus nélkül
pub fn expression_domain(expr: &UcpExpr, values: &UcpValueFacts) -> Option<UcpValueDomain> {
    expression_domain_with_optional_modulus(expr, values, None)
}

//Fig. 9 Var/Const/Op: expression véges Delta domainjét számolja a field modulus szerint
pub fn expression_domain_with_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: &BigInt,
) -> Option<UcpValueDomain> {
    expression_domain_with_optional_modulus(expr, values, Some(field_modulus))
}

//Fig. 9 közös motor: Var, Const és Op szabályok finite-setes kiértékelése
fn expression_domain_with_optional_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Option<UcpValueDomain> {
    match expr {
        UcpExpr::Var(cell) => {
            let domain = values.domain(cell)?;
            match field_modulus {
                Some(_) => finite_domain_from_values(domain_values(domain), field_modulus),
                None => Some(domain.clone()),
            }
        }
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

//Bound stored integers, not machine words: field elements can exceed i64.
pub(crate) fn bounded_value(value: BigInt) -> Option<BigInt> {
    if value.bits() <= MAX_VALUE_BITS {
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

pub(crate) fn normalize_field_value(value: BigInt, modulus: &BigInt) -> Option<BigInt> {
    if modulus <= &BigInt::from(1) || modulus.bits() > MAX_VALUE_BITS {
        return None;
    }

    let mut normalized = value % modulus;
    if normalized < BigInt::from(0) {
        normalized += modulus;
    }

    //Signed reprezentánst használunk: p-1 például -1-ként tárolható,
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

//A domainből BigInt vektort csinál
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
    value_kind_with_optional_modulus(expr, values, None)
}

fn value_kind_with_optional_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    modulus: Option<&BigInt>,
) -> ValueKind {
    if modulus.is_some_and(|modulus| modulus <= &BigInt::from(1)) {
        return ValueKind::Unknown;
    }
    if let Some(domain) = expression_domain_with_optional_modulus(expr, values, modulus) {
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
                let inner_kind = value_kind_with_optional_modulus(inner, values, modulus);
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
            UcpExpr::Neg(inner) => value_kind_with_optional_modulus(inner, values, modulus),
            UcpExpr::Mul(left, right) => {
                match (
                    value_kind_with_optional_modulus(left, values, modulus),
                    value_kind_with_optional_modulus(right, values, modulus),
                ) {
                    (ValueKind::Zero, _) | (_, ValueKind::Zero) => ValueKind::Zero,
                    (ValueKind::NonZero, ValueKind::NonZero) => ValueKind::NonZero,
                    _ => ValueKind::Unknown,
                }
            }
            _ => ValueKind::Unknown,
        }
    }
}

//Fig. 10 dispatcher: null-egyenletből új Delta domain-eket tanul modulus nélkül
pub fn infer_value_domains_from_zero_equation(
    expr: &UcpExpr,
    values: &UcpValueFacts,
) -> Vec<(CellId, UcpValueDomain)> {
    infer_value_domains_from_zero_equation_with_optional_modulus(expr, values, None)
}

//Fig. 10 dispatcher: null-egyenletből modulus-aware Delta domain-eket tanul
pub fn infer_value_domains_from_zero_equation_with_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: &BigInt,
) -> Vec<(CellId, UcpValueDomain)> {
    infer_value_domains_from_zero_equation_with_optional_modulus(expr, values, Some(field_modulus))
}

//Fig. 10 közös hívási pont: Root, Assign, általános lineáris domain és Base-Conv futtatása
fn infer_value_domains_from_zero_equation_with_optional_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Vec<(CellId, UcpValueDomain)> {
    let mut inferences = Vec::new();

    //Fig. 10 Root: szorzatgyökökből finite domain tanulása
    if let Some((root_expr, domain)) = infer_root_expression_domain(expr, values, field_modulus) {
        for (cell, domain) in infer_domains_from_expression_domain_with_optional_modulus(
            root_expr,
            &domain,
            values,
            field_modulus,
        ) {
            push_domain_inference(&mut inferences, cell, domain);
        }
    }

    //Fig. 10 Assign: c*x-e=0 alakból konkrét érték tanulása, ha e konkrét
    if let Some((cell, value)) = infer_from_zero_expr(expr, values, field_modulus) {
        push_domain_inference(&mut inferences, cell, UcpValueDomain::exact(value));
    }

    //Fig. 10 Assign domain verzió: c*x-e=0 alakból finite domain tanulása, ha Delta(e) véges
    for (cell, domain) in infer_linear_domains(expr, values, field_modulus) {
        push_domain_inference(&mut inferences, cell, domain);
    }

    //Fig. 10 Base-Conv: c-alapú digitfelbontásból target-domain tanulása
    for (cell, domain) in infer_base_conv_value_domains(expr, values, field_modulus) {
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

//Konstans egyutthatos rendszereket old meg Delta szamara, akkor is, ha a cellak mar K-ban vannak.
pub fn infer_linear_system_values_with_modulus(
    expressions: &[UcpExpr],
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> Vec<(CellId, BigInt)> {
    if modulus <= &BigInt::from(1) {
        return Vec::new();
    }

    let mut equations = Vec::new();
    let mut equations_by_cell: BTreeMap<CellId, Vec<usize>> = BTreeMap::new();
    for expr in expressions {
        let Some(mut linear) = linearize_field_system(expr, values) else {
            continue;
        };
        linear.constant = mod_field(linear.constant, modulus);
        for coefficient in linear.terms.values_mut() {
            *coefficient = mod_field(coefficient.clone(), modulus);
        }
        linear
            .terms
            .retain(|_, coefficient| coefficient != &BigInt::from(0));
        if linear.terms.is_empty() {
            if linear.constant != BigInt::from(0) {
                return Vec::new();
            }
            continue;
        }
        let index = equations.len();
        for cell in linear.terms.keys() {
            equations_by_cell
                .entry(cell.clone())
                .or_default()
                .push(index);
        }
        equations.push(linear);
    }

    // A small full-rank subsystem can fix cells even if its larger component has free cells.
    let mut groups: BTreeMap<Vec<CellId>, Vec<usize>> = BTreeMap::new();
    for (index, equation) in equations
        .iter()
        .enumerate()
        .take(MAX_LINEAR_SYSTEM_EQUATIONS)
    {
        if !(2..=MAX_LINEAR_SYSTEM_CELLS).contains(&equation.terms.len()) {
            continue;
        }
        let mut cells: Vec<_> = equation.terms.keys().cloned().collect();
        cells.sort();
        groups.entry(cells).or_default().push(index);
    }
    let mut inferences = BTreeMap::new();
    for (cells, indices) in groups {
        if indices.len() >= cells.len() && indices.len() <= MAX_LINEAR_SYSTEM_EQUATIONS {
            inferences.extend(solve_linear_subsystem(
                &equations, &indices, &cells, values, modulus,
            ));
        }
    }
    //Fuggetlen komponenseket kulon oldunk meg; nagy rendszernel megmarad az SMT fallback.
    let mut visited = HashSet::new();
    for start in equations_by_cell.keys() {
        if !visited.insert(start.clone()) {
            continue;
        }
        let mut queue = VecDeque::from([start.clone()]);
        let mut cells = BTreeSet::new();
        let mut indices = BTreeSet::new();
        while let Some(cell) = queue.pop_front() {
            cells.insert(cell.clone());
            for index in &equations_by_cell[&cell] {
                if indices.insert(*index) {
                    for next in equations[*index].terms.keys() {
                        if visited.insert(next.clone()) {
                            queue.push_back(next.clone());
                        }
                    }
                }
            }
        }
        if cells.len() > MAX_LINEAR_SYSTEM_CELLS
            || indices.len() > MAX_LINEAR_SYSTEM_EQUATIONS
            || indices.len() < cells.len()
        {
            continue;
        }

        let cells: Vec<_> = cells.into_iter().collect();
        inferences.extend(solve_linear_subsystem(
            &equations,
            &indices.into_iter().collect::<Vec<_>>(),
            &cells,
            values,
            modulus,
        ));
    }
    inferences.into_iter().collect()
}

fn solve_linear_subsystem(
    equations: &[LinearExpr],
    indices: &[usize],
    cells: &[CellId],
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> Vec<(CellId, BigInt)> {
    let matrix = indices
        .iter()
        .map(|index| {
            let equation = &equations[*index];
            let mut row: Vec<_> = cells
                .iter()
                .map(|cell| {
                    equation
                        .terms
                        .get(cell)
                        .cloned()
                        .unwrap_or_else(|| BigInt::from(0))
                })
                .collect();
            row.push(mod_field(-equation.constant.clone(), modulus));
            row
        })
        .collect();
    let Some(solution) = solve_field_system(matrix, cells.len(), modulus) else {
        return Vec::new();
    };
    //A megoldasnak az eddig bizonyitott domainekkel is osszeferhetonek kell lennie.
    if cells.iter().zip(&solution).any(|(cell, value)| {
        values.domain(cell).is_some_and(|domain| {
            !domain_values(domain)
                .iter()
                .any(|candidate| mod_field(candidate.clone(), modulus) == *value)
        })
    }) {
        return Vec::new();
    }
    cells
        .iter()
        .cloned()
        .zip(solution)
        .filter_map(|(cell, value)| {
            normalize_field_value(value, modulus).map(|value| (cell, value))
        })
        .collect()
}

fn solve_field_system(
    mut matrix: Vec<Vec<BigInt>>,
    columns: usize,
    modulus: &BigInt,
) -> Option<Vec<BigInt>> {
    //A bovitetett matrixon a jobb oldalt is ugyanazokkal a sormuveletekkel alakitjuk.
    for column in 0..columns {
        let pivot = (column..matrix.len()).find(|row| matrix[*row][column] != BigInt::from(0))?;
        matrix.swap(column, pivot);
        let inverse = mod_inverse(&matrix[column][column], modulus)?;
        for entry in &mut matrix[column][column..=columns] {
            *entry = mod_field(entry.clone() * &inverse, modulus);
        }
        for row in 0..matrix.len() {
            if row == column || matrix[row][column] == BigInt::from(0) {
                continue;
            }
            let factor = matrix[row][column].clone();
            for col in column..=columns {
                matrix[row][col] = mod_field(
                    matrix[row][col].clone() - &factor * &matrix[column][col],
                    modulus,
                );
            }
        }
    }
    if matrix[columns..]
        .iter()
        .any(|row| row[columns] != BigInt::from(0))
    {
        return None;
    }
    Some(
        (0..columns)
            .map(|column| matrix[column][columns].clone())
            .collect(),
    )
}

fn linearize_field_system(expr: &UcpExpr, values: &UcpValueFacts) -> Option<LinearExpr> {
    //A koefficiensek teljes field elemek lehetnek; csak a vegso Delta erteket korlatozzuk.
    match expr {
        UcpExpr::Var(cell) => Some(match values.known_value(cell) {
            Some(value) => LinearExpr::constant(value.clone()),
            None => LinearExpr::term(cell.clone(), BigInt::from(1)),
        }),
        UcpExpr::Const(scalar) => Some(LinearExpr::constant(scalar.as_known()?)),
        UcpExpr::Neg(inner) => Some(linearize_field_system(inner, values)?.scale(BigInt::from(-1))),
        UcpExpr::Add(left, right) => {
            Some(linearize_field_system(left, values)?.add(linearize_field_system(right, values)?))
        }
        UcpExpr::Mul(left, right) => {
            let left = linearize_field_system(left, values)?;
            let right = linearize_field_system(right, values)?;
            if left.terms.is_empty() {
                Some(right.scale(left.constant))
            } else if right.terms.is_empty() {
                Some(left.scale(right.constant))
            } else {
                None
            }
        }
        UcpExpr::Scale(_, UcpScalar::Zero) => Some(LinearExpr::constant(BigInt::from(0))),
        UcpExpr::Scale(inner, scalar) => {
            Some(linearize_field_system(inner, values)?.scale(scalar.as_known()?))
        }
    }
}

//Fig. 9/lookup bridge: külső Omega domainből lineáris expression bemeneti celladomaineket tanul
pub fn infer_domains_from_expression_domain(
    expr: &UcpExpr,
    expr_domain: &UcpValueDomain,
    values: &UcpValueFacts,
) -> Vec<(CellId, UcpValueDomain)> {
    infer_domains_from_expression_domain_with_optional_modulus(expr, expr_domain, values, None)
}

//Fig. 9/lookup bridge modulusosan: c*x inverzét fieldben tudjuk venni
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

//Fig. 10 Root on an affine expression: product(e - c_i) = 0 implies e in {c_i}.
fn infer_root_expression_domain<'a>(
    expr: &'a UcpExpr,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Option<(&'a UcpExpr, UcpValueDomain)> {
    let mut factors = Vec::new();
    collect_product_factors(expr, &mut factors, field_modulus);

    if factors.len() < 2 {
        return None;
    }

    let first = *factors.first()?;
    let common = linearize(first, values)?;
    if common.terms.is_empty() {
        return None;
    }
    let mut roots = Vec::new();

    for factor in factors {
        let linear = linearize(factor, values)?;
        //Allow both e-c and c-e, as used by the upstream polynomial range gadget.
        if linear.terms == common.terms {
            roots.push(&common.constant - linear.constant);
        } else if linear.terms.len() == common.terms.len()
            && linear.terms.iter().all(|(cell, coefficient)| {
                common
                    .terms
                    .get(cell)
                    .is_some_and(|other| coefficient == &-other)
            })
        {
            roots.push(&common.constant + linear.constant);
        } else {
            return None;
        }
    }

    Some((first, finite_domain_from_values(roots, field_modulus)?))
}

//Szorzatot faktorokra bont, hogy a root szabály felismerhető legyen
//Például: [x,x-1,x-2]
fn collect_product_factors<'a>(
    expr: &'a UcpExpr,
    factors: &mut Vec<&'a UcpExpr>,
    modulus: Option<&BigInt>,
) {
    match expr {
        UcpExpr::Mul(left, right) => {
            collect_product_factors(left, factors, modulus);
            collect_product_factors(right, factors, modulus);
        }
        UcpExpr::Neg(inner) => collect_product_factors(inner, factors, modulus),
        UcpExpr::Scale(_, UcpScalar::Known(scale)) if scale == &BigInt::from(0) => {
            factors.push(expr)
        }
        UcpExpr::Scale(inner, scalar) if scalar.is_non_zero_with_modulus(modulus) => {
            collect_product_factors(inner, factors, modulus)
        }
        //A zero factor makes the equation tautological; retain it so Root rejects the product.
        UcpExpr::Scale(_, UcpScalar::Zero) => factors.push(expr),
        _ => factors.push(expr),
    }
}

//Fig. 10 Assign előszűrő: nemnulla szorzótényezők mellett konkrét cellaértéket tanul
fn infer_from_zero_expr(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    modulus: Option<&BigInt>,
) -> Option<(CellId, BigInt)> {
    match expr {
        UcpExpr::Scale(_, UcpScalar::Known(scale)) if scale == &BigInt::from(0) => None,
        UcpExpr::Mul(left, right) => match (
            value_kind_with_optional_modulus(left, values, modulus),
            value_kind_with_optional_modulus(right, values, modulus),
        ) {
            (ValueKind::NonZero, _) => infer_from_zero_expr(right, values, modulus),
            (_, ValueKind::NonZero) => infer_from_zero_expr(left, values, modulus),
            (ValueKind::Zero, _) | (_, ValueKind::Zero) => None,
            _ => infer_linear_assignment(expr, values, modulus),
        },
        UcpExpr::Scale(inner, scalar) if scalar.is_non_zero_with_modulus(modulus) => {
            infer_from_zero_expr(inner, values, modulus)
        }
        UcpExpr::Scale(_, UcpScalar::Zero) => None,
        _ => infer_linear_assignment(expr, values, modulus),
    }
}

//Fig. 10 Assign konkrét verzió: lineáris null-egyenletet old meg egy ismeretlen cellára
fn infer_linear_assignment(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    modulus: Option<&BigInt>,
) -> Option<(CellId, BigInt)> {
    let linear = linearize(expr, values)?;

    if linear.terms.len() != 1 {
        return None;
    }

    let (cell, coefficient) = linear.terms.into_iter().next().unwrap();
    if coefficient == BigInt::from(0) {
        return None;
    }

    let numerator = -linear.constant;
    Some((cell, solve_linear_value(&numerator, &coefficient, modulus)?))
}

//Fig. 10 Assign domain verzió: lineáris null-egyenletből finite domaint tanul célcellákra
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

//Fig. 10 Base-Conv value rule: y0 + c*y1 + ... + c^n*yn - x = 0 esetén
//ha minden yi domainje [0, c-1]-ben van, akkor x domainje [0, c^(n+1)-1].
//Intervallum domainünk nincs, ezért csak akkor tanulunk, ha ez explicit finite setként kicsi marad.
fn infer_base_conv_value_domains(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Vec<(CellId, UcpValueDomain)> {
    let Some(linear) = linearize(expr, values) else {
        return Vec::new();
    };

    if linear.constant != BigInt::from(0) {
        return Vec::new();
    }

    let mut inferences = Vec::new();

    for (target, target_coefficient) in &linear.terms {
        if !is_plus_or_minus_one(target_coefficient) {
            continue;
        }

        let Some(domain) = infer_base_conv_value_domain_for_target(
            &linear,
            target,
            target_coefficient,
            values,
            field_modulus,
        ) else {
            continue;
        };

        push_domain_inference(&mut inferences, target.clone(), domain);
    }

    inferences
}

//Fig. 10 Base-Conv konkrét targetre: felismeri az 1,c,c^2,... coefficient mintát
fn infer_base_conv_value_domain_for_target(
    linear: &LinearExpr,
    target: &CellId,
    target_coefficient: &BigInt,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Option<UcpValueDomain> {
    let mut digits_with_coefficients = Vec::new();

    for (cell, coefficient) in &linear.terms {
        if cell == target {
            continue;
        }

        let digit_coefficient = -coefficient * target_coefficient;
        if digit_coefficient <= BigInt::from(0) {
            return None;
        }

        digits_with_coefficients.push((cell.clone(), digit_coefficient));
    }

    let (base, digits) = parse_base_conv_digit_powers(digits_with_coefficients)?;
    let max_digit = &base - BigInt::from(1);

    if digits
        .iter()
        .any(|digit| !values.domain_is_subset_of_range(digit, &BigInt::from(0), &max_digit))
    {
        return None;
    }

    let domain_size = pow_bigint(&base, digits.len());
    if domain_size <= BigInt::from(0) || domain_size > BigInt::from(MAX_FINITE_DOMAIN_SIZE as i64) {
        return None;
    }

    let mut domain_values = Vec::new();
    let mut value = BigInt::from(0);
    while value < domain_size {
        domain_values.push(value.clone());
        value += 1;
    }

    finite_domain_from_values(domain_values, field_modulus)
}

//Fig. 10 Base-Conv segéd: ellenőrzi, hogy a coefficientek pontosan c hatványai
fn parse_base_conv_digit_powers(
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

fn pow_bigint(base: &BigInt, exponent: usize) -> BigInt {
    let mut result = BigInt::from(1);
    for _ in 0..exponent {
        result *= base;
    }
    result
}

fn is_plus_or_minus_one(value: &BigInt) -> bool {
    value == &BigInt::from(1) || value == &BigInt::from(-1)
}

//Fig. 10 Assign segéd: target cella domainjét oldja meg nulla jobb oldal mellett
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

//Fig. 10 Assign/lookup segéd: target cella domainjét oldja meg tetszőleges véges jobb oldal mellett
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
            if modulus <= &BigInt::from(1) {
                return None;
            }
            let inverse = mod_inverse(coefficient, modulus)?;
            normalize_value(numerator * inverse, Some(modulus))
        }
        None => {
            if coefficient == &BigInt::from(0) {
                return None;
            }
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
pub(crate) fn parse_cell_id(name: &str) -> Option<CellId> {
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

    fn coupled_equations(x: &CellId, y: &CellId, sum: i64, difference: i64) -> Vec<UcpExpr> {
        vec![
            UcpExpr::add(
                UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::var(y.clone())),
                UcpExpr::known_constant_i64(-sum),
            ),
            UcpExpr::add(
                UcpExpr::add(
                    UcpExpr::var(x.clone()),
                    UcpExpr::neg(UcpExpr::var(y.clone())),
                ),
                UcpExpr::known_constant_i64(-difference),
            ),
        ]
    }

    //Az egyenkenti Assign elakadna, de a ket egyenlet egyutt x=6,y=4-et ad.
    #[test]
    fn solves_coupled_linear_values() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        assert_eq!(
            infer_linear_system_values_with_modulus(
                &coupled_equations(&x, &y, 10, 2),
                &UcpValueFacts::new(),
                &BigInt::from(101),
            ),
            vec![(x, BigInt::from(6)), (y, BigInt::from(4))],
        );
    }

    //Nem valasztunk tetszoleges modellt, ha a rang hianyos vagy az extra sor ellentmond.
    #[test]
    fn rejects_singular_and_inconsistent_linear_systems() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let mut equations = coupled_equations(&x, &y, 10, 2);
        assert!(infer_linear_system_values_with_modulus(
            &equations[..1],
            &UcpValueFacts::new(),
            &BigInt::from(101),
        )
        .is_empty());
        let singular = vec![equations[0].clone(), equations[0].clone()];
        assert!(infer_linear_system_values_with_modulus(
            &singular,
            &UcpValueFacts::new(),
            &BigInt::from(101),
        )
        .is_empty());
        equations.push(coupled_equations(&x, &y, 11, 2).remove(0));
        assert!(infer_linear_system_values_with_modulus(
            &equations,
            &UcpValueFacts::new(),
            &BigInt::from(101),
        )
        .is_empty());
    }

    //A p-1 koefficiens -1-et jelent akkor is, ha a pozitiv reprezentans nem fer i64-be.
    #[test]
    fn solves_with_large_field_coefficients() {
        let modulus = (BigInt::from(1) << 127usize) - BigInt::from(1);
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let mut equations = coupled_equations(&x, &y, 5, 1);
        equations[1] = UcpExpr::add(
            UcpExpr::add(
                UcpExpr::var(x.clone()),
                UcpExpr::scale_by(UcpExpr::var(y.clone()), UcpScalar::known(&modulus - 1)),
            ),
            UcpExpr::known_constant_i64(-1),
        );
        assert_eq!(
            infer_linear_system_values_with_modulus(&equations, &UcpValueFacts::new(), &modulus,),
            vec![(x, BigInt::from(3)), (y, BigInt::from(2))]
        );
    }

    #[test]
    fn does_not_learn_values_outside_existing_domains() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let mut values = UcpValueFacts::new();
        values.mark_domain(x.clone(), finite_domain(&[0, 1]));
        assert!(infer_linear_system_values_with_modulus(
            &coupled_equations(&x, &y, 10, 2),
            &values,
            &BigInt::from(101),
        )
        .is_empty());
    }

    //A nagy komponens koltsegkorlatja nem akadalyozza a fuggetlen kis rendszer megoldasat.
    #[test]
    fn limits_large_components_but_solves_small_independent_ones() {
        let count = MAX_LINEAR_SYSTEM_CELLS + 1;
        let mut equations: Vec<_> = (0..count)
            .map(|index| {
                UcpExpr::add(
                    UcpExpr::add(
                        UcpExpr::var(CellId::advice(index, 0)),
                        UcpExpr::var(CellId::advice((index + 1) % count, 0)),
                    ),
                    UcpExpr::known_constant_i64(-2),
                )
            })
            .collect();
        let x = CellId::advice(count, 0);
        let y = CellId::advice(count + 1, 0);
        equations.extend(coupled_equations(&x, &y, 10, 2));
        assert_eq!(
            infer_linear_system_values_with_modulus(
                &equations,
                &UcpValueFacts::new(),
                &BigInt::from(101),
            ),
            vec![(x, BigInt::from(6)), (y, BigInt::from(4))]
        );
    }

    #[test]
    fn solves_a_full_rank_subsystem_inside_an_underdetermined_component() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let mut equations = coupled_equations(&x, &y, 10, 2);
        // x+y=10 and x-y=2 fix x,y; adding x+z+w=0 leaves z,w ambiguous.
        equations.push(UcpExpr::add(
            UcpExpr::var(x.clone()),
            UcpExpr::add(
                UcpExpr::var(CellId::advice(2, 0)),
                UcpExpr::var(CellId::advice(3, 0)),
            ),
        ));
        assert_eq!(
            infer_linear_system_values_with_modulus(
                &equations,
                &UcpValueFacts::new(),
                &BigInt::from(101)
            ),
            vec![(x, BigInt::from(6)), (y, BigInt::from(4))]
        );
    }

    #[test]
    fn small_subsystem_survives_the_connected_component_size_limit() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let mut equations = coupled_equations(&x, &y, 10, 2);
        for index in 2..MAX_LINEAR_SYSTEM_CELLS + 3 {
            equations.push(UcpExpr::add(
                UcpExpr::var(x.clone()),
                UcpExpr::add(
                    UcpExpr::var(CellId::advice(index, 0)),
                    UcpExpr::var(CellId::advice(index + 1, 0)),
                ),
            ));
        }
        assert_eq!(
            infer_linear_system_values_with_modulus(
                &equations,
                &UcpValueFacts::new(),
                &BigInt::from(101)
            ),
            vec![(x, BigInt::from(6)), (y, BigInt::from(4))]
        );
    }

    #[test]
    fn local_subsystem_search_respects_the_equation_budget() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let mut equations: Vec<_> = (2..MAX_LINEAR_SYSTEM_EQUATIONS + 2)
            .map(|index| {
                UcpExpr::add(
                    UcpExpr::var(x.clone()),
                    UcpExpr::add(
                        UcpExpr::var(CellId::advice(index, 0)),
                        UcpExpr::var(CellId::advice(index + 1, 0)),
                    ),
                )
            })
            .collect();
        // The useful pair is beyond the local search budget; the full component is oversized.
        equations.extend(coupled_equations(&x, &y, 10, 2));
        assert!(infer_linear_system_values_with_modulus(
            &equations,
            &UcpValueFacts::new(),
            &BigInt::from(101),
        )
        .is_empty());
    }

    #[test]
    fn subsystem_values_cover_all_satisfying_assignments_in_small_prime_fields() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let z = CellId::advice(2, 0);
        let w = CellId::advice(3, 0);
        for p in [3, 5, 7] {
            for sum in 0..p {
                for difference in 0..p {
                    let mut equations = coupled_equations(&x, &y, sum, difference);
                    equations.push(UcpExpr::add(
                        UcpExpr::var(x.clone()),
                        UcpExpr::add(UcpExpr::var(z.clone()), UcpExpr::var(w.clone())),
                    ));
                    let inferred = infer_linear_system_values_with_modulus(
                        &equations,
                        &UcpValueFacts::new(),
                        &BigInt::from(p),
                    );
                    assert_eq!(inferred.len(), 2);
                    for a in 0..p {
                        for b in 0..p {
                            for c in 0..p {
                                for d in 0..p {
                                    if (a + b) % p != sum
                                        || (a - b + p) % p != difference
                                        || (a + c + d) % p != 0
                                    {
                                        continue;
                                    }
                                    for (cell, value) in &inferred {
                                        let actual = if cell == &x {
                                            a
                                        } else {
                                            assert_eq!(cell, &y);
                                            b
                                        };
                                        assert_eq!(
                                            mod_field(value.clone(), &BigInt::from(p)),
                                            BigInt::from(actual)
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    //Both large and small coordinates survive: an i64 bound must not drop a field solution.
    #[test]
    fn solves_values_beyond_i64_alongside_small_signed_solutions() {
        let modulus = (BigInt::from(1) << 127usize) - BigInt::from(1);
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let large = BigInt::from(i64::MAX) + BigInt::from(1);
        let equations = vec![
            UcpExpr::add(
                UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::var(y.clone())),
                UcpExpr::known_constant(-&large),
            ),
            UcpExpr::add(
                UcpExpr::add(
                    UcpExpr::var(x.clone()),
                    UcpExpr::neg(UcpExpr::var(y.clone())),
                ),
                UcpExpr::known_constant(-(&large + BigInt::from(2))),
            ),
        ];
        assert_eq!(
            infer_linear_system_values_with_modulus(&equations, &UcpValueFacts::new(), &modulus,),
            vec![(x, large + BigInt::from(1)), (y, BigInt::from(-1))]
        );
    }

    #[test]
    fn value_bit_and_domain_limits_abort_without_retaining_a_truncated_set() {
        let largest = (BigInt::from(1) << MAX_VALUE_BITS as usize) - BigInt::from(1);
        let oversized = &largest + BigInt::from(1);
        assert_eq!(bounded_value(largest.clone()), Some(largest));
        assert!(bounded_value(oversized.clone()).is_none());
        assert!(UcpValueDomain::finite_set([BigInt::from(1), oversized.clone()]).is_none());
        assert!(
            UcpValueDomain::finite_set((0..=MAX_FINITE_DOMAIN_SIZE).map(BigInt::from)).is_none()
        );
        assert!(UcpValueDomain::finite_set(std::iter::repeat_n(
            BigInt::from(1),
            MAX_FINITE_DOMAIN_SIZE + 1
        ))
        .is_some());
        let cell = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();
        assert!(!values.mark_known(cell.clone(), oversized));
        assert!(values.domain(&cell).is_none());
    }

    #[test]
    fn large_root_domain_preserves_holes_and_refines_to_an_exact_value() {
        let x = CellId::advice(0, 0);
        let root = BigInt::from(1) << 200usize;
        let modulus = (BigInt::from(1) << 521usize) - BigInt::from(1);
        // (x - 2^200) * (x - (2^200 + 2)) = 0 permits two roots, not their midpoint.
        let expression = UcpExpr::mul(
            UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant(-&root)),
            UcpExpr::add(
                UcpExpr::var(x.clone()),
                UcpExpr::known_constant(-(&root + BigInt::from(2))),
            ),
        );
        let mut values = UcpValueFacts::new();
        let domain = UcpValueDomain::finite_set([root.clone(), &root + 2]).unwrap();
        assert_eq!(
            infer_value_domains_from_zero_equation_with_modulus(&expression, &values, &modulus),
            vec![(x.clone(), domain.clone())]
        );
        assert!(values.mark_domain(x.clone(), domain));
        assert!(values.mark_domain(
            x.clone(),
            UcpValueDomain::finite_set([&root + 2, &root + 3]).unwrap()
        ));
        assert_eq!(values.known_value(&x), Some(&(&root + 2)));
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

    #[test]
    fn root_rule_handles_opposite_sign_factors() {
        //The library uses b*(1-b), rather than b*(b-1).
        let b = CellId::advice(0, 0);
        let expr = UcpExpr::mul(
            UcpExpr::var(b.clone()),
            UcpExpr::add(
                UcpExpr::known_constant_i64(1),
                UcpExpr::neg(UcpExpr::var(b.clone())),
            ),
        );
        assert_eq!(
            infer_value_domains_from_zero_equation(&expr, &UcpValueFacts::new()),
            vec![(b, finite_domain(&[0, 1]))]
        );
    }

    #[test]
    fn affine_root_projection_covers_every_small_field_solution() {
        //A shifted first factor and reversed-sign second factor test the shared-expression identity.
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let word = UcpExpr::add(
            UcpExpr::var(x.clone()),
            UcpExpr::scale_by(UcpExpr::var(y.clone()), UcpScalar::known_i64(-4)),
        );
        let expr = UcpExpr::mul(
            UcpExpr::add(word.clone(), UcpExpr::known_constant_i64(-3)),
            UcpExpr::mul(
                UcpExpr::add(UcpExpr::known_constant_i64(7), UcpExpr::neg(word.clone())),
                UcpExpr::add(word, UcpExpr::known_constant_i64(1)),
            ),
        );
        let mut values = UcpValueFacts::new();
        values.mark_domain(y.clone(), finite_domain(&[0, 1, 2]));
        let inferences =
            infer_value_domains_from_zero_equation_with_modulus(&expr, &values, &BigInt::from(17));
        let (_, domain) = inferences.iter().find(|(cell, _)| cell == &x).unwrap();
        assert_eq!(domain, &finite_domain(&[-6, -2, -1, 3, 7]));
        for a in 0_i64..17 {
            for b in 0_i64..3 {
                let d = a - 4 * b;
                if ((d - 3) * (7 - d) * (d + 1)).rem_euclid(17) == 0 {
                    let signed = if a > 8 { a - 17 } else { a };
                    assert!(domain_values(domain).contains(&BigInt::from(signed)));
                }
            }
        }
    }

    #[test]
    fn root_rule_rejects_different_affine_parts_and_unknown_scalars() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let affine = |coefficient| {
            UcpExpr::add(
                UcpExpr::var(x.clone()),
                UcpExpr::scale_by(UcpExpr::var(y.clone()), UcpScalar::known_i64(coefficient)),
            )
        };
        let expr = UcpExpr::mul(affine(-4), affine(-2));
        assert!(infer_root_expression_domain(&expr, &UcpValueFacts::new(), None).is_none());
        let expr = UcpExpr::scale_by(
            UcpExpr::mul(
                UcpExpr::var(x.clone()),
                UcpExpr::add(UcpExpr::var(x), UcpExpr::known_constant_i64(-1)),
            ),
            UcpScalar::Unknown,
        );
        assert!(infer_root_expression_domain(&expr, &UcpValueFacts::new(), None).is_none());
    }

    #[test]
    fn root_rule_does_not_drop_a_zero_factor() {
        //Raw enum construction intentionally bypasses the constructor's zero simplification.
        let x = UcpExpr::var(CellId::advice(0, 0));
        for scalar in [UcpScalar::Zero, UcpScalar::Known(BigInt::from(0))] {
            let zero = UcpExpr::Scale(Box::new(x.clone()), scalar);
            let expr = UcpExpr::Mul(
                Box::new(zero),
                Box::new(UcpExpr::mul(
                    x.clone(),
                    UcpExpr::add(x.clone(), UcpExpr::known_constant_i64(-1)),
                )),
            );
            assert!(
                infer_value_domains_from_zero_equation(&expr, &UcpValueFacts::new()).is_empty()
            );
        }
    }

    #[test]
    fn affine_root_projection_respects_the_finite_domain_limit() {
        let x = UcpExpr::var(CellId::advice(0, 0));
        let product = (1..=MAX_FINITE_DOMAIN_SIZE).fold(x.clone(), |product, root| {
            UcpExpr::mul(
                product,
                UcpExpr::add(x.clone(), UcpExpr::known_constant_i64(-(root as i64))),
            )
        });
        assert!(infer_root_expression_domain(&product, &UcpValueFacts::new(), None).is_none());
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

    //Azt ellenőrzi, hogy a Fig. 10 Base-Conv value szabály explicit finite domainként tanulja x tartományát
    #[test]
    fn base_conv_value_rule_learns_target_range_as_finite_set() {
        let x = CellId::advice(0, 0);
        let b0 = CellId::advice(1, 0);
        let b1 = CellId::advice(2, 0);
        let b2 = CellId::advice(3, 0);
        let boolean = finite_domain(&[0, 1]);
        let mut values = UcpValueFacts::new();
        values.mark_domain(b0.clone(), boolean.clone());
        values.mark_domain(b1.clone(), boolean.clone());
        values.mark_domain(b2.clone(), boolean);

        let expr = UcpExpr::add(
            UcpExpr::add(
                UcpExpr::var(b0),
                UcpExpr::scale_by(UcpExpr::var(b1), UcpScalar::known_i64(2)),
            ),
            UcpExpr::add(
                UcpExpr::scale_by(UcpExpr::var(b2), UcpScalar::known_i64(4)),
                UcpExpr::neg(UcpExpr::var(x.clone())),
            ),
        );

        let inferences = infer_base_conv_value_domains(&expr, &values, None);

        assert_eq!(
            inferences,
            vec![(x, finite_domain(&[0, 1, 2, 3, 4, 5, 6, 7]))]
        );
    }

    //Azt ellenőrzi, hogy túl nagy base-conv tartományt nem listázunk ki finite setként
    #[test]
    fn base_conv_value_rule_respects_finite_domain_limit() {
        let x = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();
        let boolean = finite_domain(&[0, 1]);
        let mut expr = UcpExpr::neg(UcpExpr::var(x.clone()));

        for index in 0..9 {
            let bit = CellId::advice(index + 1, 0);
            values.mark_domain(bit.clone(), boolean.clone());
            let coefficient = 1_i64 << index;
            expr = UcpExpr::add(
                UcpExpr::scale_by(UcpExpr::var(bit), UcpScalar::known_i64(coefficient)),
                expr,
            );
        }

        assert!(infer_base_conv_value_domains(&expr, &values, None).is_empty());
    }
}
