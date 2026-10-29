//Delta: lefedő domainek tárolása és kifejezések kiértékelése.
//Az új tényeket levezető algoritmusok a value_inference.rs fájlban találhatók.
//Az alábbi ábrahivatkozások a QED²-cikkre utalnak; az ábraszámok még ellenőrizendők.

use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
};
use anyhow::{ensure, Context, Result};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

// A következtető függvényeket a value modul elérési útján exportálja.
#[path = "value_inference.rs"]
mod inference;
pub(crate) use inference::LinearDomains;
#[cfg(test)]
use inference::{
    infer_base_conv_value_domains, infer_root_expression_domain, mod_field,
    MAX_LINEAR_SYSTEM_CELLS, MAX_LINEAR_SYSTEM_EQUATIONS,
};
pub use inference::{
    infer_domains_from_expression_domain, infer_domains_from_expression_domain_with_modulus,
    infer_linear_system_values_with_modulus, infer_value_assignments_from_zero_equation,
    infer_value_domains_from_zero_equation, infer_value_domains_from_zero_equation_with_modulus,
};

// Reprezentációs korlátnál nem tanul új domaint; a valódi lehetőségeket nem csonkítja.
pub(crate) const MAX_FINITE_DOMAIN_SIZE: usize = 256;
/// A támogatott Halo2-testek értékei elférnek benne, de a tárolt egészek mérete korlátos marad.
pub const MAX_VALUE_BITS: u64 = 4096;

//Minden valóban lehetséges értéket lefed, de tartalmazhat még kizáratlan jelölteket is.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpValueDomain {
    Exact(BigInt),
    //Explicit halmaz, nem intervallum: például {1,3} nem tartalmazza a 2-t.
    FiniteSet(BTreeSet<BigInt>),
}

//A cellákhoz rendelt domain-t tárolja
//Hiányzó bejegyzés: nincs tárolt domain. Ez nem bizonyít sem egyértelműséget, sem titkosságot.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UcpValueFacts {
    domains: HashMap<CellId, UcpValueDomain>,
    complete_domains: HashSet<CellId>,
}

//Enum az értékekhez
//NonZero nem jelent egyetlen értéket: például a {3,7} domain is biztosan nem nulla.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueKind {
    Zero,
    NonZero,
    Unknown,
}

impl UcpValueDomain {
    // Konkrét értékből egyelemű domaint készít.
    pub fn exact(value: BigInt) -> Self {
        Self::Exact(value)
    }

    // A megadott értékekből véges domaint készít.
    //Duplikátumokat töröl, az egyelemű halmazt Exact-tá alakítja; hibánál vagy üres halmaznál None.
    pub fn finite_set<I>(values: I) -> Option<Self>
    where
        I: IntoIterator<Item = BigInt>,
    {
        let mut set = BTreeSet::new();

        // A teljes halmaz felépítése közben ellenőrzi az érték- és elemszámkorlátot.
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

    //Az egyeleműséget az Exact változat jelzi; a finite_set konstruktor biztosítja ezt az alakot.
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

    // Visszaadja a domain legnagyobb értékét az intervallumos feltételek ellenőrzéséhez.
    pub fn max_value(&self) -> &BigInt {
        match self {
            Self::Exact(value) => value,
            Self::FiniteSet(values) => values
                .iter()
                .next_back()
                .expect("finite_set never creates an empty set"),
        }
    }

    // Visszaadja a két domain metszetét.
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

    // A konkrét értéket egyelemű domainként jegyzi be.
    // Új tény bejegyzésekor igazat ad vissza a következő UCP-kör jelzéséhez.
    pub fn mark_known(&mut self, cell: CellId, value: BigInt) -> bool {
        self.mark_domain(cell, UcpValueDomain::exact(value))
    }

    // A megadott lefedő domaint az állapotba olvasztja.
    // Új vagy szűkebb domain bejegyzésekor igazat ad vissza.
    //Csak már igazolt lefedő domaint szabad átadni: ez a tároló nem ellenőriz kényszereket vagy SMT-t.
    pub fn mark_domain(&mut self, cell: CellId, domain: UcpValueDomain) -> bool {
        if self.domain_is_complete(&cell) {
            return false;
        }
        // A bemeneti domain reprezentálhatóságát ellenőrzi.
        let domain = match domain {
            // A konkrét érték bitméretét ellenőrzi.
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
                // Meglévő domainnél a két halmaz metszetét képezi.
                // Üres metszetet nem tárol; az engine külön vizsgálja az ellentmondást.
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
            // Meglévő bejegyzés hiányában felveszi az új domaint.
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

    /// Kielégíthető premisszák mellett az egyelemű lefedő domain már teljes.
    /// Az egyértelműség visszaállított érték nélkül nem igazolja a domain teljességét.
    /// A false azt jelenti, hogy a teljesség nincs bizonyítva. Új premisszákhoz új elemzési állapot kell.
    pub fn domain_is_complete(&self, cell: &CellId) -> bool {
        self.domains
            .get(cell)
            .is_some_and(|domain| domain.is_singleton() || self.complete_domains.contains(cell))
    }

    /// A mintáknak ugyanazon eredeti kontextus kielégítő értékadásaiból kell származniuk.
    //A W mintái belső, Delta jelöltjei külső közelítést adnak; egyezésük igazolja a teljességet.
    pub(crate) fn mark_complete_from_samples(
        &mut self,
        cell: &CellId,
        samples: &BTreeSet<BigInt>,
        modulus: &BigInt,
    ) -> Result<bool> {
        let Some(domain) = self.domains.get(cell) else {
            return Ok(false);
        };
        let entries: Vec<_> = match domain {
            UcpValueDomain::Exact(value) => vec![value],
            UcpValueDomain::FiniteSet(values) => values.iter().collect(),
        };
        let mut candidates = BTreeMap::new();
        // Közös testbeli reprezentánsra normalizálja az értékeket; -1 és p-1 ugyanazt az elemet jelöli.
        for value in entries {
            let normalized = normalize_field_value(value.clone(), modulus)
                .context("Unsupported complete-domain field value")?;
            candidates
                .entry(normalized)
                .or_insert_with(|| value.clone());
        }
        let feasible: BTreeSet<_> = samples
            .iter()
            .map(|value| {
                normalize_field_value(value.clone(), modulus)
                    .context("Unsupported complete-domain sample")
            })
            .collect::<Result<_>>()?;
        ensure!(
            feasible.iter().all(|value| candidates.contains_key(value)),
            "Recorded domain for {} excludes a proven feasible value",
            cell
        );
        if feasible.len() != candidates.len() || feasible.is_empty() {
            return Ok(false);
        }
        let canonical = UcpValueDomain::finite_set(candidates.into_values())
            .context("Complete domain exceeds representation limits")?;
        let changed = self.domains.get(cell) != Some(&canonical);
        self.domains.insert(cell.clone(), canonical);
        Ok(self.complete_domains.insert(cell.clone()) || changed)
    }

    /// Önálló másolatot készít a domainekről hipotetikus következtetéshez.
    /// A másolatban törli a többértékű domainek teljességi jelöléseit, hogy azok
    /// a vizsgált feltevés mellett szűkíthetők legyenek. Az eredeti állapotot nem módosítja.
    /// Az egyelemű domaineket a domain_is_complete továbbra is teljesnek tekinti.
    pub(crate) fn for_hypothetical_reasoning(&self) -> Self {
        Self {
            domains: self.domains.clone(),
            // A másolatban engedi a többértékű teljes domain hipotetikus szűkítését; az eredeti állapotot nem módosítja.
            complete_domains: HashSet::new(),
        }
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

//Az elemző bemenetében megadott instance cellákból létrehozza a kezdeti konkrét Delta-értékeket.
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

//Megpróbál egy UCP-kifejezést konkrét értékre kiértékelni a már ismert Delta alapján.
//Ez BigInt-aritmetika; a testmodulus szerinti normalizálást a modulusos domainfüggvények végzik.
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
        // Skálázásnál konkrét együtthatóval számol, vagy a biztos nulla eredményt ismeri fel.
        UcpExpr::Scale(inner, scalar) => match scalar {
            //Nullával szorzás mindig nulla
            UcpScalar::Zero => Some(BigInt::from(0)),
            //Konkrét skálánál kiszámolja a belső érték és a skála szorzatát
            UcpScalar::Known(scale) => bounded_value(evaluate_expr(inner, values)? * scale),
            // Ismeretlen skálánál csak a nulla belső értékből ad konkrét eredményt.
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

//QED²-cikk 9. ábrája, Var/Const/Op: a kifejezés véges Delta-domainjét számolja modulus nélkül.
pub fn expression_domain(expr: &UcpExpr, values: &UcpValueFacts) -> Option<UcpValueDomain> {
    expression_domain_with_optional_modulus(expr, values, None)
}

//QED²-cikk 9. ábrája, Var/Const/Op: a kifejezés véges Delta-domainjét számolja a test modulusa szerint.
pub fn expression_domain_with_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: &BigInt,
) -> Option<UcpValueDomain> {
    expression_domain_with_optional_modulus(expr, values, Some(field_modulus))
}

// QED²-cikk 9. ábrája: a Var, Const és Op lépéseket közös végeshalmaz-kiértékelővel kezeli.
//A műveleti eredmény is lefedő domain: a részfák közötti korrelációkat nem követi pontosan.
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

//A tárolt egészek méretét korlátozza, nem gépi szavakat: a testelemek túlléphetik az i64 tartományát.
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

    // Előjeles reprezentánst használ: p-1 például -1-ként tárolható,
    //az elemző SMT-illesztője később ezt újra testelemre normalizálja.
    if normalized > modulus / BigInt::from(2) {
        normalized -= modulus;
    }

    bounded_value(normalized)
}

fn finite_domain_from_values<I>(values: I, field_modulus: Option<&BigInt>) -> Option<UcpValueDomain>
where
    I: IntoIterator<Item = BigInt>,
{
    // Normalizálás után szűri az ismétléseket; túl nagy eredménynél nem ad új domaint.
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

    // A Descartes-szorzat munkáját is korlátozza; None esetén nem állapít meg üres megoldáshalmazt.
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

//Megmondja, hogy egy kifejezés biztosan nulla, biztosan nem nulla, vagy ismeretlen.
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
    //Ha a teljes domain nem számolható ki, az algebrai nulla/nemnulla tulajdonság még felismerhető.
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

    // A teszt ellenőrzi, hogy a két egyenletet együtt megoldja x=6,y=4-re, ahol az egyenkénti Assign elakad.
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

    // A teszt ellenőrzi, hogy ranghiánynál vagy ellentmondó további sornál nem választ tetszőleges modellt.
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

    // A teszt ellenőrzi, hogy a p-1 együtthatót -1-ként kezeli az i64-en túli reprezentánsnál is.
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

    // A teszt ellenőrzi, hogy nagy komponens korlátja mellett is megoldja a független kis rendszert.
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
        //Az x+y=10 és x-y=2 rögzíti x és y értékét; az x+z+w=0 mellett z és w nem egyértelmű.
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
        //A hasznos egyenletpár már a helyi keresési kereten kívül van; a teljes komponens túl nagy.
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

    //A nagy és kis értékek is megmaradnak: az i64 korlátja nem zárhat ki testbeli megoldást.
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
        //Az (x - 2^200) * (x - (2^200 + 2)) = 0 két gyököt enged meg, nem a középpontjukat.
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

    //Azt ellenőrzi, hogy ismert értékekkel egy egyszerű aritmetikai kifejezés kiértékelhető.
    #[test]
    fn evaluates_known_arithmetic_expression() {
        let x = CellId::instance(0, 0);
        let mut values = UcpValueFacts::new();
        values.mark_known(x.clone(), BigInt::from(2));
        let expr = UcpExpr::add(UcpExpr::var(x), UcpExpr::known_constant_i64(-1));

        assert_eq!(evaluate_expr(&expr, &values), Some(BigInt::from(1)));
        assert_eq!(value_kind(&expr, &values), ValueKind::NonZero);
    }

    //Azt ellenőrzi, hogy nem nulla szorzótényező mellett a c * y = 0 alakból y = 0 következik.
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
        //A könyvtár a b*(1-b) alakot használja a b*(b-1) helyett.
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
        //Az eltolt első és az ellentétes előjelű második tényező a közös kifejezés felismerését teszteli.
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
        //A közvetlen enum-létrehozás szándékosan megkerüli a konstruktor nullával való egyszerűsítését.
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

    //Azt ellenőrzi, hogy két domain metszete szűkítheti a logikai értéktartományt konkrét értékre.
    #[test]
    fn intersecting_domain_can_refine_boolean_to_exact_value() {
        let b = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();

        assert!(values.mark_domain(b.clone(), finite_domain(&[0, 1])));
        assert!(values.mark_known(b.clone(), BigInt::from(1)));

        assert_eq!(values.known_value(&b), Some(&BigInt::from(1)));
    }

    //Azt ellenőrzi, hogy egy véges domain teljesen beleesik-e egy adott intervallumba.
    #[test]
    fn finite_domain_can_be_checked_against_digit_range() {
        let b = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();

        values.mark_domain(b.clone(), finite_domain(&[0, 1]));

        assert!(values.domain_is_subset_of_range(&b, &BigInt::from(0), &BigInt::from(1)));
        assert!(values.domain_is_subset_of_range(&b, &BigInt::from(0), &BigInt::from(9)));
        assert!(!values.domain_is_subset_of_range(&b, &BigInt::from(1), &BigInt::from(9)));
    }

    //QED²-cikk 9. ábrája, Var/Const/Op: a véges kifejezésdomainek kiértékelését teszteli.
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

    // A teszt ellenőrzi, hogy c*x-e=0 esetén a testben c inverzével számol.
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

    // A teszt ellenőrzi, hogy az e in Omega tagsági feltételből celladomaint következtet.
    #[test]
    fn expression_membership_learns_affine_input_domain() {
        let x = CellId::advice(0, 0);
        let expr = UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(1));
        let table_domain = finite_domain(&[1, 2, 3]);

        let inferences =
            infer_domains_from_expression_domain(&expr, &table_domain, &UcpValueFacts::new());

        assert_eq!(inferences, vec![(x, finite_domain(&[0, 1, 2]))]);
    }

    //QED²-cikk 10. ábrája, Base-Conv: a számjegyes alakhoz kapcsolódó domainkövetkeztetést teszteli.
    // A számjegykorlátokból x lefedő domainjét képezi; a számjegyek egyértelműségét itt nem bizonyítja.
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

    // A teszt ellenőrzi, hogy túl nagy számjegytartományt nem sorol fel csonkított véges halmazként.
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

#[cfg(test)]
mod completeness_tests {
    use super::*;
    use crate::circuit_analyzer::ucp::{
        engine::analyze_expressions_with_values_and_modulus, facts::UcpFacts,
    };

    fn domain(values: &[i64]) -> UcpValueDomain {
        UcpValueDomain::finite_set(values.iter().copied().map(BigInt::from)).unwrap()
    }

    fn samples(values: &[i64]) -> BTreeSet<BigInt> {
        values.iter().copied().map(BigInt::from).collect()
    }

    #[test]
    fn uniqueness_and_partial_samples_do_not_certify_a_finite_domain() {
        let cell = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();
        assert!(!values.domain_is_complete(&cell));
        values.mark_domain(cell.clone(), domain(&[0, 1, 2]));
        assert!(!values
            .mark_complete_from_samples(&cell, &samples(&[0, 1]), &101.into())
            .unwrap());
        let result = analyze_expressions_with_values_and_modulus(
            &[],
            UcpFacts::from_iter([cell.clone()]),
            values,
            &101.into(),
        );
        assert!(result.facts.is_unique(&cell));
        assert!(!result.value_facts.domain_is_complete(&cell));
        assert_eq!(result.value_facts.domain(&cell), Some(&domain(&[0, 1, 2])));
    }

    #[test]
    fn complete_domains_are_stable_but_hypothetical_copies_can_narrow() {
        let cell = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();
        values.mark_domain(cell.clone(), domain(&[3, 7]));
        assert!(values
            .mark_complete_from_samples(&cell, &samples(&[3, 7]), &101.into())
            .unwrap());
        assert!(values.domain_is_complete(&cell));
        assert!(!values.mark_known(cell.clone(), 3.into()));
        assert_eq!(values.domain(&cell), Some(&domain(&[3, 7])));
        assert!(!values
            .mark_complete_from_samples(&cell, &samples(&[3, 7]), &101.into())
            .unwrap());
        let mut hypothetical = values.for_hypothetical_reasoning();
        assert!(!hypothetical.domain_is_complete(&cell));
        assert!(hypothetical.mark_known(cell.clone(), 3.into()));
        assert!(hypothetical.domain_is_complete(&cell));
        assert_eq!(values.domain(&cell), Some(&domain(&[3, 7])));
        assert_eq!(hypothetical.known_value(&cell), Some(&3.into()));
    }

    #[test]
    fn inconsistent_empty_and_oversized_samples_cannot_certify_a_domain() {
        let cell = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();
        values.mark_domain(cell.clone(), domain(&[0, 1]));
        assert!(!values
            .mark_complete_from_samples(&cell, &BTreeSet::new(), &101.into())
            .unwrap());
        assert!(values
            .mark_complete_from_samples(&cell, &samples(&[0, 1, 2]), &101.into())
            .is_err());
        let oversized = BTreeSet::from([BigInt::from(1) << (MAX_VALUE_BITS + 1) as usize]);
        assert!(values
            .mark_complete_from_samples(&cell, &oversized, &101.into())
            .is_err());
        assert!(!values.domain_is_complete(&cell));
        assert_eq!(values.domain(&cell), Some(&domain(&[0, 1])));
    }

    #[test]
    fn singleton_domains_and_field_aliases_have_one_feasible_value() {
        let cell = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();
        values.mark_known(cell.clone(), 3.into());
        assert!(values.domain_is_complete(&cell));
        let mut aliases = UcpValueFacts::new();
        aliases.mark_domain(cell.clone(), domain(&[-1, 12]));
        assert!(!aliases.domain_is_complete(&cell));
        assert!(aliases
            .mark_complete_from_samples(&cell, &samples(&[-1, 12]), &13.into())
            .unwrap());
        assert!(aliases.domain_is_complete(&cell));
        assert_eq!(aliases.known_value(&cell), Some(&(-1).into()));
    }

    #[test]
    fn complete_domains_remain_operands_for_other_cells_without_exporting_completeness() {
        let source = CellId::advice(0, 0);
        let shifted = CellId::advice(1, 0);
        let zero = CellId::advice(2, 0);
        let mut values = UcpValueFacts::new();
        values.mark_domain(source.clone(), domain(&[3, 7]));
        values
            .mark_complete_from_samples(&source, &samples(&[3, 7]), &101.into())
            .unwrap();
        let equations = [
            UcpExpr::add(
                UcpExpr::var(shifted.clone()),
                UcpExpr::neg(UcpExpr::add(
                    UcpExpr::var(source.clone()),
                    UcpExpr::known_constant_i64(1),
                )),
            ),
            UcpExpr::mul(
                UcpExpr::var(zero.clone()),
                UcpExpr::add(
                    UcpExpr::var(source.clone()),
                    UcpExpr::known_constant_i64(-5),
                ),
            ),
        ];
        let inferences = infer_value_domains_from_zero_equation_with_modulus(
            &equations[0],
            &values,
            &101.into(),
        );
        assert!(inferences.iter().all(|(cell, _)| cell != &source));
        let result = analyze_expressions_with_values_and_modulus(
            &equations,
            UcpFacts::new(),
            values,
            &101.into(),
        );
        assert_eq!(result.value_facts.domain(&source), Some(&domain(&[3, 7])));
        assert!(result.value_facts.domain_is_complete(&source));
        assert!(!result.facts.is_unique(&source));
        assert_eq!(result.value_facts.domain(&shifted), Some(&domain(&[4, 8])));
        assert!(!result.value_facts.domain_is_complete(&shifted));
        assert_eq!(result.value_facts.known_value(&zero), Some(&0.into()));
        assert!(result.facts.is_unique(&zero));
        assert!(result.value_facts.domain_is_complete(&zero));
    }
}
