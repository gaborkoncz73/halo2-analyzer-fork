//! Korlatos felsorolas egyetlen nullaegyenletre: kis veges domainek kombinacioit probalja vegig.
//! Csak azt a kombinaciot zarja ki, amelyre az egyenlet biztosan nem teljesul; a tobbi megmarad.
//! Legfeljebb egy domain nelkuli cellat enged, es azt csak affin elofordulasnal szamolja ki.

use super::{
    finite_domain_from_values, mod_field, mod_inverse, BigInt, CellId, UcpExpr, UcpScalar,
};
use super::{UcpValueDomain, UcpValueFacts, MAX_FINITE_DOMAIN_SIZE};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap},
};

// A keretek a munkat korlatozzak; tullepesnel nem tanul uj tenyt, es nem csonkit domaint.
const MAX_ASSIGNMENTS: usize = 4096;
const MAX_EXPRESSION_NODES: usize = 256;

// A kifejezes erteke coefficient*y+constant alakban, a p modulus szerint.
struct Affine {
    coefficient: BigInt,
    constant: BigInt,
}

impl Affine {
    fn is_zero(&self) -> bool {
        self.coefficient == BigInt::from(0) && self.constant == BigInt::from(0)
    }
}

fn is_constant_zero(expr: &UcpExpr, modulus: &BigInt) -> bool {
    match expr {
        UcpExpr::Const(scalar) => match scalar {
            UcpScalar::Zero => true,
            UcpScalar::Known(value) => mod_field(value.clone(), modulus) == BigInt::from(0),
            UcpScalar::NonZero | UcpScalar::Unknown => false,
        },
        UcpExpr::Scale(inner, scalar) => {
            scalar_is_zero(scalar, modulus) || is_constant_zero(inner, modulus)
        }
        UcpExpr::Mul(left, right) => {
            is_constant_zero(left, modulus) || is_constant_zero(right, modulus)
        }
        UcpExpr::Neg(inner) => is_constant_zero(inner, modulus),
        UcpExpr::Add(_, _) | UcpExpr::Var(_) => false,
    }
}

fn scalar_is_zero(scalar: &UcpScalar, modulus: &BigInt) -> bool {
    match scalar {
        UcpScalar::Zero => true,
        UcpScalar::Known(value) => mod_field(value.clone(), modulus) == BigInt::from(0),
        UcpScalar::NonZero | UcpScalar::Unknown => false,
    }
}

// Csak az erteket tenylegesen befolyasolo cellakat gyujti; a nullaval szorzott reszfat kihagyja.
fn live_cells(
    expr: &UcpExpr,
    modulus: &BigInt,
    cells: &mut BTreeSet<CellId>,
    nodes: &mut usize,
) -> Option<()> {
    *nodes += 1;
    if *nodes > MAX_EXPRESSION_NODES {
        return None;
    }
    if is_constant_zero(expr, modulus) {
        return Some(());
    }
    match expr {
        UcpExpr::Var(cell) => {
            cells.insert(cell.clone());
        }
        UcpExpr::Const(_) => {}
        UcpExpr::Neg(inner) | UcpExpr::Scale(inner, _) => live_cells(inner, modulus, cells, nodes)?,
        UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
            live_cells(left, modulus, cells, nodes)?;
            live_cells(right, modulus, cells, nodes)?;
        }
    }
    Some(())
}

// None: az ertek ezen a helyen nem szamolhato ki (ismeretlen skalar vagy y-ban nem affin alak).
fn evaluate(
    expr: &UcpExpr,
    assignment: &BTreeMap<CellId, BigInt>,
    unknown: Option<&CellId>,
    modulus: &BigInt,
) -> Option<Affine> {
    match expr {
        UcpExpr::Var(cell) => {
            if unknown == Some(cell) {
                return Some(Affine {
                    coefficient: BigInt::from(1),
                    constant: BigInt::from(0),
                });
            }
            Some(Affine {
                coefficient: BigInt::from(0),
                constant: assignment.get(cell)?.clone(),
            })
        }
        UcpExpr::Const(scalar) => Some(Affine {
            coefficient: BigInt::from(0),
            constant: mod_field(scalar.as_known()?, modulus),
        }),
        UcpExpr::Neg(inner) => {
            let inner = evaluate(inner, assignment, unknown, modulus)?;
            Some(Affine {
                coefficient: mod_field(-inner.coefficient, modulus),
                constant: mod_field(-inner.constant, modulus),
            })
        }
        UcpExpr::Add(left, right) => {
            let left = evaluate(left, assignment, unknown, modulus)?;
            let right = evaluate(right, assignment, unknown, modulus)?;
            Some(Affine {
                coefficient: mod_field(left.coefficient + right.coefficient, modulus),
                constant: mod_field(left.constant + right.constant, modulus),
            })
        }
        UcpExpr::Mul(left, right) => {
            let left = evaluate(left, assignment, unknown, modulus);
            let right = evaluate(right, assignment, unknown, modulus);
            // A nullatenyezo a masik oldal ertekelhetosegetol fuggetlenul nullat ad.
            if left.as_ref().is_some_and(Affine::is_zero)
                || right.as_ref().is_some_and(Affine::is_zero)
            {
                return Some(Affine {
                    coefficient: BigInt::from(0),
                    constant: BigInt::from(0),
                });
            }
            let (left, right) = (left?, right?);
            if left.coefficient != BigInt::from(0) && right.coefficient != BigInt::from(0) {
                return None;
            }
            Some(Affine {
                coefficient: mod_field(
                    &left.coefficient * &right.constant + &right.coefficient * &left.constant,
                    modulus,
                ),
                constant: mod_field(left.constant * right.constant, modulus),
            })
        }
        UcpExpr::Scale(inner, scalar) => {
            if scalar_is_zero(scalar, modulus) {
                return Some(Affine {
                    coefficient: BigInt::from(0),
                    constant: BigInt::from(0),
                });
            }
            let inner = evaluate(inner, assignment, unknown, modulus)?;
            if inner.is_zero() {
                return Some(inner);
            }
            let scale = mod_field(scalar.as_known()?, modulus);
            Some(Affine {
                coefficient: mod_field(inner.coefficient * &scale, modulus),
                constant: mod_field(inner.constant * scale, modulus),
            })
        }
    }
}

// A kereso reteg tesztjei ezzel olyan kapcsolast vizsgalhatnak, amelyet a UCP egyedul nem old meg.
#[cfg(test)]
thread_local! {
    static DISABLED_FOR_TEST: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
pub(crate) struct ZeroEnumerationDisabled;

#[cfg(test)]
pub(crate) fn without_zero_enumeration() -> ZeroEnumerationDisabled {
    DISABLED_FOR_TEST.with(|disabled| disabled.set(true));
    ZeroEnumerationDisabled
}

#[cfg(test)]
impl Drop for ZeroEnumerationDisabled {
    fn drop(&mut self) {
        DISABLED_FOR_TEST.with(|disabled| disabled.set(false));
    }
}

type DomainsKey = Vec<(Option<UcpValueDomain>, bool)>;
type Answer = Vec<(CellId, UcpValueDomain)>;

// A felsorolas tiszta fuggveny: az eredmenyt az egyenlet, a modulus es a cellak domainjei hatarozzak meg.
// A hipotetikus kerdesek tobbnyire csak nehany cellat erintenek, ezert ugyanazok a bemenetek ismetlodnek.
#[derive(Default)]
struct AnswerCache {
    entries: usize,
    answers: HashMap<BigInt, HashMap<UcpExpr, HashMap<DomainsKey, Answer>>>,
}

const MAX_CACHED_ANSWERS: usize = 1 << 18;

thread_local! {
    static ANSWERS: RefCell<AnswerCache> = RefCell::default();
}

pub(super) fn infer(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> Vec<(CellId, UcpValueDomain)> {
    #[cfg(test)]
    if DISABLED_FOR_TEST.with(std::cell::Cell::get) {
        return Vec::new();
    }
    if modulus <= &BigInt::from(1) {
        return Vec::new();
    }
    let mut cells = BTreeSet::new();
    let mut nodes = 0;
    if live_cells(expr, modulus, &mut cells, &mut nodes).is_none() {
        return Vec::new();
    }
    let key: DomainsKey = cells
        .iter()
        .map(|cell| (values.domain(cell).cloned(), values.domain_is_complete(cell)))
        .collect();
    let cached = ANSWERS.with(|cache| {
        cache
            .borrow()
            .answers
            .get(modulus)
            .and_then(|answers| answers.get(expr))
            .and_then(|answers| answers.get(&key))
            .cloned()
    });
    if let Some(answer) = cached {
        return answer;
    }
    let answer = enumerate(expr, cells, values, modulus);
    ANSWERS.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.entries >= MAX_CACHED_ANSWERS {
            *cache = AnswerCache::default();
        }
        cache.entries += 1;
        cache
            .answers
            .entry(modulus.clone())
            .or_default()
            .entry(expr.clone())
            .or_default()
            .insert(key, answer.clone());
    });
    answer
}

fn enumerate(
    expr: &UcpExpr,
    cells: BTreeSet<CellId>,
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> Answer {
    let mut fixed = BTreeMap::new();
    let mut enumerated: Vec<(CellId, Vec<BigInt>)> = Vec::new();
    let mut unknown = None;
    let mut assignments = 1usize;
    for cell in cells {
        match values.domain(&cell) {
            None => {
                // Ket domain nelkuli cella mellett az egyenlet egy kombinaciot sem zarhat ki.
                if unknown.replace(cell).is_some() {
                    return Vec::new();
                }
            }
            Some(domain) => {
                let candidates: Vec<_> = super::domain_values(domain)
                    .into_iter()
                    .map(|value| mod_field(value, modulus))
                    .collect();
                if let [value] = candidates.as_slice() {
                    fixed.insert(cell, value.clone());
                } else {
                    let Some(next) = assignments.checked_mul(candidates.len()) else {
                        return Vec::new();
                    };
                    if next > MAX_ASSIGNMENTS {
                        return Vec::new();
                    }
                    assignments = next;
                    enumerated.push((cell, candidates));
                }
            }
        }
    }
    if enumerated.is_empty() {
        // Egyetlen ismeretlenre a meglevo linearis szabalyok mar valaszolnak.
        return Vec::new();
    }

    let known_complete = |cell: &CellId| values.domain_is_complete(cell);
    let mut kept: Vec<BTreeSet<BigInt>> = vec![BTreeSet::new(); enumerated.len()];
    let mut unknown_values = BTreeSet::new();
    let mut unknown_is_determined = unknown.is_some();
    let mut indices = vec![0usize; enumerated.len()];
    let mut assignment = fixed;
    loop {
        for (index, (cell, candidates)) in enumerated.iter().enumerate() {
            assignment.insert(cell.clone(), candidates[indices[index]].clone());
        }
        let keep = match evaluate(expr, &assignment, unknown.as_ref(), modulus) {
            // Nem kiertekelheto agat nem zar ki, es az ismeretlenre sem kovetkeztet belole.
            None => {
                unknown_is_determined = false;
                true
            }
            Some(value) if value.coefficient == BigInt::from(0) => {
                unknown_is_determined = false;
                value.constant == BigInt::from(0)
            }
            Some(value) => {
                match mod_inverse(&value.coefficient, modulus) {
                    Some(inverse) => {
                        unknown_values.insert(mod_field(-value.constant * inverse, modulus));
                    }
                    None => unknown_is_determined = false,
                }
                true
            }
        };
        if keep {
            for (index, (_, candidates)) in enumerated.iter().enumerate() {
                kept[index].insert(candidates[indices[index]].clone());
            }
        }
        // A kovetkezo kombinaciora lep; az utolso utan kilep.
        let mut position = 0;
        loop {
            if position == indices.len() {
                let mut results = Vec::new();
                if kept.iter().any(BTreeSet::is_empty) {
                    return results;
                }
                for ((cell, candidates), values) in enumerated.iter().zip(kept) {
                    // Csak valodi szukulest javasol; a teljesnek igazolt domaint nem erinti.
                    if values.len() == candidates.len() || known_complete(cell) {
                        continue;
                    }
                    if let Some(domain) = finite_domain_from_values(values, Some(modulus)) {
                        results.push((cell.clone(), domain));
                    }
                }
                if let (Some(cell), true) = (unknown, unknown_is_determined) {
                    if !unknown_values.is_empty() && unknown_values.len() <= MAX_FINITE_DOMAIN_SIZE
                    {
                        if let Some(domain) =
                            finite_domain_from_values(unknown_values, Some(modulus))
                        {
                            results.push((cell, domain));
                        }
                    }
                }
                return results;
            }
            indices[position] += 1;
            if indices[position] < enumerated[position].1.len() {
                break;
            }
            indices[position] = 0;
            position += 1;
        }
    }
}
