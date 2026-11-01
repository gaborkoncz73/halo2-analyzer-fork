//! Kis véges domainekből vetít vissza olyan kifejezést, amely a célcellában affin.
//! A többi cella közötti korrelációk elhagyása csak bővítheti a lefedő halmazt.

use super::super::combine_domain_values;
use super::{
    domain_values, finite_domain_from_values, mod_inverse, normalize_value, solve_linear_value,
    BigInt, CellId, UcpExpr, UcpScalar, UcpValueDomain, UcpValueFacts,
};
use std::collections::BTreeSet;

const MAX_EXPRESSION_NODES: usize = 256;
const MAX_TARGETS: usize = 64;
const MAX_PROJECTION_WORK: usize = 4096;

// A teljes kifejezés minden megengedett értékeléséhez tartalmaz megfelelő a és b értéket:
// expr = a*target+b. A két halmaz nem állítja a párok közös megvalósíthatóságát.
struct AffineCover {
    coefficient: UcpValueDomain,
    remainder: UcpValueDomain,
}

struct Projection<'a> {
    values: &'a UcpValueFacts,
    modulus: Option<&'a BigInt>,
    work: usize,
}

pub(super) fn infer(
    expr: &UcpExpr,
    rhs: &UcpValueDomain,
    values: &UcpValueFacts,
    modulus: Option<&BigInt>,
) -> Vec<(CellId, UcpValueDomain)> {
    if modulus.is_some_and(|p| p <= &BigInt::from(1)) {
        return Vec::new();
    }
    let mut targets = BTreeSet::new();
    let mut pending = vec![expr];
    let mut nodes = 0;
    while let Some(node) = pending.pop() {
        nodes += 1;
        if nodes > MAX_EXPRESSION_NODES {
            return Vec::new();
        }
        match node {
            UcpExpr::Var(cell) => {
                if !values.domain_is_complete(cell) && values.known_value(cell).is_none() {
                    targets.insert(cell.clone());
                    if targets.len() > MAX_TARGETS {
                        return Vec::new();
                    }
                }
            }
            UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
                pending.extend([left.as_ref(), right.as_ref()]);
            }
            UcpExpr::Neg(inner) | UcpExpr::Scale(inner, _) => pending.push(inner),
            UcpExpr::Const(_) => (),
        }
    }
    let mut projection = Projection {
        values,
        modulus,
        work: MAX_PROJECTION_WORK,
    };
    let mut results = Vec::new();
    for target in targets {
        if let Some(domain) = projection.project(expr, rhs, &target) {
            results.push((target, domain));
        }
        if projection.work == 0 {
            break;
        }
    }
    results
}

impl Projection<'_> {
    fn charge(&mut self, amount: usize) -> Option<()> {
        match self.work.checked_sub(amount) {
            Some(remaining) => {
                self.work = remaining;
                Some(())
            }
            None => {
                self.work = 0;
                None
            }
        }
    }

    fn combine(
        &mut self,
        left: &UcpValueDomain,
        right: &UcpValueDomain,
        op: fn(BigInt, BigInt) -> BigInt,
    ) -> Option<UcpValueDomain> {
        fn size(domain: &UcpValueDomain) -> usize {
            match domain {
                UcpValueDomain::Exact(_) => 1,
                UcpValueDomain::FiniteSet(values) => values.len(),
            }
        }
        self.charge(size(left).checked_mul(size(right))?)?;
        combine_domain_values(left, right, self.modulus, op)
    }

    fn split(&mut self, expr: &UcpExpr, target: &CellId) -> Option<AffineCover> {
        self.charge(1)?;
        let zero = UcpValueDomain::exact(0.into());
        match expr {
            UcpExpr::Var(cell) if cell == target => Some(AffineCover {
                coefficient: UcpValueDomain::exact(1.into()),
                remainder: zero,
            }),
            UcpExpr::Var(cell) => Some(AffineCover {
                coefficient: zero,
                remainder: finite_domain_from_values(
                    domain_values(self.values.domain(cell)?),
                    self.modulus,
                )?,
            }),
            UcpExpr::Const(scalar) => Some(AffineCover {
                coefficient: zero,
                remainder: finite_domain_from_values([scalar.as_known()?], self.modulus)?,
            }),
            UcpExpr::Neg(inner) => {
                let inner = self.split(inner, target)?;
                self.scale(inner, (-1).into())
            }
            UcpExpr::Scale(inner, scalar) => match scalar {
                UcpScalar::Zero => Some(AffineCover {
                    coefficient: zero.clone(),
                    remainder: zero,
                }),
                _ => {
                    let inner = self.split(inner, target)?;
                    self.scale(inner, scalar.as_known()?)
                }
            },
            UcpExpr::Add(left, right) => {
                let left = self.split(left, target)?;
                let right = self.split(right, target)?;
                Some(AffineCover {
                    coefficient: self
                        .combine(&left.coefficient, &right.coefficient, |a, b| a + b)?,
                    remainder: self.combine(&left.remainder, &right.remainder, |a, b| a + b)?,
                })
            }
            UcpExpr::Mul(left, right) => {
                let left = self.split(left, target)?;
                let right = self.split(right, target)?;
                // Csak akkor szoroz affin alakokat, ha az egyik tényező célcellabeli együtthatója nulla.
                // A cél két előfordulásából származó négyzetes tagot nem hagyja el.
                let (dependent, independent) = if left.coefficient == zero {
                    (right, left.remainder)
                } else if right.coefficient == zero {
                    (left, right.remainder)
                } else {
                    return None;
                };
                Some(AffineCover {
                    coefficient: self
                        .combine(&dependent.coefficient, &independent, |a, b| a * b)?,
                    remainder: self.combine(&dependent.remainder, &independent, |a, b| a * b)?,
                })
            }
        }
    }

    fn scale(&mut self, inner: AffineCover, scalar: BigInt) -> Option<AffineCover> {
        let scalar = finite_domain_from_values([scalar], self.modulus)?;
        Some(AffineCover {
            coefficient: self.combine(&inner.coefficient, &scalar, |a, b| a * b)?,
            remainder: self.combine(&inner.remainder, &scalar, |a, b| a * b)?,
        })
    }

    fn project(
        &mut self,
        expr: &UcpExpr,
        rhs: &UcpValueDomain,
        target: &CellId,
    ) -> Option<UcpValueDomain> {
        let cover = self.split(expr, target)?;
        let numerators = self.combine(rhs, &cover.remainder, |a, b| a - b)?;
        let coefficients = domain_values(&cover.coefficient);
        let numerators = domain_values(&numerators);
        self.charge(coefficients.len().checked_mul(numerators.len())?)?;
        if coefficients.len().saturating_mul(numerators.len()) > super::MAX_FINITE_DOMAIN_SIZE {
            return None;
        }
        let mut candidates = Vec::new();
        for coefficient in coefficients {
            // Egyetlen lehetséges nulla vagy nem invertálható együttható is az egész vetítés kihagyását kéri.
            // Ilyen ág tetszőleges célértéket megengedhet; az ág eldobása alulbecslést okozhatna.
            let inverse = match self.modulus {
                Some(p) => Some(mod_inverse(&coefficient, p)?),
                None if coefficient == BigInt::from(0) => return None,
                None => None,
            };
            for numerator in &numerators {
                candidates.push(match &inverse {
                    Some(inverse) => normalize_value(numerator * inverse, self.modulus)?,
                    None => solve_linear_value(numerator, &coefficient, None)?,
                });
            }
        }
        finite_domain_from_values(candidates, self.modulus)
    }
}

#[cfg(test)]
#[path = "tests/finite_projection_tests.rs"]
mod tests;
