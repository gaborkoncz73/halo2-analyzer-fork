//! A lineáris összefüggéseket véges domainekkel és ideiglenes egész intervallumokkal kapcsolja össze.
//! Az intervallumokat nem tárolja Deltában, és a jelöltekhez nem állít megvalósíthatóságot.

use super::{
    domain_values, linearize_field_system, mod_field, mod_inverse, normalize_field_value, CellId,
    LinearExpr, UcpExpr, UcpValueDomain, UcpValueFacts, MAX_FINITE_DOMAIN_SIZE,
};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

// A keretek csak az új következtetés munkáját korlátozzák; kimaradó sort vagy jelöltet nem tekint kizártnak.
const MAX_ROWS: usize = 256;
const MAX_COLUMNS: usize = 128;
const MAX_INTERVAL_ROUNDS: usize = 16;
const MAX_ROW_COMBINATIONS: usize = 4096;
const MAX_SUPPORT_CHECKS: usize = 16_384;

#[derive(Clone)]
struct Row {
    constant: BigInt,
    terms: Vec<(CellId, BigInt)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Interval {
    lo: BigInt,
    hi: BigInt,
}

pub(crate) struct LinearDomains {
    rows: Vec<Row>,
    cells: Vec<CellId>,
}

fn balanced(value: BigInt, modulus: &BigInt) -> BigInt {
    let value = mod_field(value, modulus);
    if &value * 2 > *modulus {
        value - modulus
    } else {
        value
    }
}

fn gcd(mut a: BigInt, mut b: BigInt) -> BigInt {
    while b != BigInt::from(0) {
        let r = a % &b;
        a = b;
        b = r;
    }
    if a < BigInt::from(0) {
        -a
    } else {
        a
    }
}

fn normalize_row(row: &mut [BigInt], modulus: &BigInt) {
    for value in row.iter_mut() {
        *value = balanced(value.clone(), modulus);
    }
    let divisor = row.iter().fold(BigInt::from(0), |d, v| gcd(d, v.clone()));
    // Csak invertálható közös tényezővel oszt, így a kongruencia következménye megmarad.
    if divisor > BigInt::from(1) && mod_inverse(&divisor, modulus).is_some() {
        for value in row {
            *value /= &divisor;
        }
    }
}

fn floor_div(a: &BigInt, b: &BigInt) -> BigInt {
    let q = a / b;
    if a % b < BigInt::from(0) {
        q - 1
    } else {
        q
    }
}

fn ceil_div(a: &BigInt, b: &BigInt) -> BigInt {
    -floor_div(&-a, b)
}

impl LinearDomains {
    pub(crate) fn new(expressions: &[UcpExpr], values: &UcpValueFacts, modulus: &BigInt) -> Self {
        let _profile = crate::circuit_analyzer::ucp::profiling::scope("ucp.linear_projection");
        let mut equations: Vec<LinearExpr> = expressions
            .iter()
            .filter_map(|expr| linearize_field_system(expr, values))
            .take(MAX_ROWS)
            .collect();
        let mut frequency = BTreeMap::<CellId, usize>::new();
        for equation in &mut equations {
            equation.constant = balanced(equation.constant.clone(), modulus);
            for coefficient in equation.terms.values_mut() {
                *coefficient = balanced(coefficient.clone(), modulus);
            }
            equation.terms.retain(|_, c| *c != BigInt::from(0));
            for cell in equation.terms.keys() {
                *frequency.entry(cell.clone()).or_default() += 1;
            }
        }
        let mut columns: Vec<_> = frequency.keys().cloned().collect();
        // A ritkán előforduló segédcellákat előbb eliminálja; a sorrend csak a következtetés erejét érinti.
        columns.sort_by_key(|cell| (frequency[cell], cell.clone()));
        let mut rows: Vec<Row> = equations
            .iter()
            .map(|e| {
                let mut terms: Vec<_> = e
                    .terms
                    .iter()
                    .map(|(c, a)| (c.clone(), a.clone()))
                    .collect();
                terms.sort_by(|a, b| a.0.cmp(&b.0));
                Row {
                    constant: e.constant.clone(),
                    terms,
                }
            })
            .collect();
        if columns.len() <= MAX_COLUMNS {
            let n = columns.len();
            let mut matrix: Vec<Vec<BigInt>> = equations
                .iter()
                .map(|e| {
                    columns
                        .iter()
                        .map(|c| e.terms.get(c).cloned().unwrap_or_default())
                        .chain([e.constant.clone()])
                        .collect()
                })
                .collect();
            let mut rank = 0;
            for column in 0..n {
                let pivot = (rank..matrix.len())
                    .filter(|&r| matrix[r][column] != BigInt::from(0))
                    .min_by_key(|&r| {
                        (
                            matrix[r][column] != BigInt::from(1)
                                && matrix[r][column] != BigInt::from(-1),
                            matrix[r].iter().filter(|v| **v != BigInt::from(0)).count(),
                        )
                    });
                let Some(pivot) = pivot else {
                    continue;
                };
                matrix.swap(rank, pivot);
                let pivot_row = matrix[rank].clone();
                for (r, row) in matrix.iter_mut().enumerate() {
                    if r == rank || row[column] == BigInt::from(0) {
                        continue;
                    }
                    let factor = row[column].clone();
                    for c in 0..=n {
                        row[c] = &pivot_row[column] * &row[c] - &factor * &pivot_row[c];
                    }
                    normalize_row(row, modulus);
                }
                rank += 1;
            }
            rows.extend(matrix.into_iter().map(|row| {
                Row {
                    constant: row[n].clone(),
                    terms: columns
                        .iter()
                        .cloned()
                        .zip(row)
                        .filter(|(_, c)| *c != BigInt::from(0))
                        .collect(),
                }
            }));
        }
        Self {
            rows,
            cells: frequency.into_keys().collect(),
        }
    }

    pub(crate) fn infer(
        &self,
        values: &UcpValueFacts,
        modulus: &BigInt,
    ) -> (Vec<(CellId, UcpValueDomain)>, bool) {
        let _profile = crate::circuit_analyzer::ucp::profiling::scope("ucp.relational_domains");
        let mut bounds: BTreeMap<_, _> = self
            .cells
            .iter()
            .map(|cell| {
                let interval = match values.domain(cell) {
                    Some(domain) => {
                        let entries: BTreeSet<_> = domain_values(domain)
                            .into_iter()
                            .map(|v| mod_field(v, modulus))
                            .collect();
                        Interval {
                            lo: entries.first().unwrap().clone(),
                            hi: entries.last().unwrap().clone(),
                        }
                    }
                    None => Interval {
                        lo: 0.into(),
                        hi: modulus - 1,
                    },
                };
                (cell.clone(), interval)
            })
            .collect();
        let mut learned = values.clone();
        for _ in 0..MAX_INTERVAL_ROUNDS {
            let mut changed = false;
            for row in &self.rows {
                match row.contract(&mut bounds, modulus) {
                    Some(update) => changed |= update,
                    None => return (Vec::new(), true),
                }
            }
            if !changed {
                break;
            }
        }
        for (cell, interval) in &bounds {
            let candidates = match learned.domain(cell) {
                Some(domain) => domain_values(domain)
                    .into_iter()
                    .filter(|v| {
                        let v = mod_field(v.clone(), modulus);
                        v >= interval.lo && v <= interval.hi
                    })
                    .collect::<Vec<_>>(),
                None if &interval.hi - &interval.lo < BigInt::from(MAX_FINITE_DOMAIN_SIZE) => {
                    let mut entries = Vec::new();
                    let mut value = interval.lo.clone();
                    while value <= interval.hi {
                        entries.push(
                            normalize_field_value(value.clone(), modulus)
                                .unwrap_or_else(|| value.clone()),
                        );
                        value += 1;
                    }
                    entries
                }
                None => continue,
            };
            if candidates.is_empty() {
                return (Vec::new(), true);
            }
            if let Some(domain) = UcpValueDomain::finite_set(candidates) {
                learned.mark_domain(cell.clone(), domain);
            }
        }
        let mut allowance = MAX_SUPPORT_CHECKS;
        for row in &self.rows {
            if !row.support(&mut learned, &bounds, modulus, &mut allowance) {
                return (Vec::new(), true);
            }
        }
        let inferences = self
            .cells
            .iter()
            .filter_map(|cell| {
                let domain = learned.domain(cell)?;
                (values.domain(cell) != Some(domain)).then(|| (cell.clone(), domain.clone()))
            })
            .collect();
        (inferences, false)
    }
}

impl Row {
    fn contract(&self, bounds: &mut BTreeMap<CellId, Interval>, modulus: &BigInt) -> Option<bool> {
        let ranges: Vec<_> = self
            .terms
            .iter()
            .map(|(c, a)| {
                let b = &bounds[c];
                if a >= &BigInt::from(0) {
                    (&b.lo * a, &b.hi * a)
                } else {
                    (&b.hi * a, &b.lo * a)
                }
            })
            .collect();
        let lo = ranges
            .iter()
            .fold(self.constant.clone(), |s, (lo, _)| s + lo);
        let hi = ranges
            .iter()
            .fold(self.constant.clone(), |s, (_, hi)| s + hi);
        let first = ceil_div(&lo, modulus);
        let last = floor_div(&hi, modulus);
        if first > last {
            return None;
        }
        // Több lehetséges körbefordulásnál nem alkalmaz egész egyenletként érvénytelen szűkítést.
        if first != last {
            return Some(false);
        }
        let total = first * modulus;
        let mut changed = false;
        for ((cell, coefficient), (part_lo, part_hi)) in self.terms.iter().zip(ranges) {
            let numerator_lo = &total - (&hi - part_hi);
            let numerator_hi = &total - (&lo - part_lo);
            let (candidate_lo, candidate_hi) = if coefficient > &BigInt::from(0) {
                (
                    ceil_div(&numerator_lo, coefficient),
                    floor_div(&numerator_hi, coefficient),
                )
            } else {
                (
                    ceil_div(&-numerator_hi, &-coefficient),
                    floor_div(&-numerator_lo, &-coefficient),
                )
            };
            let interval = bounds.get_mut(cell).unwrap();
            let next = Interval {
                lo: interval.lo.clone().max(candidate_lo),
                hi: interval.hi.clone().min(candidate_hi),
            };
            if next.lo > next.hi {
                return None;
            }
            changed |= next != *interval;
            *interval = next;
        }
        Some(changed)
    }

    fn support(
        &self,
        values: &mut UcpValueFacts,
        bounds: &BTreeMap<CellId, Interval>,
        modulus: &BigInt,
        allowance: &mut usize,
    ) -> bool {
        let mut choices: Vec<_> = self
            .terms
            .iter()
            .enumerate()
            .filter_map(|(target, (_, coefficient))| {
                let mut count = 1usize;
                for (i, (cell, _)) in self.terms.iter().enumerate() {
                    if i != target {
                        let size = match values.domain(cell)? {
                            UcpValueDomain::Exact(_) => 1,
                            UcpValueDomain::FiniteSet(entries) => entries.len(),
                        };
                        count = count.checked_mul(size)?;
                        if count > MAX_ROW_COMBINATIONS || count > *allowance {
                            return None;
                        }
                    }
                }
                (count <= MAX_ROW_COMBINATIONS && count <= *allowance).then_some((
                    count,
                    target,
                    coefficient,
                ))
            })
            .collect();
        choices.sort_by_key(|(count, target, _)| (*count, *target));
        let Some((count, target, coefficient)) = choices.first() else {
            return true;
        };
        let Some(inverse) = mod_inverse(coefficient, modulus) else {
            return true;
        };
        *allowance -= count;
        let others: Vec<_> = self
            .terms
            .iter()
            .enumerate()
            .filter(|(i, _)| i != target)
            .map(|(i, (cell, _))| (i, domain_values(values.domain(cell).unwrap())))
            .collect();
        let mut supported: Vec<BTreeSet<BigInt>> = vec![BTreeSet::new(); self.terms.len()];
        let mut assignment = vec![BigInt::from(0); self.terms.len()];
        let target_cell = &self.terms[*target].0;
        let target_entries: Option<BTreeMap<BigInt, BigInt>> =
            values.domain(target_cell).map(|domain| {
                domain_values(domain)
                    .into_iter()
                    .map(|v| (mod_field(v.clone(), modulus), v))
                    .collect()
            });
        for ordinal in 0..*count {
            let mut ordinal = ordinal;
            let mut sum = self.constant.clone();
            for (i, entries) in &others {
                let value = &entries[ordinal % entries.len()];
                ordinal /= entries.len();
                assignment[*i] = value.clone();
                sum += &self.terms[*i].1 * value;
            }
            let candidate = mod_field(-sum * &inverse, modulus);
            let cell = &self.terms[*target].0;
            let interval = &bounds[cell];
            if candidate < interval.lo || candidate > interval.hi {
                continue;
            }
            // A meglévő domain reprezentánsát tartja meg: a tároló egészszámként metszi a halmazokat.
            assignment[*target] = match &target_entries {
                Some(entries) => match entries.get(&candidate) {
                    Some(v) => v.clone(),
                    None => continue,
                },
                None => normalize_field_value(candidate.clone(), modulus).unwrap_or(candidate),
            };
            for (set, value) in supported.iter_mut().zip(&assignment) {
                set.insert(value.clone());
            }
        }
        if supported.iter().any(BTreeSet::is_empty) {
            return false;
        }
        // A teljes sorvizsgálat vetületeit adja tovább; méretkorlátnál nem csonkítja a halmazt.
        for ((cell, _), candidates) in self.terms.iter().zip(supported) {
            if let Some(domain) = UcpValueDomain::finite_set(candidates) {
                values.mark_domain(cell.clone(), domain);
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(n: usize) -> UcpExpr {
        UcpExpr::var(CellId::advice(n, 0))
    }
    fn constant(n: i64) -> UcpExpr {
        UcpExpr::known_constant_i64(n)
    }
    fn scale(n: i64, expr: UcpExpr) -> UcpExpr {
        UcpExpr::mul(constant(n), expr)
    }
    fn domain(entries: impl IntoIterator<Item = i64>) -> UcpValueDomain {
        UcpValueDomain::finite_set(entries.into_iter().map(BigInt::from)).unwrap()
    }

    #[test]
    fn relational_linear_domains_preserve_every_small_modular_solution() {
        for p in [5_i64, 7, 9, 11] {
            for a in -3..=3 {
                for b in 1..=3 {
                    for rhs in 0..p {
                        let expr = UcpExpr::add(
                            UcpExpr::add(scale(a, var(0)), scale(b, var(1))),
                            constant(-rhs),
                        );
                        let mut values = UcpValueFacts::new();
                        values.mark_domain(CellId::advice(0, 0), domain(0..p.min(4)));
                        values.mark_domain(
                            CellId::advice(1, 0),
                            domain((0..p).filter(|v| v % 2 == 0)),
                        );
                        let feasible: Vec<_> = (0..p.min(4))
                            .flat_map(|x| (0..p).filter(move |y| y % 2 == 0).map(move |y| (x, y)))
                            .filter(|(x, y)| (a * x + b * y - rhs).rem_euclid(p) == 0)
                            .collect();
                        let (inferences, inconsistent) =
                            LinearDomains::new(&[expr], &values, &p.into())
                                .infer(&values, &p.into());
                        if feasible.is_empty() {
                            continue;
                        }
                        assert!(!inconsistent, "p={p}, a={a}, b={b}, rhs={rhs}");
                        for (cell, inferred) in inferences {
                            let projected: BTreeSet<_> = domain_values(&inferred)
                                .into_iter()
                                .map(|v| mod_field(v, &p.into()))
                                .collect();
                            for (x, y) in &feasible {
                                assert!(projected.contains(&BigInt::from(if cell.column == 0 {*x} else {*y})), "p={p}, a={a}, b={b}, rhs={rhs}, cell={cell}, inferred={inferred:?}, feasible={feasible:?}");
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn relational_linear_domains_eliminate_auxiliaries_in_an_underdetermined_system() {
        let expressions = [
            UcpExpr::add(var(3), scale(-3, var(0))),
            UcpExpr::add(UcpExpr::add(var(3), var(1)), constant(-13)),
            UcpExpr::add(
                UcpExpr::add(var(0), var(1)),
                UcpExpr::add(var(2), constant(-9)),
            ),
        ];
        let mut values = UcpValueFacts::new();
        for c in 0..3 {
            values.mark_domain(CellId::advice(c, 0), domain(0..8));
        }
        let (inferences, conflict) =
            LinearDomains::new(&expressions, &values, &101.into()).infer(&values, &101.into());
        assert!(!conflict);
        assert!(inferences
            .iter()
            .any(|(cell, d)| cell.column == 3 && domain_values(d).len() < 8));
        let expected: Vec<_> = (0..8)
            .flat_map(|x| (0..8).flat_map(move |y| (0..8).map(move |z| (x, y, z))))
            .filter(|(x, y, z)| 3 * x + y == 13 && x + y + z == 9)
            .collect();
        for (cell, d) in inferences {
            let entries = domain_values(&d);
            for (x, y, z) in &expected {
                assert!(entries.contains(&BigInt::from(match cell.column {
                    0 => *x,
                    1 => *y,
                    2 => *z,
                    _ => 3 * x,
                })));
            }
        }
    }

    #[test]
    fn relational_linear_domains_use_a_derived_rounding_equation_without_enumerating_large_ranges()
    {
        let mut expressions = vec![
            UcpExpr::add(
                UcpExpr::add(scale(20, var(0)), scale(-100, var(1))),
                UcpExpr::neg(var(2)),
            ),
            UcpExpr::add(UcpExpr::add(var(0), var(1)), constant(-206_948)),
        ];
        let p = BigInt::from(1_000_000_007);
        let mut values = UcpValueFacts::new();
        values.mark_domain(CellId::advice(2, 0), domain(0..100));
        // A számjegyek intervallumai nagy tartományt fognak közre, de egyetlen domaint sem csonkítanak.
        for target in 0..2 {
            let mut packed = UcpExpr::zero();
            for digit in 0..5 {
                let c = 3 + target * 5 + digit;
                values.mark_domain(CellId::advice(c, 0), domain(0..16));
                packed = UcpExpr::add(packed, scale(16_i64.pow(digit as u32), var(c)));
            }
            expressions.push(UcpExpr::add(var(target), UcpExpr::neg(packed)));
        }
        let kernel = LinearDomains::new(&expressions, &values, &p);
        let (inferences, conflict) = kernel.infer(&values, &p);
        assert!(!conflict);
        // Az intervallum is elegendő a 120*E-r=100*206948 egyenlet egyetlen E értékéhez.
        assert!(inferences
            .iter()
            .any(|(c, d)| c.column == 0 && d == &UcpValueDomain::exact(172_457.into())));
    }

    #[test]
    fn relational_linear_domains_do_not_confuse_field_aliases_or_wraparound_with_integer_equality()
    {
        let p = BigInt::from(17);
        let expressions = [UcpExpr::add(UcpExpr::add(var(0), var(1)), constant(-2))];
        let mut values = UcpValueFacts::new();
        values.mark_domain(CellId::advice(0, 0), domain([-1, 0, 1, 2, 3]));
        values.mark_domain(CellId::advice(1, 0), domain([0, 1, 2, 3, 16]));
        let (inferences, conflict) =
            LinearDomains::new(&expressions, &values, &p).infer(&values, &p);
        assert!(!conflict);
        for (cell, d) in inferences {
            let entries: BTreeSet<_> = domain_values(&d)
                .into_iter()
                .map(|v| mod_field(v, &p))
                .collect();
            assert!(entries.contains(&BigInt::from(if cell.column == 0 { 16 } else { 3 })));
        }
    }

    #[test]
    fn relational_linear_domains_skip_over_budget_joins_without_returning_partial_projections() {
        let row = Row {
            constant: 0.into(),
            terms: (0..4)
                .map(|c| (CellId::advice(c, 0), BigInt::from(1)))
                .collect(),
        };
        let mut values = UcpValueFacts::new();
        let mut bounds = BTreeMap::new();
        for c in 0..4 {
            values.mark_domain(CellId::advice(c, 0), domain(0..128));
            bounds.insert(
                CellId::advice(c, 0),
                Interval {
                    lo: 0.into(),
                    hi: 127.into(),
                },
            );
        }
        let before = values.clone();
        let mut allowance = MAX_SUPPORT_CHECKS;
        assert!(row.support(&mut values, &bounds, &1009.into(), &mut allowance));
        assert_eq!(values, before);
    }

    #[test]
    fn relational_linear_domains_coupled_rows_cover_all_solutions_after_renaming_and_reordering() {
        for p in [7_i64, 11, 13] {
            for seed in 0..24_i64 {
                for renamed in [false, true] {
                    let cell = |c| {
                        CellId::advice(
                            if renamed { 20 - c } else { c },
                            if renamed { 3 } else { 0 },
                        )
                    };
                    let coefficients = [[seed % 5 - 2, 1, 2], [1, (seed / 3) % 5 - 2, -1]];
                    let rhs = [seed % p, (3 * seed + 1) % p];
                    let mut expressions: Vec<_> = coefficients
                        .iter()
                        .zip(rhs)
                        .map(|(coefficients, rhs)| {
                            coefficients
                                .iter()
                                .enumerate()
                                .fold(constant(-rhs), |e, (c, a)| {
                                    UcpExpr::add(e, scale(*a, UcpExpr::var(cell(c))))
                                })
                        })
                        .collect();
                    if renamed {
                        expressions.reverse();
                    }
                    let mut values = UcpValueFacts::new();
                    for c in 0..2 {
                        values.mark_domain(cell(c), domain(0..4));
                    }
                    let feasible: Vec<_> = (0..4)
                        .flat_map(|x| (0..4).flat_map(move |y| (0..p).map(move |z| [x, y, z])))
                        .filter(|assignment| {
                            coefficients.iter().zip(rhs).all(|(a, b)| {
                                (a.iter().zip(assignment).map(|(a, x)| a * x).sum::<i64>() - b)
                                    .rem_euclid(p)
                                    == 0
                            })
                        })
                        .collect();
                    if feasible.is_empty() {
                        continue;
                    }
                    let (inferences, conflict) =
                        LinearDomains::new(&expressions, &values, &p.into())
                            .infer(&values, &p.into());
                    assert!(!conflict, "p={p}, seed={seed}");
                    for (c, d) in inferences {
                        let index = (0..3).find(|i| cell(*i) == c).unwrap();
                        let projected: BTreeSet<_> = domain_values(&d)
                            .into_iter()
                            .map(|v| mod_field(v, &p.into()))
                            .collect();
                        for assignment in &feasible {
                            assert!(
                                projected.contains(&BigInt::from(assignment[index])),
                                "p={p}, seed={seed}, cell={c}, domain={d:?}"
                            );
                        }
                    }
                }
            }
        }
    }
}
