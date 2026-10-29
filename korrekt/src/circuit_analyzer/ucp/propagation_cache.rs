//! Egy propagációs futáson belül újrahasznosítja a változatlan bemenetű kifejezések eredményét.
//! A feltételes ágak is csak azonos domainek és teljességi jelölések mellett kapnak találatot.

use super::super::{
    cell::CellId,
    expr::UcpExpr,
    profiling,
    value::{
        expression_domain, expression_domain_with_modulus, infer_value_domains_from_zero_equation,
        infer_value_domains_from_zero_equation_with_modulus, LinearDomains, UcpValueDomain,
        UcpValueFacts,
    },
};
use num_bigint::BigInt;
use std::collections::BTreeSet;

const MAX_EXPRESSIONS: usize = 1024;
const MAX_STORED_VALUES: usize = 65_536;
const MAX_ENTRY_VALUES: usize = 4096;

type Signature = Vec<(CellId, Option<UcpValueDomain>, bool)>;

struct Entry<T> {
    signature: Signature,
    result: T,
    weight: usize,
}

struct Memo<T> {
    entries: Vec<Option<Entry<T>>>,
    weight: usize,
}

fn domain_size(domain: &UcpValueDomain) -> usize {
    match domain {
        UcpValueDomain::Exact(_) => 1,
        UcpValueDomain::FiniteSet(values) => values.len(),
    }
}

impl<T: Clone> Memo<T> {
    fn new(count: usize) -> Self {
        Self {
            entries: (0..count).map(|_| None).collect(),
            weight: 0,
        }
    }

    fn get(&self, index: usize, cells: &[CellId], values: &UcpValueFacts) -> Option<T> {
        let entry = self.entries.get(index)?.as_ref()?;
        let same = cells.len() == entry.signature.len()
            && cells
                .iter()
                .zip(&entry.signature)
                .all(|(cell, (cached_cell, domain, complete))| {
                    cached_cell == cell
                        && domain.as_ref() == values.domain(cell)
                        && *complete == values.domain_is_complete(cell)
                });
        if same {
            profiling::count("expression_cache.hit");
            Some(entry.result.clone())
        } else {
            None
        }
    }

    fn store(
        &mut self,
        index: usize,
        cells: &[CellId],
        values: &UcpValueFacts,
        result: &T,
        output_values: usize,
    ) {
        let Some(slot) = self.entries.get_mut(index) else {
            return;
        };
        if let Some(previous) = slot.take() {
            self.weight -= previous.weight;
        }
        let weight = cells.len()
            + output_values
            + cells
                .iter()
                .filter_map(|cell| values.domain(cell))
                .map(domain_size)
                .sum::<usize>();
        if weight > MAX_ENTRY_VALUES || self.weight.saturating_add(weight) > MAX_STORED_VALUES {
            profiling::count("expression_cache.capacity_skip");
            return;
        }
        self.weight += weight;
        *slot = Some(Entry {
            signature: cells
                .iter()
                .map(|cell| {
                    (
                        cell.clone(),
                        values.domain(cell).cloned(),
                        values.domain_is_complete(cell),
                    )
                })
                .collect(),
            result: result.clone(),
            weight,
        });
    }
}

pub(super) struct PropagationCache<'a> {
    expressions: &'a [UcpExpr],
    modulus: Option<&'a BigInt>,
    dependencies: Vec<Vec<CellId>>,
    inferences: Memo<Vec<(CellId, UcpValueDomain)>>,
    evaluations: Memo<Option<UcpValueDomain>>,
    linear_domains: Option<LinearDomains>,
}

impl<'a> PropagationCache<'a> {
    pub fn new(expressions: &'a [UcpExpr], modulus: Option<&'a BigInt>) -> Self {
        Self::with_capacity(expressions, modulus, MAX_EXPRESSIONS)
    }

    pub(super) fn with_capacity(
        expressions: &'a [UcpExpr],
        modulus: Option<&'a BigInt>,
        capacity: usize,
    ) -> Self {
        let dependencies: Vec<_> = expressions
            .iter()
            .take(capacity.min(MAX_EXPRESSIONS))
            .map(|expr| {
                fn collect(expr: &UcpExpr, cells: &mut BTreeSet<CellId>) {
                    match expr {
                        UcpExpr::Var(cell) => {
                            cells.insert(cell.clone());
                        }
                        UcpExpr::Const(_) => {}
                        UcpExpr::Neg(inner) | UcpExpr::Scale(inner, _) => collect(inner, cells),
                        UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
                            collect(left, cells);
                            collect(right, cells);
                        }
                    }
                }
                let mut cells = BTreeSet::new();
                collect(expr, &mut cells);
                cells.into_iter().collect()
            })
            .collect();
        Self {
            expressions,
            modulus,
            inferences: Memo::new(dependencies.len()),
            evaluations: Memo::new(dependencies.len()),
            dependencies,
            linear_domains: None,
        }
    }

    pub fn prepare_relations(&mut self, values: &UcpValueFacts) {
        if self.linear_domains.is_none() {
            if let Some(modulus) = self.modulus.filter(|p| **p > BigInt::from(1)) {
                self.linear_domains = Some(LinearDomains::new(self.expressions, values, modulus));
            }
        }
    }

    pub fn infer_relations(&self, values: &UcpValueFacts) -> (Vec<(CellId, UcpValueDomain)>, bool) {
        match (&self.linear_domains, self.modulus) {
            (Some(relations), Some(modulus)) => relations.infer(values, modulus),
            _ => (Vec::new(), false),
        }
    }

    pub fn infer(&mut self, index: usize, values: &UcpValueFacts) -> Vec<(CellId, UcpValueDomain)> {
        let cells = self.dependencies.get(index);
        if let Some(result) = cells.and_then(|cells| self.inferences.get(index, cells, values)) {
            return result;
        }
        profiling::count("expression_cache.inference_miss");
        let expr = &self.expressions[index];
        let result = match self.modulus {
            Some(modulus) => {
                infer_value_domains_from_zero_equation_with_modulus(expr, values, modulus)
            }
            None => infer_value_domains_from_zero_equation(expr, values),
        };
        if let Some(cells) = cells {
            let output_values = result.iter().map(|(_, domain)| domain_size(domain)).sum();
            self.inferences
                .store(index, cells, values, &result, output_values);
        }
        result
    }

    pub fn evaluate(&mut self, index: usize, values: &UcpValueFacts) -> Option<UcpValueDomain> {
        let cells = self.dependencies.get(index);
        if let Some(result) = cells.and_then(|cells| self.evaluations.get(index, cells, values)) {
            return result;
        }
        profiling::count("expression_cache.evaluation_miss");
        let expr = &self.expressions[index];
        let result = match self.modulus {
            Some(modulus) => expression_domain_with_modulus(expr, values, modulus),
            None => expression_domain(expr, values),
        };
        if let Some(cells) = cells {
            self.evaluations.store(
                index,
                cells,
                values,
                &result,
                result.as_ref().map_or(0, domain_size),
            );
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expression_cache_tracks_domains_completeness_and_unrelated_cells() {
        let canonical = |mut entries: Vec<(CellId, UcpValueDomain)>| {
            entries.sort_by(|a, b| a.0.cmp(&b.0));
            entries
        };
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let expressions = [UcpExpr::add(
            UcpExpr::var(x.clone()),
            UcpExpr::neg(UcpExpr::var(y.clone())),
        )];
        let modulus = BigInt::from(97);
        let mut cache = PropagationCache::new(&expressions, Some(&modulus));
        let mut values = UcpValueFacts::new();
        let domain = UcpValueDomain::finite_set([1.into(), 2.into()]).unwrap();
        values.mark_domain(y.clone(), domain.clone());
        let first = cache.infer(0, &values);
        assert_eq!(
            first,
            infer_value_domains_from_zero_equation_with_modulus(&expressions[0], &values, &modulus)
        );
        values.mark_known(CellId::advice(99, 99), 42.into());
        assert_eq!(cache.infer(0, &values), first);
        values.mark_domain(x.clone(), domain);
        let _ = cache.infer(0, &values);
        values
            .mark_complete_from_samples(&x, &[1.into(), 2.into()].into(), &modulus)
            .unwrap();
        assert_eq!(
            cache.infer(0, &values),
            infer_value_domains_from_zero_equation_with_modulus(&expressions[0], &values, &modulus)
        );
        let hypothetical = values.for_hypothetical_reasoning();
        assert_eq!(
            canonical(cache.infer(0, &hypothetical)),
            canonical(infer_value_domains_from_zero_equation_with_modulus(
                &expressions[0],
                &hypothetical,
                &modulus
            ))
        );
        for n in [1, 2, -1] {
            let mut changed = UcpValueFacts::new();
            changed.mark_known(x.clone(), n.into());
            changed.mark_known(y.clone(), 1.into());
            assert_eq!(
                cache.evaluate(0, &changed),
                expression_domain_with_modulus(&expressions[0], &changed, &modulus)
            );
        }
    }

    #[test]
    fn expression_cache_capacity_skips_storage_without_truncation() {
        let cell = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();
        values.mark_known(cell.clone(), 7.into());
        let mut memo = Memo::<Vec<i32>>::new(1);
        memo.store(
            0,
            &[cell.clone()],
            &values,
            &vec![1, 2],
            MAX_ENTRY_VALUES + 1,
        );
        assert!(memo.get(0, &[cell.clone()], &values).is_none());
        assert_eq!(memo.weight, 0);
        memo.store(0, &[cell.clone()], &values, &vec![1, 2], 2);
        assert!(memo.get(0, &[], &values).is_none());
        let other = CellId::advice(1, 0);
        values.mark_known(other.clone(), 7.into());
        assert!(memo.get(0, &[other], &values).is_none());
        assert_eq!(memo.get(0, &[cell], &values), Some(vec![1, 2]));
    }
}
