//! A szorzatkényszerekből lehetséges premisszafeloldó jelölteket keres, kizárólag ütemezéshez.

use super::RefinementCandidate;
use crate::circuit_analyzer::ucp::{
    cell::CellId,
    expr::UcpExpr,
    extractor::UcpProblem,
    value::{
        infer_domains_from_expression_domain_with_modulus, normalize_field_value, UcpValueDomain,
        UcpValueFacts,
    },
};
use num_bigint::BigInt;
use std::collections::BTreeSet;

#[derive(Clone, Default)]
pub(super) struct RefinementPlan {
    pub priority: Vec<BigInt>,
    pub yield_after: BTreeSet<BigInt>,
    pub expected_gain: usize,
}

pub(super) fn critical_exclusions(
    candidate: &RefinementCandidate<'_>,
    problem: &UcpProblem,
    values: &UcpValueFacts,
) -> BTreeSet<BigInt> {
    let mut critical = BTreeSet::new();
    for expression in &problem.expressions {
        let mut factors = Vec::new();
        product_factors(expression, &problem.field_modulus, &mut factors);
        if factors.len() < 2 {
            continue;
        }
        for factor in factors {
            if !contains_cell(factor, candidate.cell) {
                continue;
            }
            // A tényező nullaságát csak hipotetikusan vizsgálja; a gyököt nem jegyzi be Deltába.
            for (cell, domain) in infer_domains_from_expression_domain_with_modulus(
                factor,
                &UcpValueDomain::exact(0.into()),
                values,
                &problem.field_modulus,
            ) {
                if &cell == candidate.cell {
                    if let Some(root) = domain.exact_value().and_then(|value| {
                        normalize_field_value(value.clone(), &problem.field_modulus)
                    }) {
                        if candidate.candidates.contains_key(&root) {
                            critical.insert(root);
                        }
                    }
                }
            }
        }
    }
    critical
}

fn product_factors<'a>(expr: &'a UcpExpr, modulus: &BigInt, factors: &mut Vec<&'a UcpExpr>) {
    // A korlát csak a heurisztika felismerési munkáját fogja vissza, nem az eredeti kényszereket.
    if factors.len() >= 64 {
        return;
    }
    match expr {
        UcpExpr::Mul(left, right) => {
            product_factors(left, modulus, factors);
            product_factors(right, modulus, factors);
        }
        UcpExpr::Neg(inner) => product_factors(inner, modulus, factors),
        UcpExpr::Scale(inner, scalar) if scalar.is_non_zero_with_modulus(Some(modulus)) => {
            product_factors(inner, modulus, factors);
        }
        _ => factors.push(expr),
    }
}

fn contains_cell(expr: &UcpExpr, target: &CellId) -> bool {
    match expr {
        UcpExpr::Var(cell) => cell == target,
        UcpExpr::Const(_) => false,
        UcpExpr::Neg(inner) | UcpExpr::Scale(inner, _) => contains_cell(inner, target),
        UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
            contains_cell(left, target) || contains_cell(right, target)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit_analyzer::ucp::{expr::UcpScalar, facts::UcpFacts};

    #[test]
    fn critical_roots_follow_coefficients_cell_ids_and_field_aliases() {
        for (column, row, root) in [(0, 0, 2), (7, -3, 5), (9, 12, 8), (3, 4, -1)] {
            let cell = CellId::advice(column, row);
            let factor = UcpExpr::add(
                UcpExpr::scale_by(UcpExpr::var(cell.clone()), UcpScalar::Known(3.into())),
                UcpExpr::known_constant_i64(-3 * root),
            );
            let expression =
                UcpExpr::neg(UcpExpr::mul(UcpExpr::var(CellId::advice(99, 7)), factor));
            let domain =
                UcpValueDomain::finite_set([-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9].map(BigInt::from))
                    .unwrap();
            let mut values = UcpValueFacts::new();
            values.mark_domain(cell.clone(), domain.clone());
            let before = values.clone();
            let problem = UcpProblem {
                expressions: vec![expression],
                expression_domains: vec![],
                lookups: vec![],
                initial_facts: UcpFacts::new(),
                initial_value_facts: values.clone(),
                target_cells: vec![cell.clone()],
                output_cells: vec![cell.clone()],
                witness_cells: vec![cell.clone()],
                field_modulus: 101.into(),
            };
            let candidate = RefinementCandidate {
                cell: &cell,
                candidates: super::super::canonical_candidates(&domain, &problem.field_modulus)
                    .unwrap(),
            };
            assert_eq!(
                critical_exclusions(&candidate, &problem, &values),
                [normalize_field_value(root.into(), &101.into()).unwrap()].into()
            );
            assert_eq!(values, before);
        }
    }
}
