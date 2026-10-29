//! A lookup-táblákból szükséges domaineket és teljes rendezett n-es relációkat gyűjt ki.
//! Az elkészült relációkon nem következtet; azt a lookup.rs modul végzi.
//! A nem támogatott vagy túl nagy táblát nem csonkítja, hanem kihagyja az adott kivonatot.

use super::super::{
    cell::CellKind,
    expr::UcpExpr,
    lookup::{UcpLookup, MAX_LOOKUP_ARITY},
    plonkish::{expression_to_ucp_expr_with_fixed_values, field_to_bigint},
    value::{
        infer_domains_from_expression_domain_with_modulus, UcpValueDomain, UcpValueFacts,
        MAX_FINITE_DOMAIN_SIZE,
    },
};
use super::{field_modulus, fixed_only_expression_value, region_has_advice_cell, wrap_query_rows};
use crate::circuit_analyzer::{
    analyzable::{Analyzable, AnalyzableField},
    halo2_proofs_libs::*,
};
use num_bigint::BigInt;
use std::collections::BTreeSet;

// Az egyoszlopos vetületeket a teljes reláció reprezentálhatatlansága mellett is megtartja.
//Lookup argumentekből kezdeti Delta domaineket tanul.
// A táblaoldalt a ténylegesen hozzárendelt fixed értékek véges halmazából képezi.
// Bemenetként advice cellát vagy egyszerű lineáris kifejezést, például x+1-et vagy 2*x-et is kezel.
pub fn extract_lookup_value_facts<F: AnalyzableField>(analyzable: &Analyzable<F>) -> UcpValueFacts {
    lookup_values_from_domains(
        &extract_lookup_expression_domains(analyzable),
        &field_modulus::<F>(),
    )
}

pub(super) fn lookup_values_from_domains(
    domains: &[(UcpExpr, UcpValueDomain)],
    modulus: &BigInt,
) -> UcpValueFacts {
    let mut values = UcpValueFacts::new();
    for (expr, domain) in domains {
        for (cell, domain) in
            infer_domains_from_expression_domain_with_modulus(expr, domain, &values, modulus)
        {
            if cell.kind == CellKind::Advice {
                values.mark_domain(cell, domain);
            }
        }
    }
    values
}

// Az e in Omega feltételt akkor is megőrzi, ha az operandusokhoz még nem ismer domaint.
pub fn extract_lookup_expression_domains<F: AnalyzableField>(
    analyzable: &Analyzable<F>,
) -> Vec<(UcpExpr, UcpValueDomain)> {
    let mut domains = Vec::new();

    // A táblaoldal domainjét kapcsolásonként egyszer állítja elő,
    // mert az csak a fixed oszloptól függ,
    // nem az egyes régiókban vizsgált bemeneti sortól.
    let lookup_inputs_and_domains = analyzable
        .cs
        .lookups
        .iter()
        .flat_map(|lookup| {
            lookup
                .input_expressions
                .iter()
                .zip(lookup.table_expressions.iter())
        })
        .filter_map(|(input_expr, table_expr)| {
            lookup_table_domain(table_expr, &analyzable.fixed).map(|domain| (input_expr, domain))
        })
        .collect::<Vec<_>>();

    if lookup_inputs_and_domains.is_empty() {
        return domains;
    }

    for region in &analyzable.regions {
        if !region_has_advice_cell(region) {
            continue;
        }

        let Some((region_begin, region_end)) = region.rows else {
            continue;
        };

        for absolute_row in region_begin..=region_end {
            let row = i32::try_from(absolute_row - region_begin)
                .expect("UCP local row does not fit into i32");

            for (input_expr, domain) in &lookup_inputs_and_domains {
                // A szelektorral nullává tett lookup-bemenetből nem következtet privát cellára,
                // ezért az ilyen sorhoz nem készít új UCP-kifejezést.
                if fixed_only_expression_value(input_expr, region_begin, row, &analyzable.fixed)
                    .is_some_and(|value| bool::from(value.is_zero()))
                {
                    continue;
                }

                let mut input = expression_to_ucp_expr_with_fixed_values(
                    input_expr,
                    region_begin,
                    row,
                    &analyzable.fixed,
                );

                wrap_query_rows(&mut input, analyzable.k);
                domains.push((input, domain.clone()));
            }
        }
    }

    domains
}

// A teljes táblasorokat együtt őrzi meg, hogy megtartsa az oszlopok közötti korrelációt.
// Hiányos vagy túl nagy relációból nem készít részleges, tévesen szigorú táblát.
pub(super) fn extract_lookup_relations<F: AnalyzableField>(
    analyzable: &Analyzable<F>,
) -> Vec<UcpLookup> {
    let mut relations = Vec::new();
    for lookup in &analyzable.cs.lookups {
        if lookup.input_expressions.len() < 2
            || lookup.input_expressions.len() > MAX_LOOKUP_ARITY
            || lookup.input_expressions.len() != lookup.table_expressions.len()
        {
            continue;
        }
        let columns: Option<Vec<_>> = lookup
            .table_expressions
            .iter()
            .map(|expr| {
                let Expression::Fixed(query) = expr else {
                    return None;
                };
                if query.rotation != Rotation::cur() {
                    return None;
                }
                analyzable.fixed.get(query.column_index)
            })
            .collect();
        let Some(columns) = columns else {
            continue;
        };
        if columns
            .iter()
            .any(|column| column.len() != columns[0].len())
        {
            continue;
        }
        let mut tuples = BTreeSet::new();
        let mut supported = true;
        for row in 0..columns[0].len() {
            if columns
                .iter()
                .all(|column| matches!(column[row], CellValue::Unassigned))
            {
                continue;
            }
            let tuple: Option<Vec<_>> = columns
                .iter()
                .map(|column| match &column[row] {
                    CellValue::Assigned(value) => Some(field_to_bigint(value)),
                    _ => None,
                })
                .collect();
            let Some(tuple) = tuple else {
                supported = false;
                break;
            };
            tuples.insert(tuple);
            if tuples.len() > MAX_FINITE_DOMAIN_SIZE {
                supported = false;
                break;
            }
        }
        if !supported {
            continue;
        }
        let tuples: Vec<_> = tuples.into_iter().collect();
        for region in &analyzable.regions {
            if !region_has_advice_cell(region) {
                continue;
            }
            let Some((begin, end)) = region.rows else {
                continue;
            };
            for absolute in begin..=end {
                let row = i32::try_from(absolute - begin).expect("UCP local row fits i32");
                if lookup.input_expressions.iter().all(|expr| {
                    fixed_only_expression_value(expr, begin, row, &analyzable.fixed).is_some()
                }) {
                    continue;
                }
                let inputs = lookup
                    .input_expressions
                    .iter()
                    .map(|expr| {
                        let mut input = expression_to_ucp_expr_with_fixed_values(
                            expr,
                            begin,
                            row,
                            &analyzable.fixed,
                        );
                        wrap_query_rows(&mut input, analyzable.k);
                        input
                    })
                    .collect();
                if let Some(relation) = UcpLookup::new(inputs, tuples.clone()) {
                    relations.push(relation);
                }
            }
        }
    }
    relations
}

pub(super) fn lookup_table_domain<F: AnalyzableField>(
    expr: &Expression<F>,
    fixed_values: &[Vec<CellValue<F>>],
) -> Option<UcpValueDomain> {
    let Expression::Fixed(query) = expr else {
        return None;
    };

    // A táblaoszlopot csak Rotation::cur() rotációval fogadja el;
    // más fixed kifejezésből nem készít tartománydomaint.
    if query.rotation != Rotation::cur() {
        return None;
    }

    let column_values = fixed_values.get(query.column_index)?;
    let mut domain_values = BTreeSet::new();

    for value in column_values {
        match value {
            CellValue::Assigned(value) => {
                domain_values.insert(field_to_bigint(value));
                // Csonkított táblavetületet nem tart meg; a nagy domaint az SMT-re hagyja.
                if domain_values.len() > MAX_FINITE_DOMAIN_SIZE {
                    return None;
                }
            }
            // Csak ténylegesen hozzárendelt táblaértéket vesz fel a domainbe.
            // Unassigned bejegyzésből nem tanul nullaértéket.
            CellValue::Unassigned => {}
            // Poison bejegyzésnél elutasítja a domainkivonást.
            CellValue::Poison(_) => return None,
        }
    }

    UcpValueDomain::finite_set(domain_values)
}
