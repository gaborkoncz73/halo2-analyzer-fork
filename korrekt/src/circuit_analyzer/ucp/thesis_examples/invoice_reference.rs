//! A kis bemeneti térben közvetlen egészszám-aritmetikával számol referenciát.
//! A kapott megoldásokat nem adja át az UCP-nek vagy az SMT-keresésnek premisszaként.

use super::invoice_circuit::*;
use crate::circuit_analyzer::ucp::cell::CellId;
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn supplier_pairs(quantity: u64) -> Vec<(u64, u64)> {
    (0..=60)
        .step_by(2)
        .filter_map(|u| {
            quantity
                .checked_sub(u)
                .filter(|v| *v <= 63 && v % 3 == 0)
                .map(|v| (u, v))
        })
        .collect()
}

fn dot(left: [u64; 4], right: [u64; 4]) -> u64 {
    left.into_iter().zip(right).map(|(a, b)| a * b).sum()
}

// Egy rögzített lineáris megfigyelésből a negyedik mennyiséget számítja ki,
// majd a többi feltételt közvetlenül ellenőrzi; így nem járja be a teljes 128^4 teret.
pub(super) fn cart_vectors(mask: u8) -> Vec<[u64; 4]> {
    assert!(mask & 3 != 0);
    let mut result = Vec::new();
    for a in 0..128 {
        if supplier_pairs(a).is_empty() {
            continue;
        }
        for b in 0..128 {
            for c in 0..128 {
                let partial = if mask & 1 != 0 {
                    a + b + c
                } else {
                    500 * a + 1000 * b + 700 * c
                };
                let total = if mask & 1 != 0 {
                    OBSERVED[0]
                } else {
                    OBSERVED[1]
                };
                let divisor = if mask & 1 != 0 { 1 } else { 200 };
                let Some(rest) = total.checked_sub(partial) else {
                    continue;
                };
                if rest % divisor != 0 || rest / divisor >= 128 {
                    continue;
                }
                let quantities = [a, b, c, rest / divisor];
                let weight = dot(quantities, WEIGHTS);
                if mask & 2 != 0 && weight != OBSERVED[1] {
                    continue;
                }
                if mask & 4 != 0 && dot(quantities, POINTS) != OBSERVED[2] {
                    continue;
                }
                let Some(shipping) = SHIPPING.iter().find(|s| s[1] <= weight && weight <= s[2])
                else {
                    continue;
                };
                if mask & 8 != 0 {
                    let subtotal = dot(quantities, PRICES);
                    let matches = COUPONS.into_iter().any(|rate| {
                        let base = subtotal - subtotal * rate / 100 + 17;
                        base + base * 20 / 100 + shipping[3] == OBSERVED[3]
                    });
                    if !matches {
                        continue;
                    }
                }
                result.push(quantities);
            }
        }
    }
    result
}

pub(super) fn full_witnesses() -> Vec<CartWitness> {
    cart_vectors(ALL)
        .into_iter()
        .flat_map(|quantities| {
            (0..COUPONS.len()).flat_map(move |coupon| {
                supplier_pairs(quantities[0])
                    .into_iter()
                    .filter_map(move |(supplier_u, _)| {
                        let witness = CartWitness {
                            quantities,
                            coupon,
                            supplier_u,
                        };
                        (witness.observations() == OBSERVED).then_some(witness)
                    })
            })
        })
        .collect()
}

pub(super) fn projections() -> BTreeMap<CellId, BTreeSet<BigInt>> {
    let mut values = BTreeMap::<CellId, BTreeSet<BigInt>>::new();
    for witness in full_witnesses() {
        let rows = witness.rows();
        for cell in targets() {
            values
                .entry(cell.clone())
                .or_default()
                .insert(rows[cell.row as usize][cell.column].into());
        }
    }
    values
}
