//! Demonstration tests for the UCP prototype.
//!
//! These tests are intentionally small and readable. They are not meant to
//! stress every corner case; they show the main paper-style ideas in isolation:
//! K grows by uniqueness propagation, Delta grows by value/domain inference,
//! and the larger rules can then fire from those facts.

use super::{
    cell::CellId,
    choose_var::choose_query_cell,
    engine::analyze_expressions_with_values_and_modulus,
    expr::UcpExpr,
    facts::UcpFacts,
    value::{UcpValueDomain, UcpValueFacts},
};
use num_bigint::BigInt;
use std::collections::HashSet;

fn modulus() -> BigInt {
    BigInt::from(101)
}

fn add3(left: UcpExpr, middle: UcpExpr, right: UcpExpr) -> UcpExpr {
    UcpExpr::add(UcpExpr::add(left, middle), right)
}

fn product(y: &CellId, x: &CellId, root: i64) -> UcpExpr {
    UcpExpr::mul(
        UcpExpr::var(y.clone()),
        UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(-root)),
    )
}

fn sorted_unique_cells(result: &super::engine::UcpResult) -> Vec<CellId> {
    let mut cells: Vec<CellId> = result.facts.unique_cells().iter().cloned().collect();
    cells.sort();
    cells
}

// Demo 1:
// Egy sima assignment chain:
//   x + public - 5 = 0
//   y - x - 1 = 0
//   z - y - 1 = 0
//
// Kezdetben csak a public input van K-ban. Az Assign szabály először x-et,
// majd y-t, majd z-t teszi unique-ká. Ez a legegyszerűbb "lavina" példa.
#[test]
fn demo_assign_chain_grows_k_step_by_step() {
    let public = CellId::instance(0, 0);
    let x = CellId::advice(0, 0);
    let y = CellId::advice(1, 0);
    let z = CellId::advice(2, 0);

    let expressions = vec![
        add3(
            UcpExpr::var(x.clone()),
            UcpExpr::var(public.clone()),
            UcpExpr::known_constant_i64(-5),
        ),
        add3(
            UcpExpr::var(y.clone()),
            UcpExpr::neg(UcpExpr::var(x.clone())),
            UcpExpr::known_constant_i64(-1),
        ),
        add3(
            UcpExpr::var(z.clone()),
            UcpExpr::neg(UcpExpr::var(y.clone())),
            UcpExpr::known_constant_i64(-1),
        ),
    ];
    let facts = UcpFacts::from_iter([public.clone()]);

    let result = analyze_expressions_with_values_and_modulus(
        &expressions,
        facts,
        UcpValueFacts::new(),
        &modulus(),
    );

    println!("demo_assign_chain K={:?}", sorted_unique_cells(&result));

    assert!(result.facts.is_unique(&public));
    assert!(result.facts.is_unique(&x));
    assert!(result.facts.is_unique(&y));
    assert!(result.facts.is_unique(&z));
    assert!(result.all_expressions_unique());
}

// Demo 2:
// Boolean domainek + Base-Conv együtt:
//   b0 * (b0 - 1) = 0      => Delta(b0) = {0, 1}
//   b1 * (b1 - 1) = 0      => Delta(b1) = {0, 1}
//   b0 + 2*b1 - x = 0
//
// Ha x unique, és a két digit domainje [0,1]-ben van, akkor a base-2 felírás
// egyértelmű, ezért b0 és b1 is unique lesz.
#[test]
fn demo_boolean_roots_enable_base_conversion() {
    let x = CellId::instance(0, 0);
    let b0 = CellId::advice(0, 0);
    let b1 = CellId::advice(1, 0);

    let boolean_b0 = UcpExpr::mul(
        UcpExpr::var(b0.clone()),
        UcpExpr::add(UcpExpr::var(b0.clone()), UcpExpr::known_constant_i64(-1)),
    );
    let boolean_b1 = UcpExpr::mul(
        UcpExpr::var(b1.clone()),
        UcpExpr::add(UcpExpr::var(b1.clone()), UcpExpr::known_constant_i64(-1)),
    );
    let base_conv = add3(
        UcpExpr::var(b0.clone()),
        UcpExpr::scale_by(
            UcpExpr::var(b1.clone()),
            super::expr::UcpScalar::known_i64(2),
        ),
        UcpExpr::neg(UcpExpr::var(x.clone())),
    );
    let expressions = vec![boolean_b0, boolean_b1, base_conv];
    let facts = UcpFacts::from_iter([x.clone()]);

    let result = analyze_expressions_with_values_and_modulus(
        &expressions,
        facts,
        UcpValueFacts::new(),
        &modulus(),
    );

    println!(
        "demo_boolean_base_conv K={:?} Delta={:?}",
        sorted_unique_cells(&result),
        result.value_facts.domains()
    );

    assert_eq!(
        result.value_facts.domain(&b0),
        Some(&UcpValueDomain::finite_set([BigInt::from(0), BigInt::from(1)]).unwrap())
    );
    assert_eq!(
        result.value_facts.domain(&b1),
        Some(&UcpValueDomain::finite_set([BigInt::from(0), BigInt::from(1)]).unwrap())
    );
    assert!(result.facts.is_unique(&b0));
    assert!(result.facts.is_unique(&b1));
}

// Demo 3:
// All-But-One-0:
//   y0 + y1 + y2 = e
//   y0 * (x - 0) = 0
//   y1 * (x - 1) = 0
//   y2 * (x - 2) = 0
//
// Ha x és e unique, akkor a három y_i is unique. Ha Delta szerint x=1 és e=7,
// akkor konkrétan y1=7, a többi y pedig 0.
#[test]
fn demo_all_but_one_learns_one_hot_values() {
    let x = CellId::instance(0, 0);
    let e = CellId::instance(1, 0);
    let y0 = CellId::advice(0, 0);
    let y1 = CellId::advice(1, 0);
    let y2 = CellId::advice(2, 0);

    let expressions = vec![
        product(&y0, &x, 0),
        product(&y1, &x, 1),
        product(&y2, &x, 2),
        add3(
            UcpExpr::var(y0.clone()),
            UcpExpr::var(y1.clone()),
            UcpExpr::add(
                UcpExpr::var(y2.clone()),
                UcpExpr::neg(UcpExpr::var(e.clone())),
            ),
        ),
    ];
    let facts = UcpFacts::from_iter([x.clone(), e.clone()]);
    let mut values = UcpValueFacts::new();
    values.mark_known(x.clone(), BigInt::from(1));
    values.mark_known(e.clone(), BigInt::from(7));

    let result =
        analyze_expressions_with_values_and_modulus(&expressions, facts, values, &modulus());

    println!(
        "demo_all_but_one K={:?} values={:?}",
        sorted_unique_cells(&result),
        result.value_facts.known_values()
    );

    assert!(result.facts.is_unique(&y0));
    assert!(result.facts.is_unique(&y1));
    assert!(result.facts.is_unique(&y2));
    assert_eq!(result.value_facts.known_value(&y0), Some(&BigInt::from(0)));
    assert_eq!(result.value_facts.known_value(&y1), Some(&BigInt::from(7)));
    assert_eq!(result.value_facts.known_value(&y2), Some(&BigInt::from(0)));
}

// Demo 4:
// BigInt-Mul / lineáris rendszer:
//   2*x + y = a
//   x + 3*y = b
//
// A jobb oldal unique, az együttható-mátrix determinánsa nem nulla modulo p,
// ezért x és y egyértelműen meghatározottak.
#[test]
fn demo_bigint_mul_solves_invertible_linear_system() {
    let a = CellId::instance(0, 0);
    let b = CellId::instance(1, 0);
    let x = CellId::advice(0, 0);
    let y = CellId::advice(1, 0);

    let expressions = vec![
        add3(
            UcpExpr::scale_by(
                UcpExpr::var(x.clone()),
                super::expr::UcpScalar::known_i64(2),
            ),
            UcpExpr::var(y.clone()),
            UcpExpr::neg(UcpExpr::var(a.clone())),
        ),
        add3(
            UcpExpr::var(x.clone()),
            UcpExpr::scale_by(
                UcpExpr::var(y.clone()),
                super::expr::UcpScalar::known_i64(3),
            ),
            UcpExpr::neg(UcpExpr::var(b.clone())),
        ),
    ];
    let facts = UcpFacts::from_iter([a, b]);

    let result = analyze_expressions_with_values_and_modulus(
        &expressions,
        facts,
        UcpValueFacts::new(),
        &modulus(),
    );

    println!("demo_bigint_mul K={:?}", sorted_unique_cells(&result));

    assert!(result.facts.is_unique(&x));
    assert!(result.facts.is_unique(&y));
    assert!(result.all_expressions_unique());
}

// Demo 5:
// A ChooseVar heurisztika nem soundness szabály, hanem SMT-kérdés választó.
// Itt a z targetet választja, mert ha közvetlenül a target unique voltát
// bizonyítja SMT, akkor azonnal lezárható az output ellenőrzés.
#[test]
fn demo_choose_var_prefers_target_that_closes_the_goal() {
    let public = CellId::instance(0, 0);
    let x = CellId::advice(0, 0);
    let y = CellId::advice(1, 0);
    let z = CellId::advice(2, 0);

    let expressions = vec![
        add3(
            UcpExpr::var(x.clone()),
            UcpExpr::var(public.clone()),
            UcpExpr::known_constant_i64(-5),
        ),
        add3(
            UcpExpr::var(y.clone()),
            UcpExpr::neg(UcpExpr::var(x.clone())),
            UcpExpr::known_constant_i64(-1),
        ),
        add3(
            UcpExpr::var(z.clone()),
            UcpExpr::neg(UcpExpr::var(y.clone())),
            UcpExpr::known_constant_i64(-1),
        ),
    ];
    let facts = UcpFacts::from_iter([public.clone()]);
    let chosen = choose_query_cell(
        &expressions,
        &facts,
        &UcpValueFacts::new(),
        &modulus(),
        &[z.clone()],
        &[x.clone(), y.clone(), z.clone()],
        &HashSet::new(),
    );

    println!("demo_choose_var chosen={:?}", chosen);

    assert_eq!(chosen, Some(z));
}

// Demo 6:
// Negatív példa: ugyanaz a két változó csak egyetlen egyenletben szerepel:
//   x + y = public
//
// Ebből az UCP helyesen nem tanulja meg se x-et, se y-t. Ez fontos, mert a demo
// nemcsak azt mutatja, mikor tanulunk, hanem azt is, mikor nem szabad tanulni.
#[test]
fn demo_underconstrained_equation_stays_unresolved() {
    let public = CellId::instance(0, 0);
    let x = CellId::advice(0, 0);
    let y = CellId::advice(1, 0);
    let expressions = vec![add3(
        UcpExpr::var(x.clone()),
        UcpExpr::var(y.clone()),
        UcpExpr::neg(UcpExpr::var(public.clone())),
    )];
    let facts = UcpFacts::from_iter([public]);

    let result = analyze_expressions_with_values_and_modulus(
        &expressions,
        facts,
        UcpValueFacts::new(),
        &modulus(),
    );

    println!(
        "demo_underconstrained unresolved={:?}",
        result.unresolved_targets(&[x.clone(), y.clone()])
    );

    assert!(!result.facts.is_unique(&x));
    assert!(!result.facts.is_unique(&y));
    assert_eq!(result.unresolved_targets(&[x, y]).len(), 2);
}
