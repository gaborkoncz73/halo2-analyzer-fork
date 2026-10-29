use super::{
    base_conv::finite_base_candidates,
    cell::CellId,
    engine::analyze_expressions_with_relations_and_modulus,
    expr::UcpExpr,
    facts::UcpFacts,
    lookup::{entries, UcpLookup},
    value::{normalize_field_value, UcpValueDomain, UcpValueFacts, MAX_FINITE_DOMAIN_SIZE},
};
use num_bigint::BigInt;
use std::collections::BTreeSet;

fn var(n: usize) -> UcpExpr {
    UcpExpr::var(CellId::advice(n, 0))
}
fn constant(n: i64) -> UcpExpr {
    UcpExpr::known_constant_i64(n)
}
fn sum(terms: impl IntoIterator<Item = UcpExpr>) -> UcpExpr {
    terms.into_iter().fold(UcpExpr::zero(), UcpExpr::add)
}
fn domain(values: impl IntoIterator<Item = i64>) -> UcpValueDomain {
    UcpValueDomain::finite_set(values.into_iter().map(BigInt::from)).unwrap()
}
fn normalize(n: i64, p: i64) -> BigInt {
    normalize_field_value(n.into(), &p.into()).unwrap()
}
fn analyze(
    expressions: &[UcpExpr],
    lookups: &[UcpLookup],
    values: UcpValueFacts,
    p: i64,
) -> super::engine::UcpResult {
    analyze_expressions_with_relations_and_modulus(
        expressions,
        &[],
        lookups,
        UcpFacts::new(),
        values,
        &p.into(),
    )
}

#[test]
fn tuple_membership_filters_whole_rows_not_cartesian_column_products() {
    let relation = UcpLookup::new(
        vec![var(0), var(1)],
        vec![
            vec![2.into(), 8.into()],
            vec![5.into(), 9.into()],
            vec![7.into(), 8.into()],
        ],
    )
    .unwrap();
    let mut values = UcpValueFacts::new();
    values.mark_known(CellId::advice(1, 0), 8.into());
    let result = analyze(&[], &[relation], values, 101);
    assert_eq!(
        result.value_facts.domain(&CellId::advice(0, 0)),
        Some(&domain([2, 7]))
    );
    assert!(!result.value_facts.domain_is_complete(&CellId::advice(0, 0)));
    assert!(!result.facts.is_unique(&CellId::advice(0, 0)));
}

#[test]
fn tuple_membership_accepts_affine_inputs_and_field_aliases() {
    let relation = UcpLookup::new(
        vec![UcpExpr::add(var(0), var(1)), var(1)],
        vec![vec![3.into(), 12.into()], vec![8.into(), 2.into()]],
    )
    .unwrap();
    let mut values = UcpValueFacts::new();
    values.mark_known(CellId::advice(1, 0), (-1).into());
    let result = analyze(&[], &[relation], values, 13);
    assert_eq!(
        result.value_facts.known_value(&CellId::advice(0, 0)),
        Some(&BigInt::from(4))
    );
}

#[test]
fn tuple_membership_matches_exhaustive_small_field_projections() {
    for p in [5, 7, 11] {
        for tag in 0..p {
            let rows: Vec<_> = (0..p)
                .flat_map(|x| {
                    (0..p).filter_map(move |y| {
                        ((3 * x + y * y) % p == tag).then(|| vec![BigInt::from(x), BigInt::from(y)])
                    })
                })
                .collect();
            if rows.is_empty() {
                continue;
            }
            for fixed_y in 0..p {
                let feasible: BTreeSet<_> = rows
                    .iter()
                    .filter(|row| row[1] == BigInt::from(fixed_y))
                    .map(|row| normalize_field_value(row[0].clone(), &p.into()).unwrap())
                    .collect();
                if feasible.is_empty() {
                    continue;
                }
                let relation = UcpLookup::new(vec![var(0), var(1)], rows.clone()).unwrap();
                let mut values = UcpValueFacts::new();
                values.mark_known(CellId::advice(1, 0), normalize(fixed_y, p));
                let result = analyze(&[], &[relation], values, p);
                assert_eq!(
                    entries(result.value_facts.domain(&CellId::advice(0, 0)).unwrap()),
                    feasible
                );
            }
        }
    }
}

#[test]
fn tuple_limits_reject_entire_relations_and_partial_rows() {
    assert!(UcpLookup::new(vec![var(0), var(1)], vec![vec![1.into()]]).is_none());
    assert!(UcpLookup::new(
        vec![var(0)],
        (0..=MAX_FINITE_DOMAIN_SIZE)
            .map(|x| vec![x.into()])
            .collect()
    )
    .is_none());
    assert!(UcpLookup::new(vec![var(0)], vec![]).is_none());
}

fn packed_fixture(base: i64, count: usize) -> (Vec<UcpExpr>, UcpValueFacts) {
    let mut power = 1;
    let mut packed = vec![];
    let mut values = UcpValueFacts::new();
    for bit in 0..count {
        values.mark_domain(CellId::advice(bit + 1, 0), domain(0..base));
        packed.push(UcpExpr::scale_by(
            var(bit + 1),
            super::expr::UcpScalar::known_i64(power),
        ));
        power *= base;
    }
    values.mark_domain(CellId::advice(0, 0), domain(0..power));
    (
        vec![UcpExpr::add(var(0), UcpExpr::neg(sum(packed)))],
        values,
    )
}

#[test]
fn finite_radix_filtering_matches_exhaustive_digit_checks() {
    for (base, count, p) in [(2_i64, 3, 11), (2, 4, 29), (3, 3, 101), (4, 2, 37)] {
        let bound = base.pow(count as u32);
        for weight in 1..=(base - 1) * count as i64 {
            let (mut expressions, mut values) = packed_fixture(base, count);
            // Non-binary radix digits, signed field representatives and an unrelated digit sum.
            values = {
                let mut canonical = UcpValueFacts::new();
                for (cell, d) in values.domains() {
                    canonical.mark_domain(
                        cell.clone(),
                        UcpValueDomain::finite_set(
                            entries(d)
                                .into_iter()
                                .map(|v| normalize_field_value(v, &p.into()).unwrap()),
                        )
                        .unwrap(),
                    );
                }
                canonical
            };
            expressions.push(UcpExpr::add(sum((1..=count).map(var)), constant(-weight)));
            let expected: BTreeSet<_> = (0..bound)
                .filter(|x| {
                    let mut left = *x;
                    (0..count)
                        .map(|_| {
                            let digit = left % base;
                            left /= base;
                            digit
                        })
                        .sum::<i64>()
                        == weight
                })
                .map(|x| normalize(x, p))
                .collect();
            let result = analyze(&expressions, &[], values, p);
            assert_eq!(
                entries(result.value_facts.domain(&CellId::advice(0, 0)).unwrap()),
                expected,
                "base={base}, digits={count}, p={p}, sum={weight}"
            );
        }
    }
}

#[test]
fn conditional_facts_do_not_escape_and_unknown_constraints_do_not_refute() {
    let (mut expressions, values) = packed_fixture(2, 3);
    expressions.push(UcpExpr::constant());
    let result = analyze(&expressions, &[], values.clone(), 101);
    assert_eq!(result.value_facts, values);
    assert!((1..=3).all(|col| !result.facts.is_unique(&CellId::advice(col, 0))));
}

#[test]
fn wrapped_radix_equations_are_not_inverted_as_integer_digits() {
    let (expressions, values) = packed_fixture(2, 3);
    assert!(finite_base_candidates(&expressions, &values, &7.into()).is_empty());
    // 0 has two digit representations modulo 7. Never discard its 111 witness.
    let mut expressions = expressions;
    expressions.push(UcpExpr::add(sum((1..=3).map(var)), constant(-3)));
    let result = analyze(&expressions, &[], values, 7);
    assert!(
        entries(result.value_facts.domain(&CellId::advice(0, 0)).unwrap())
            .contains(&BigInt::from(0))
    );
}

#[test]
fn conditional_probe_budget_preserves_unvisited_candidates() {
    let (mut expressions, mut values) = packed_fixture(2, 8);
    let required = UcpExpr::add(sum((1..=8).map(var)), constant(-4));
    expressions.push(UcpExpr::mul(required.clone(), required));
    let packed = CellId::advice(20, 0);
    values.mark_domain(packed.clone(), domain(0..256));
    for i in 21..29 {
        values.mark_domain(CellId::advice(i, 0), domain([0, 1]));
    }
    expressions.push(UcpExpr::add(
        var(20),
        UcpExpr::neg(sum((0..8).map(|i| {
            UcpExpr::scale_by(var(21 + i), super::expr::UcpScalar::known_i64(1 << i))
        }))),
    ));
    // A nemlineáris alak nem engedi, hogy az elimináció önmagában szűkítse a második csomagot.
    let required = UcpExpr::add(sum((21..29).map(var)), constant(-3));
    expressions.push(UcpExpr::mul(required.clone(), required));
    let result = analyze(&expressions, &[], values, 1009);
    assert_eq!(
        entries(result.value_facts.domain(&CellId::advice(0, 0)).unwrap()).len(),
        70
    );
    assert_eq!(
        entries(result.value_facts.domain(&packed).unwrap()).len(),
        256
    );
}

#[test]
fn conditional_round_limit_is_not_a_proof_of_infeasibility() {
    let (mut expressions, mut values) = packed_fixture(2, 2);
    let mut chain = vec![UcpExpr::add(var(10), UcpExpr::neg(var(0)))];
    for i in 11..=90 {
        chain.push(UcpExpr::add(
            var(i),
            UcpExpr::neg(UcpExpr::mul(var(i - 1), var(i - 1))),
        ));
    }
    chain.reverse();
    expressions.extend(chain);
    values.mark_known(CellId::advice(90, 0), 0.into());
    let result = analyze(&expressions, &[], values, 101);
    // All nonzero candidates are actually impossible, but require more conditional rounds.
    // Retain them when the bounded proof attempt cannot reach the contradiction.
    assert_eq!(
        result.value_facts.domain(&CellId::advice(0, 0)),
        Some(&domain(0..4))
    );
}

#[test]
fn finite_radix_filtering_is_independent_of_cell_names_and_equation_order() {
    fn rename(expr: UcpExpr) -> UcpExpr {
        match expr {
            UcpExpr::Var(cell) => UcpExpr::var(CellId::advice(900 - cell.column, cell.row + 7)),
            UcpExpr::Neg(inner) => UcpExpr::neg(rename(*inner)),
            UcpExpr::Add(a, b) => UcpExpr::add(rename(*a), rename(*b)),
            UcpExpr::Mul(a, b) => UcpExpr::mul(rename(*a), rename(*b)),
            UcpExpr::Scale(inner, scalar) => UcpExpr::scale_by(rename(*inner), scalar),
            other => other,
        }
    }
    let (mut expressions, values) = packed_fixture(3, 3);
    expressions.push(UcpExpr::add(sum((1..=3).map(var)), constant(-3)));
    let original = analyze(&expressions, &[], values.clone(), 101);
    let mut renamed = UcpValueFacts::new();
    for (cell, domain) in values.domains() {
        renamed.mark_domain(
            CellId::advice(900 - cell.column, cell.row + 7),
            domain.clone(),
        );
    }
    let reordered: Vec<_> = expressions.into_iter().rev().map(rename).collect();
    let result = analyze(&reordered, &[], renamed, 101);
    for (cell, domain) in original.value_facts.domains() {
        assert_eq!(
            result
                .value_facts
                .domain(&CellId::advice(900 - cell.column, cell.row + 7)),
            Some(domain)
        );
    }
}

#[test]
fn conditional_filtering_preserves_all_small_field_nonlinear_solutions() {
    for p in [5, 7, 11] {
        for a in -1..=1 {
            for b in -1..=1 {
                for c in -1..=1 {
                    for rhs in 0..p {
                        let expected: BTreeSet<_> = (0_i64..4)
                            .filter(|x| {
                                let lo = x % 2;
                                let hi = x / 2;
                                (a * lo * hi + b * lo + c * hi - rhs).rem_euclid(p) == 0
                            })
                            .map(|x| normalize(x, p))
                            .collect();
                        if expected.is_empty() {
                            continue;
                        }
                        let (mut expressions, initial) = packed_fixture(2, 2);
                        let mut values = UcpValueFacts::new();
                        for (cell, d) in initial.domains() {
                            values.mark_domain(
                                cell.clone(),
                                UcpValueDomain::finite_set(
                                    entries(d)
                                        .into_iter()
                                        .map(|v| normalize_field_value(v, &p.into()).unwrap()),
                                )
                                .unwrap(),
                            );
                        }
                        expressions.push(sum([
                            UcpExpr::scale_by(
                                UcpExpr::mul(var(1), var(2)),
                                super::expr::UcpScalar::known_i64(a),
                            ),
                            UcpExpr::scale_by(var(1), super::expr::UcpScalar::known_i64(b)),
                            UcpExpr::scale_by(var(2), super::expr::UcpScalar::known_i64(c)),
                            constant(-rhs),
                        ]));
                        let result = analyze(&expressions, &[], values, p);
                        let retained =
                            entries(result.value_facts.domain(&CellId::advice(0, 0)).unwrap());
                        assert!(
                            expected.is_subset(&retained),
                            "p={p}, a={a}, b={b}, c={c}, rhs={rhs}"
                        );
                        if result.facts.is_unique(&CellId::advice(0, 0)) {
                            assert_eq!(expected.len(), 1);
                        }
                    }
                }
            }
        }
    }
}

#[cfg(feature = "use_zcash_halo2_proofs")]
mod extraction {
    use super::super::extractor::extract_ucp_problem;
    use super::*;
    use crate::circuit_analyzer::{analyzable::Analyzable, halo2_proofs_libs::*};

    #[derive(Clone)]
    struct TupleCircuit<const LARGE: bool>;

    #[derive(Clone)]
    struct Config {
        x: Column<Advice>,
        y: Column<Advice>,
        public: Column<Instance>,
        q: Selector,
        tables: [TableColumn; 2],
    }

    impl<const LARGE: bool> Circuit<Fr> for TupleCircuit<LARGE> {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;
        fn without_witnesses(&self) -> Self {
            Self
        }
        fn configure(meta: &mut ConstraintSystem<Fr>) -> Config {
            let x = meta.advice_column();
            let y = meta.advice_column();
            let public = meta.instance_column();
            meta.enable_equality(y);
            meta.enable_equality(public);
            let q = meta.complex_selector();
            let tables = [meta.lookup_table_column(), meta.lookup_table_column()];
            meta.lookup(|meta| {
                let active = meta.query_selector(q);
                vec![
                    (
                        active.clone() * meta.query_advice(x, Rotation::prev()),
                        tables[0],
                    ),
                    (active * meta.query_advice(y, Rotation::cur()), tables[1]),
                ]
            });
            Config {
                x,
                y,
                public,
                q,
                tables,
            }
        }
        fn synthesize(&self, c: Config, mut layouter: impl Layouter<Fr>) -> Result<(), Error> {
            layouter.assign_table(
                || "complete tuple relation",
                |mut table| {
                    for i in 0..if LARGE { 257 } else { 4 } {
                        let second = if LARGE { i % 3 } else { [0, 3, 3, 4][i] };
                        for (column, value) in c.tables.into_iter().zip([i, second]) {
                            table.assign_cell(
                                || "tuple member",
                                column,
                                i,
                                || Value::known(Fr::from(value as u64)),
                            )?;
                        }
                    }
                    Ok(())
                },
            )?;
            let y = layouter.assign_region(
                || "rotated active tuple",
                |mut r| {
                    r.assign_advice(|| "private", c.x, 0, || Value::known(Fr::from(1)))?;
                    c.q.enable(&mut r, 1)?;
                    r.assign_advice(
                        || "observed",
                        c.y,
                        1,
                        || Value::known(Fr::from(if LARGE { 1 } else { 3 })),
                    )
                },
            )?;
            layouter.constrain_instance(y.cell(), c.public, 0)
        }
    }

    #[test]
    fn extraction_keeps_rotated_tuple_correlation_and_skips_inactive_rows() {
        let circuit = TupleCircuit::<false>;
        MockProver::run(4, &circuit, vec![vec![Fr::from(3)]])
            .unwrap()
            .assert_satisfied();
        let layout = Analyzable::<Fr>::config_and_synthesize(&circuit, 4).unwrap();
        let problem = extract_ucp_problem(&layout);
        assert_eq!(problem.lookups.len(), 1);
        let mut values = problem.initial_value_facts.clone();
        values.mark_known(CellId::instance(0, 0), 3.into());
        let result = problem.analyze_with_values(problem.initial_facts.clone(), values);
        assert_eq!(
            result.value_facts.domain(&CellId::advice(0, 0)),
            Some(&domain([1, 2]))
        );
    }

    #[test]
    fn oversized_tuple_extraction_does_not_truncate_the_covering_relation() {
        let circuit = TupleCircuit::<true>;
        MockProver::run(9, &circuit, vec![vec![Fr::from(1)]])
            .unwrap()
            .assert_satisfied();
        let layout = Analyzable::<Fr>::config_and_synthesize(&circuit, 9).unwrap();
        let problem = extract_ucp_problem(&layout);
        assert!(problem.lookups.is_empty());
        assert!(problem
            .initial_value_facts
            .domain(&CellId::advice(0, 0))
            .is_none());
        assert_eq!(
            problem.initial_value_facts.domain(&CellId::advice(1, 1)),
            Some(&domain([0, 1, 2]))
        );
    }
}
