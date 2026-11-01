use super::*;
use crate::circuit_analyzer::ucp::{
    engine::analyze_expressions_with_values_and_modulus,
    facts::UcpFacts,
    value::{
        evaluate_expr, infer_domains_from_expression_domain_with_modulus,
        infer_value_domains_from_zero_equation_with_modulus, normalize_field_value, MAX_VALUE_BITS,
    },
};

fn cell(n: usize) -> CellId {
    CellId::advice(n, 0)
}

fn var(n: usize) -> UcpExpr {
    UcpExpr::var(cell(n))
}

fn constant(n: i64) -> UcpExpr {
    UcpExpr::known_constant_i64(n)
}

fn domain(values: impl IntoIterator<Item = i64>) -> UcpValueDomain {
    UcpValueDomain::finite_set(values.into_iter().map(BigInt::from)).unwrap()
}

fn contains(domain: &UcpValueDomain, value: &BigInt, modulus: &BigInt) -> bool {
    let value = normalize_field_value(value.clone(), modulus).unwrap();
    domain_values(domain)
        .into_iter()
        .any(|v| normalize_field_value(v, modulus).unwrap() == value)
}

#[test]
fn finite_projection_recovers_a_bounded_remainder_and_then_the_factor() {
    for (base, packed, quotients) in [(7, [84, 98], [12, 14]), (11, [220, 242], [20, 22])] {
        for ids in [[0, 1, 2, 3], [43, 9, 81, 6]] {
            let [factor, amount, quotient, remainder] = ids;
            let expression = UcpExpr::add(
                UcpExpr::mul(var(factor), var(amount)),
                UcpExpr::neg(UcpExpr::add(
                    UcpExpr::mul(constant(base), var(quotient)),
                    var(remainder),
                )),
            );
            let mut values = UcpValueFacts::new();
            values.mark_domain(cell(factor), domain([1, 2, 3]));
            values.mark_domain(cell(amount), domain(packed));
            values.mark_domain(cell(quotient), domain(quotients));
            values.mark_domain(cell(remainder), domain(0..base));
            let result = analyze_expressions_with_values_and_modulus(
                &[expression],
                UcpFacts::new(),
                values,
                &BigInt::from(65537),
            );
            assert_eq!(
                result.value_facts.known_value(&cell(remainder)),
                Some(&0.into())
            );
            assert_eq!(
                result.value_facts.known_value(&cell(factor)),
                Some(&1.into())
            );
            assert!(result.facts.is_unique(&cell(remainder)));
            assert!(result.facts.is_unique(&cell(factor)));
            assert_eq!(
                result.value_facts.domain(&cell(amount)),
                Some(&domain(packed))
            );
            assert!(!result.value_facts.domain_is_complete(&cell(amount)));
        }
    }
}

#[test]
fn finite_projection_accepts_nonlinear_residuals_and_finite_nonzero_coefficients() {
    // A c*x+y*z=0 alakban c is halmazból ismert; egyetlen konkrét c értéket sem feltételez.
    let expression = UcpExpr::add(UcpExpr::mul(var(1), var(0)), UcpExpr::mul(var(2), var(3)));
    let mut values = UcpValueFacts::new();
    values.mark_domain(cell(1), domain([2, 3]));
    values.mark_domain(cell(2), domain([1, 4]));
    values.mark_domain(cell(3), domain([2, 5]));
    let modulus = 101.into();
    let inferred = infer(&expression, &domain([0]), &values, Some(&modulus));
    let projection = &inferred.iter().find(|(c, _)| *c == cell(0)).unwrap().1;
    for coefficient in [2, 3] {
        for y in [1, 4] {
            for z in [2, 5] {
                let expected =
                    solve_linear_value(&(-y * z).into(), &coefficient.into(), Some(&modulus))
                        .unwrap();
                assert!(contains(projection, &expected, &modulus));
            }
        }
    }
    assert!(values.domain(&cell(0)).is_none());
}

#[test]
fn finite_projection_lookup_membership_uses_the_whole_rhs_domain() {
    let expression = UcpExpr::add(var(0), UcpExpr::mul(var(1), var(2)));
    let mut values = UcpValueFacts::new();
    values.mark_domain(cell(1), domain([2, 4]));
    values.mark_domain(cell(2), domain([3, 5]));
    let inferred = infer_domains_from_expression_domain_with_modulus(
        &expression,
        &domain([7, 11]),
        &values,
        &101.into(),
    );
    let projected = &inferred.iter().find(|(c, _)| *c == cell(0)).unwrap().1;
    assert_eq!(projected, &domain([-13, -9, -5, -3, -1, 1, 5]));
}

#[test]
fn finite_projection_does_not_treat_repeated_target_occurrences_as_independent() {
    let mut values = UcpValueFacts::new();
    values.mark_domain(cell(1), domain([1, 2]));
    let square = UcpExpr::add(UcpExpr::mul(var(0), var(0)), UcpExpr::neg(var(1)));
    assert!(infer(&square, &domain([0]), &values, Some(&17.into()))
        .iter()
        .all(|(c, _)| *c != cell(0)));
    let cancelling = UcpExpr::mul(var(0), UcpExpr::add(var(1), UcpExpr::neg(var(1))));
    assert!(infer(&cancelling, &domain([0]), &values, Some(&17.into()))
        .iter()
        .all(|(c, _)| *c != cell(0)));
}

#[test]
fn finite_projection_preserves_overapproximation_for_repeated_other_cells() {
    let expression = UcpExpr::add(var(0), UcpExpr::mul(var(1), var(1)));
    let mut values = UcpValueFacts::new();
    values.mark_domain(cell(1), domain([2, 5]));
    let inferred = infer(&expression, &domain([0]), &values, Some(&101.into()));
    let projected = &inferred.iter().find(|(c, _)| *c == cell(0)).unwrap().1;
    // A -10 megmaradhat túlbecslésként; a valódi -4 és -25 értéket nem zárhatja ki.
    assert_eq!(projected, &domain([-25, -10, -4]));
    assert!(!values.domain_is_complete(&cell(0)));
}

#[test]
fn finite_projection_rejects_zero_and_noninvertible_possible_coefficients() {
    let expression = UcpExpr::add(UcpExpr::mul(var(1), var(0)), UcpExpr::neg(var(2)));
    for (modulus, coefficients) in [(17, vec![0, 2]), (17, vec![17, 19]), (15, vec![3, 6])] {
        let mut values = UcpValueFacts::new();
        values.mark_domain(cell(1), domain(coefficients));
        values.mark_domain(cell(2), domain([0, 3]));
        assert!(
            infer(&expression, &domain([0]), &values, Some(&modulus.into()))
                .iter()
                .all(|(c, _)| *c != cell(0))
        );
    }
    for modulus in [0, 1, -7] {
        assert!(infer(
            &expression,
            &domain([0]),
            &UcpValueFacts::new(),
            Some(&modulus.into())
        )
        .is_empty());
    }
}

#[test]
fn finite_projection_handles_signed_aliases_and_integer_division() {
    let expression = UcpExpr::add(
        UcpExpr::mul(constant(2), var(0)),
        UcpExpr::mul(var(1), var(2)),
    );
    let mut values = UcpValueFacts::new();
    values.mark_domain(cell(1), domain([2, 4]));
    values.mark_domain(cell(2), domain([3, 6]));
    let inferred = infer(&expression, &domain([0]), &values, None);
    assert_eq!(
        inferred.iter().find(|(c, _)| *c == cell(0)).unwrap().1,
        domain([-12, -6, -3])
    );

    values = UcpValueFacts::new();
    values.mark_domain(cell(1), domain([1]));
    values.mark_domain(cell(2), domain([3]));
    assert!(infer(&expression, &domain([0]), &values, None)
        .iter()
        .all(|(c, _)| *c != cell(0)));

    let mut aliases = UcpValueFacts::new();
    aliases.mark_domain(cell(1), domain([2, 19]));
    aliases.mark_domain(cell(2), domain([-1, 16]));
    let expr = UcpExpr::add(UcpExpr::mul(var(1), var(0)), var(2));
    let inferred = infer(&expr, &domain([0]), &aliases, Some(&17.into()));
    assert_eq!(
        inferred.iter().find(|(c, _)| *c == cell(0)).unwrap().1,
        domain([-8])
    );
}

#[test]
fn finite_projection_limits_never_return_a_partial_candidate_prefix() {
    let expression = UcpExpr::add(var(0), UcpExpr::mul(var(1), var(2)));
    let mut values = UcpValueFacts::new();
    values.mark_domain(cell(1), domain(1..=17));
    values.mark_domain(cell(2), domain(20..=36));
    let original = values.clone();
    assert!(infer(&expression, &domain([0]), &values, Some(&1009.into())).is_empty());
    assert_eq!(values, original);

    values = UcpValueFacts::new();
    values.mark_domain(cell(1), domain([2, 4]));
    values.mark_domain(cell(2), domain([3, 5]));
    for budget in 0..80 {
        let mut projection = Projection {
            values: &values,
            modulus: None,
            work: budget,
        };
        if let Some(result) = projection.project(&expression, &domain([0]), &cell(0)) {
            assert_eq!(result, domain([-20, -12, -10, -6]));
        }
    }
    let oversized =
        (0..MAX_EXPRESSION_NODES).fold(expression, |expr, _| UcpExpr::add(expr, var(1)));
    assert!(infer(&oversized, &domain([0]), &values, None).is_empty());
    let oversized_value = UcpExpr::add(
        var(0),
        UcpExpr::known_constant(BigInt::from(1) << MAX_VALUE_BITS),
    );
    assert!(infer(&oversized_value, &domain([0]), &values, None).is_empty());
}

#[test]
fn finite_projection_unknown_inputs_and_complete_domains_are_not_assumptions() {
    let expr = UcpExpr::add(var(0), UcpExpr::mul(var(1), UcpExpr::constant()));
    assert!(infer(&expr, &domain([0]), &UcpValueFacts::new(), Some(&17.into())).is_empty());
    let mut values = UcpValueFacts::new();
    values.mark_domain(cell(0), domain([1, 2]));
    values
        .mark_complete_from_samples(&cell(0), &[1.into(), 2.into()].into(), &17.into())
        .unwrap();
    values.mark_domain(cell(1), domain([3, 4]));
    let expr = UcpExpr::add(var(0), UcpExpr::mul(var(1), var(1)));
    assert!(infer(&expr, &domain([0]), &values, Some(&17.into()))
        .iter()
        .all(|(c, _)| *c != cell(0)));
}

#[test]
fn finite_projection_preserves_every_small_field_solution() {
    let x = var(0);
    let y = var(1);
    let z = var(2);
    let mut checked_inferences = 0;
    for p in [5, 7, 11] {
        let modulus = BigInt::from(p);
        for tag in 0..p {
            let expressions = [
                UcpExpr::add(UcpExpr::mul(x.clone(), y.clone()), z.clone()),
                UcpExpr::add(
                    UcpExpr::mul(x.clone(), UcpExpr::add(y.clone(), UcpExpr::neg(z.clone()))),
                    constant(tag),
                ),
                UcpExpr::add(
                    UcpExpr::mul(x.clone(), x.clone()),
                    UcpExpr::mul(y.clone(), z.clone()),
                ),
                UcpExpr::add(
                    UcpExpr::mul(
                        UcpExpr::add(x.clone(), y.clone()),
                        UcpExpr::add(z.clone(), constant(1)),
                    ),
                    constant(tag),
                ),
                UcpExpr::add(
                    UcpExpr::mul(
                        x.clone(),
                        UcpExpr::add(UcpExpr::mul(y.clone(), y.clone()), constant(tag)),
                    ),
                    z.clone(),
                ),
                UcpExpr::scale_by(
                    UcpExpr::add(UcpExpr::mul(x.clone(), y.clone()), z.clone()),
                    UcpScalar::known_i64(p),
                ),
            ];
            for ys in [vec![0, 1, 2], vec![1, 2]] {
                let mut values = UcpValueFacts::new();
                values.mark_domain(cell(0), domain(0..p));
                values.mark_domain(cell(1), domain(ys.clone()));
                values.mark_domain(cell(2), domain([0, 2]));
                for expression in &expressions {
                    let inferred = infer_value_domains_from_zero_equation_with_modulus(
                        expression, &values, &modulus,
                    );
                    checked_inferences += inferred.len();
                    for xv in 0..p {
                        for yv in &ys {
                            for zv in [0, 2] {
                                let mut concrete = UcpValueFacts::new();
                                concrete.mark_known(cell(0), xv.into());
                                concrete.mark_known(cell(1), (*yv).into());
                                concrete.mark_known(cell(2), zv.into());
                                let result = evaluate_expr(expression, &concrete).unwrap();
                                if result % &modulus != BigInt::from(0) {
                                    continue;
                                }
                                for (target, projection) in &inferred {
                                    assert!(contains(projection, concrete.known_value(target).unwrap(), &modulus),
                                        "p={p}, expression={expression:?}, target={target:?}, assignment=({xv},{yv},{zv})");
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(checked_inferences > 50);
}
