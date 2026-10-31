//! Counterexamples from the soundness review, checked against field solutions and Halo2.
use super::{
    all_but_one::infer_all_but_one_zero_with_modulus,
    base_conv::infer_base_conversions_with_modulus,
    cell::CellId,
    engine::analyze_expressions_with_values_and_modulus,
    expr::{UcpExpr, UcpScalar},
    facts::UcpFacts,
    privacy::{
        analyze_private_recoverability, PrivacyAnalysisOptions, PrivacyAnalysisStatus,
        PrivateCellUniqueness,
    },
    privacy_validation::{validate_private_recovery_report, RecoveryValidationStatus},
    value::{UcpValueDomain, UcpValueFacts},
};
use crate::{circuit_analyzer::halo2_proofs_libs::*, io::analyzer_io_type::*};
use num_bigint::BigInt;
use std::collections::HashMap;

fn analyze_equation(expr: UcpExpr, p: i64) -> super::engine::UcpResult {
    analyze_expressions_with_values_and_modulus(
        &[expr],
        UcpFacts::new(),
        UcpValueFacts::new(),
        &p.into(),
    )
}

fn affine(cell: &CellId, coefficient: i64, constant: i64) -> UcpExpr {
    UcpExpr::add(
        UcpExpr::scale_by(
            UcpExpr::var(cell.clone()),
            UcpScalar::known_i64(coefficient),
        ),
        UcpExpr::known_constant_i64(constant),
    )
}

fn domain_contains(domain: &UcpValueDomain, candidate: i64, p: i64) -> bool {
    let equivalent =
        |value: &BigInt| (value - BigInt::from(candidate)) % BigInt::from(p) == BigInt::from(0);
    match domain {
        UcpValueDomain::Exact(value) => equivalent(value),
        UcpValueDomain::FiniteSet(values) => values.iter().any(equivalent),
    }
}

#[test]
fn linear_inference_covers_every_solution_in_small_prime_fields() {
    //Enumerate wraparound, negative representatives, zero coefficients and modular fractions.
    let cell = CellId::advice(0, 0);
    for p in [2_i64, 3, 5, 7] {
        for coefficient in -2 * p..=2 * p {
            for constant in -2 * p..=2 * p {
                let solutions: Vec<_> = (0..p)
                    .filter(|x| (coefficient * x + constant).rem_euclid(p) == 0)
                    .collect();
                let result = analyze_equation(affine(&cell, coefficient, constant), p);
                if result.facts.is_unique(&cell) {
                    assert!(solutions.len() <= 1, "p={p}, a={coefficient}, b={constant}");
                }
                if let Some(domain) = result.value_facts.domain(&cell) {
                    for solution in solutions {
                        assert!(
                            domain_contains(domain, solution, p),
                            "p={p}, a={coefficient}, b={constant}, x={solution}, domain={domain:?}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn product_inference_covers_every_solution_in_small_prime_fields() {
    let cell = CellId::advice(0, 0);
    for p in [2_i64, 3, 5, 7] {
        for a in [-p, -1, 0, 1, p] {
            for b in [-1, 0, 1] {
                for c in [-p, -1, 0, 1, p] {
                    for d in [-1, 0, 1] {
                        let solutions: Vec<_> = (0..p)
                            .filter(|x| ((a * x + b) * (c * x + d)).rem_euclid(p) == 0)
                            .collect();
                        let expr = UcpExpr::mul(affine(&cell, a, b), affine(&cell, c, d));
                        let result = analyze_equation(expr, p);
                        if result.facts.is_unique(&cell) {
                            assert!(solutions.len() <= 1);
                        }
                        if let Some(domain) = result.value_facts.domain(&cell) {
                            for solution in solutions {
                                assert!(
                                    domain_contains(domain, solution, p),
                                    "p={p}, a={a}, b={b}, c={c}, d={d}, domain={domain:?}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn modular_zero_composite_factor_does_not_determine_its_operand() {
    let cell = CellId::advice(0, 0);
    //Both expressions are 5*x=0 in F_5, but their leaves contain only nonzero 2 and 3.
    let expressions = [
        UcpExpr::add(
            UcpExpr::scale_by(
                UcpExpr::scale_by(UcpExpr::var(cell.clone()), UcpScalar::known_i64(2)),
                UcpScalar::known_i64(2),
            ),
            UcpExpr::var(cell.clone()),
        ),
        UcpExpr::mul(
            UcpExpr::add(
                UcpExpr::known_constant_i64(2),
                UcpExpr::known_constant_i64(3),
            ),
            UcpExpr::var(cell.clone()),
        ),
    ];
    for expr in expressions {
        let result = analyze_equation(expr, 5);
        assert!(!result.facts.is_unique(&cell));
        assert!(result.value_facts.domain(&cell).is_none());
    }
}

#[test]
fn modular_zero_domain_cannot_be_cancelled_as_nonzero() {
    let x = CellId::advice(0, 0);
    let factor = CellId::advice(1, 0);
    let mut values = UcpValueFacts::new();
    values.mark_known(factor.clone(), 5.into());
    let result = analyze_expressions_with_values_and_modulus(
        &[UcpExpr::mul(UcpExpr::var(factor), UcpExpr::var(x.clone()))],
        UcpFacts::new(),
        values,
        &5.into(),
    );
    assert!(!result.facts.is_unique(&x));
    assert!(result.value_facts.domain(&x).is_none());
}

#[test]
fn raw_zero_scalars_do_not_prove_assignment_or_digit_uniqueness() {
    let x = CellId::instance(0, 0);
    let digits = [CellId::advice(0, 0), CellId::advice(1, 0)];
    let mut values = UcpValueFacts::new();
    for digit in &digits {
        values.mark_domain(
            digit.clone(),
            UcpValueDomain::finite_set([0.into(), 1.into()]).unwrap(),
        );
    }
    let equation = UcpExpr::add(
        UcpExpr::add(
            UcpExpr::var(digits[0].clone()),
            UcpExpr::scale_by(UcpExpr::var(digits[1].clone()), UcpScalar::known_i64(2)),
        ),
        UcpExpr::neg(UcpExpr::var(x.clone())),
    );
    let facts = UcpFacts::from_iter([x]);
    assert_eq!(
        infer_base_conversions_with_modulus(&[equation.clone()], &facts, &values, &11.into()).len(),
        2
    );
    for zero in [
        UcpScalar::Zero,
        UcpScalar::Known(0.into()),
        UcpScalar::Known(11.into()),
    ] {
        for expr in [
            UcpExpr::Scale(Box::new(equation.clone()), zero.clone()),
            UcpExpr::Mul(
                Box::new(UcpExpr::Const(zero.clone())),
                Box::new(equation.clone()),
            ),
        ] {
            assert!(
                infer_base_conversions_with_modulus(&[expr], &facts, &values, &11.into())
                    .is_empty()
            );
        }
        let expr = UcpExpr::Scale(Box::new(UcpExpr::var(digits[0].clone())), zero);
        let result = analyze_equation(expr, 11);
        assert!(!result.facts.is_unique(&digits[0]));
    }
}

fn one_hot_equations(count: usize) -> (Vec<UcpExpr>, CellId, Vec<CellId>, UcpFacts) {
    let x = CellId::instance(0, 0);
    let e = CellId::instance(0, 1);
    let digits: Vec<_> = (0..count).map(|i| CellId::advice(i, 0)).collect();
    let mut equations: Vec<_> = digits
        .iter()
        .enumerate()
        .map(|(i, y)| UcpExpr::mul(UcpExpr::var(y.clone()), affine(&x, 1, -(i as i64))))
        .collect();
    let sum = digits.iter().fold(UcpExpr::zero(), |sum, y| {
        UcpExpr::add(sum, UcpExpr::var(y.clone()))
    });
    equations.push(UcpExpr::add(sum, UcpExpr::neg(UcpExpr::var(e.clone()))));
    (equations, x.clone(), digits, UcpFacts::from_iter([x, e]))
}

#[test]
fn all_but_one_rejects_colliding_field_roots_and_zero_wrapped_sums() {
    let (equations, _, _, facts) = one_hot_equations(6);
    assert!(infer_all_but_one_zero_with_modulus(
        &equations,
        &facts,
        &UcpValueFacts::new(),
        &5.into()
    )
    .is_empty());
    let (mut equations, _, _, facts) = one_hot_equations(2);
    let sum = equations.pop().unwrap();
    for scalar in [
        UcpScalar::Zero,
        UcpScalar::Known(0.into()),
        UcpScalar::Known(5.into()),
    ] {
        let mut wrapped = equations.clone();
        wrapped.push(UcpExpr::Mul(
            Box::new(UcpExpr::Const(scalar)),
            Box::new(sum.clone()),
        ));
        assert!(infer_all_but_one_zero_with_modulus(
            &wrapped,
            &facts,
            &UcpValueFacts::new(),
            &5.into()
        )
        .is_empty());
    }
}

#[test]
fn all_but_one_compares_signed_values_as_field_elements() {
    let (equations, x, digits, facts) = one_hot_equations(5);
    let mut values = UcpValueFacts::new();
    values.mark_known(x, (-1).into());
    values.mark_known(CellId::instance(0, 1), (-2).into());
    let inferences = infer_all_but_one_zero_with_modulus(&equations, &facts, &values, &5.into());
    assert_eq!(inferences.len(), 5);
    for inference in inferences {
        assert_eq!(
            inference.value,
            Some(if inference.cell == digits[4] {
                (-2).into()
            } else {
                0.into()
            })
        );
    }
}

fn input() -> AnalyzerInput {
    AnalyzerInput {
        verification_method: VerificationMethod::None,
        verification_input: VerificationInput {
            instance_cells: HashMap::new(),
            iterations: 1,
        },
        lookup_method: LookupMethod::InlineConstraints,
    }
}

fn recover<C: Circuit<Fr>>(circuit: &C) -> super::privacy::PrivacyAnalysisReport {
    analyze_private_recoverability::<Fr, _, _>(
        circuit,
        4,
        &input(),
        [CellId::advice(0, 0)],
        PrivacyAnalysisOptions {
            max_semantic_queries: 4,
            solver_timeout_ms: Some(2000),
            ..PrivacyAnalysisOptions::fast_probe_only()
        },
    )
    .unwrap()
}

//A fixed column activates a genuine constraint; an unrelated selector must not hide it.
#[derive(Clone, Copy)]
struct FixedActivated;
impl Circuit<Fr> for FixedActivated {
    type Config = (Column<Advice>, Column<Fixed>);
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        *self
    }
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let a = meta.advice_column();
        let f = meta.fixed_column();
        let q = meta.selector();
        meta.create_gate("fixed activation", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let f = meta.query_fixed(f);
            vec![f.clone() * (a - f)]
        });
        meta.create_gate("unused optional check", |meta| {
            vec![meta.query_selector(q) * meta.query_advice(a, Rotation::cur())]
        });
        (a, f)
    }
    fn synthesize(
        &self,
        (a, f): Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "fixed activated",
            |mut region| {
                region.assign_advice(|| "secret", a, 0, || Value::known(Fr::from(1)))?;
                region.assign_fixed(|| "activation", f, 0, || Value::known(Fr::from(1)))?;
                Ok(())
            },
        )
    }
}

#[test]
fn unrelated_selector_does_not_hide_a_fixed_activated_gate() {
    let circuit = FixedActivated;
    MockProver::run(4, &circuit, vec![])
        .unwrap()
        .assert_satisfied();
    let report = recover(&circuit);
    assert_eq!(report.status, PrivacyAnalysisStatus::Analyzed);
    assert_eq!(
        report.cells[0].domain,
        Some(UcpValueDomain::exact(1.into()))
    );
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(), &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

//The lookup is active in a selectorless region; a copied constant makes inconsistency explicit.
#[derive(Clone, Copy)]
struct UngatedLookup {
    value: u64,
}
impl Circuit<Fr> for UngatedLookup {
    type Config = (Column<Advice>, Selector, TableColumn);
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        *self
    }
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let a = meta.advice_column();
        meta.enable_equality(a);
        let f = meta.fixed_column();
        meta.enable_constant(f);
        let q = meta.selector();
        let table = meta.lookup_table_column();
        meta.lookup(|meta| vec![(meta.query_advice(a, Rotation::cur()), table)]);
        meta.create_gate("unrelated selected check", |meta| {
            vec![meta.query_selector(q) * meta.query_advice(a, Rotation::cur())]
        });
        (a, q, table)
    }
    fn synthesize(
        &self,
        (a, q, table): Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "boolean table",
            |mut table_region| {
                for row in 0..2 {
                    table_region.assign_cell(
                        || "allowed",
                        table,
                        row,
                        || Value::known(Fr::from(row as u64)),
                    )?;
                }
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "selectorless secret",
            |mut region| {
                let cell = region.assign_advice(
                    || "secret",
                    a,
                    0,
                    || Value::known(Fr::from(self.value)),
                )?;
                region.constrain_constant(cell.cell(), Fr::from(self.value))?;
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "selected dummy",
            |mut region| {
                q.enable(&mut region, 0)?;
                region.assign_advice(|| "dummy", a, 0, || Value::known(Fr::from(0)))?;
                Ok(())
            },
        )
    }
}

#[test]
fn selectorless_lookup_preserves_valid_and_inconsistent_contexts() {
    for value in 0..=2 {
        let circuit = UngatedLookup { value };
        let valid = MockProver::run(4, &circuit, vec![])
            .unwrap()
            .verify()
            .is_ok();
        let report = recover(&circuit);
        assert_eq!(valid, value < 2);
        if valid {
            assert_eq!(
                report.cells[0].domain,
                Some(UcpValueDomain::exact(value.into()))
            );
        } else {
            assert_eq!(report.status, PrivacyAnalysisStatus::Inconsistent);
            assert!(report.cells[0].domain.is_none());
        }
    }
}

//An inactive selector produces zero, but zero is not automatically a valid table entry.
#[derive(Clone, Copy)]
struct ZeroNotInTable;
impl Circuit<Fr> for ZeroNotInTable {
    type Config = (Column<Advice>, TableColumn);
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        *self
    }
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let a = meta.advice_column();
        let q = meta.complex_selector();
        let table = meta.lookup_table_column();
        meta.lookup(|meta| {
            vec![(
                meta.query_selector(q) * meta.query_advice(a, Rotation::cur()),
                table,
            )]
        });
        (a, table)
    }
    fn synthesize(
        &self,
        (a, table): Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "nonzero default",
            |mut region| {
                region.assign_cell(|| "one", table, 0, || Value::known(Fr::from(1)))?;
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "inactive lookup input",
            |mut region| {
                region.assign_advice(|| "secret", a, 0, || Value::known(Fr::from(0)))?;
                Ok(())
            },
        )
    }
}

#[test]
fn zero_lookup_inputs_must_match_a_real_table_tuple() {
    let circuit = ZeroNotInTable;
    assert!(MockProver::run(4, &circuit, vec![])
        .unwrap()
        .verify()
        .is_err());
    let report = recover(&circuit);
    assert_eq!(report.status, PrivacyAnalysisStatus::Inconsistent);
    assert!(report.cells[0].domain.is_none());
}

//Tuple membership is joint: (0,1) and (1,0) do not permit (1,1).
#[derive(Clone, Copy)]
struct PartialZeroTuple {
    value: u64,
}
impl Circuit<Fr> for PartialZeroTuple {
    type Config = (Column<Advice>, Selector, [TableColumn; 2]);
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        *self
    }
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let a = meta.advice_column();
        meta.enable_equality(a);
        let f = meta.fixed_column();
        meta.enable_constant(f);
        let q = meta.complex_selector();
        let tables = [meta.lookup_table_column(), meta.lookup_table_column()];
        meta.lookup(|meta| {
            let selector = meta.query_selector(q);
            let a = meta.query_advice(a, Rotation::cur());
            let one = Expression::Constant(Fr::from(1));
            vec![
                (selector.clone(), tables[0]),
                (one.clone() + selector * (a - one), tables[1]),
            ]
        });
        (a, q, tables)
    }
    fn synthesize(
        &self,
        (a, q, tables): Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "correlated tuples",
            |mut region| {
                for (row, tuple) in [[0_u64, 1], [1, 0]].iter().enumerate() {
                    for column in 0..2 {
                        region.assign_cell(
                            || "entry",
                            tables[column],
                            row,
                            || Value::known(Fr::from(tuple[column])),
                        )?;
                    }
                }
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "selected input",
            |mut region| {
                q.enable(&mut region, 0)?;
                let cell = region.assign_advice(
                    || "secret",
                    a,
                    0,
                    || Value::known(Fr::from(self.value)),
                )?;
                region.constrain_constant(cell.cell(), Fr::from(self.value))?;
                Ok(())
            },
        )
    }
}

#[test]
fn inline_lookup_keeps_zero_coordinates_and_tuple_correlations() {
    for value in 0..=1 {
        let circuit = PartialZeroTuple { value };
        assert_eq!(
            MockProver::run(4, &circuit, vec![])
                .unwrap()
                .verify()
                .is_ok(),
            value == 0
        );
        let report = recover(&circuit);
        if value == 0 {
            assert_eq!(
                report.cells[0].domain,
                Some(UcpValueDomain::exact(0.into()))
            );
        } else {
            assert_eq!(report.status, PrivacyAnalysisStatus::Inconsistent);
        }
    }
}

//At row 1 in a 16-row domain, rotations -1 and +15 reference the same assigned cell.
#[derive(Clone, Copy)]
struct WrappedRotations;
impl Circuit<Fr> for WrappedRotations {
    type Config = (Column<Advice>, Selector);
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        *self
    }
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let a = meta.advice_column();
        let q = meta.selector();
        meta.create_gate("wrapped aliases", |meta| {
            let current = meta.query_advice(a, Rotation::cur());
            let previous = meta.query_advice(a, Rotation::prev());
            let wrapped = meta.query_advice(a, Rotation(15));
            vec![meta.query_selector(q) * (current + previous - wrapped)]
        });
        (a, q)
    }
    fn synthesize(
        &self,
        (a, q): Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "wrapped rows",
            |mut region| {
                region.assign_advice(|| "free previous", a, 0, || Value::known(Fr::from(7)))?;
                region.assign_advice(
                    || "determined current",
                    a,
                    1,
                    || Value::known(Fr::from(0)),
                )?;
                q.enable(&mut region, 1)?;
                Ok(())
            },
        )
    }
}

#[test]
fn ucp_and_smt_use_the_same_wrapped_rotation_cells() {
    let circuit = WrappedRotations;
    MockProver::run(4, &circuit, vec![])
        .unwrap()
        .assert_satisfied();
    let report = analyze_private_recoverability::<Fr, _, _>(
        &circuit,
        4,
        &input(),
        [CellId::advice(0, 0), CellId::advice(0, 1)],
        PrivacyAnalysisOptions {
            max_semantic_queries: 4,
            solver_timeout_ms: Some(2000),
            ..PrivacyAnalysisOptions::fast_probe_only()
        },
    )
    .unwrap();
    assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
    assert_eq!(
        report.cells[1].domain,
        Some(UcpValueDomain::exact(0.into()))
    );
    assert_eq!(
        validate_private_recovery_report::<Fr, _>(&circuit, 4, &input(), &report)
            .unwrap()
            .status,
        RecoveryValidationStatus::VerifiedDomains
    );
}

//Build p*a with canonical small constants: it is zero in Fr for every secret a.
#[derive(Clone, Copy)]
struct ModularTautology;
impl Circuit<Fr> for ModularTautology {
    type Config = (Column<Advice>, Selector);
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        *self
    }
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let a = meta.advice_column();
        let q = meta.selector();
        meta.create_gate("modular tautology", |meta| {
            let secret = meta.query_advice(a, Rotation::cur());
            let mut expression = Expression::Constant(Fr::from(0));
            for digit in Fr::MODULUS.trim_start_matches("0x").chars() {
                let digit = digit.to_digit(16).unwrap();
                for shift in (0..4).rev() {
                    expression = Expression::Scaled(Box::new(expression), Fr::from(2));
                    if (digit >> shift) & 1 == 1 {
                        expression = expression + secret.clone();
                    }
                }
            }
            vec![meta.query_selector(q) * expression]
        });
        (a, q)
    }
    fn synthesize(
        &self,
        (a, q): Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "free secret",
            |mut region| {
                q.enable(&mut region, 0)?;
                region.assign_advice(|| "secret", a, 0, || Value::known(Fr::from(7)))?;
                Ok(())
            },
        )
    }
}

#[test]
fn production_modulus_tautology_never_recovers_a_free_secret() {
    let circuit = ModularTautology;
    MockProver::run(4, &circuit, vec![])
        .unwrap()
        .assert_satisfied();
    let report = recover(&circuit);
    assert_eq!(report.cells[0].uniqueness, PrivateCellUniqueness::NonUnique);
    assert!(report.cells[0].domain.is_none());
}
