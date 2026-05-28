use super::{
    all_but_one::infer_all_but_one_zero,
    base_conv::infer_base_conversions_with_modulus,
    bigint_mul::infer_bigint_mul_with_modulus,
    cell::CellId,
    expr::UcpExpr,
    facts::UcpFacts,
    rules::{expression_is_unique, infer_assigned_cell_from_zero_equation},
    value::{
        infer_value_domains_from_zero_equation,
        infer_value_domains_from_zero_equation_with_modulus, UcpValueFacts,
    },
};
use num_bigint::BigInt;

//Egy expression végső UCP státusza
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpExpressionStatus {
    //A végső K alapján unique
    Unique,
    //A végső K alapján még nem bizonyított unique
    Unresolved,
}

//Egy expression indexéhez tartozó kiértékelési eredmény
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UcpExpressionResult {
    pub index: usize,
    pub status: UcpExpressionStatus,
}

//A megadott target/output cellák constrainedness ellenőrzésének eredménye
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UcpTargetCheck {
    pub checked_targets: usize,
    pub unique_targets: usize,
    pub unresolved_targets: Vec<CellId>,
}

impl UcpTargetCheck {
    //Igaz, ha nincs unresolved target cella
    pub fn all_targets_unique(&self) -> bool {
        self.unresolved_targets.is_empty()
    }
}

//A teljes UCP futás eredménye
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UcpResult {
    //A végső K halmaz
    pub facts: UcpFacts,
    //A végső Delta érték/domain információ
    pub value_facts: UcpValueFacts,
    //Hány expressiont ellenőriztünk
    pub checked_expressions: usize,
    //Hány expression lett unique
    pub unique_expressions: usize,
    //Hány expression maradt unresolved
    pub unresolved_expressions: usize,
    //Expressionenkénti státusz index alapján
    pub expression_results: Vec<UcpExpressionResult>,
}

impl UcpResult {
    //Igaz, ha minden expression unique lett
    pub fn all_expressions_unique(&self) -> bool {
        self.unresolved_expressions == 0
    }

    //Visszaadja az unresolved expressionök indexeit
    pub fn unresolved_indices(&self) -> Vec<usize> {
        self.expression_results
            .iter()
            .filter_map(|result| match result.status {
                UcpExpressionStatus::Unique => None,
                UcpExpressionStatus::Unresolved => Some(result.index),
            })
            .collect()
    }

    //Igaz, ha minden megadott target cella szerepel a végső K halmazban
    pub fn all_targets_unique(&self, targets: &[CellId]) -> bool {
        targets.iter().all(|target| self.facts.is_unique(target))
    }

    //Kigyűjti azokat a target cellákat, amelyek nem kerültek be a K halmazba
    pub fn unresolved_targets(&self, targets: &[CellId]) -> Vec<CellId> {
        targets
            .iter()
            .filter(|target| !self.facts.is_unique(target))
            .cloned()
            .collect()
    }

    //Összefoglaló target check eredményt készít
    pub fn check_targets(&self, targets: &[CellId]) -> UcpTargetCheck {
        let unresolved_targets = self.unresolved_targets(targets);

        UcpTargetCheck {
            checked_targets: targets.len(),
            unique_targets: targets.len() - unresolved_targets.len(),
            unresolved_targets,
        }
    }
}

//UCP futtatása value inference nélkül megadott kezdeti K halmazból
pub fn analyze_expressions(expressions: &[UcpExpr], initial_facts: UcpFacts) -> UcpResult {
    analyze_expressions_with_values(expressions, initial_facts, UcpValueFacts::new())
}

//UCP fixpoint futtatása kezdeti K és Delta információval, modulusfüggő szabályok nélkül
pub fn analyze_expressions_with_values(
    expressions: &[UcpExpr],
    initial_facts: UcpFacts,
    initial_value_facts: UcpValueFacts,
) -> UcpResult {
    analyze_expressions_with_optional_modulus(expressions, initial_facts, initial_value_facts, None)
}

//UCP fixpoint futtatása a circuit tényleges mezőmodulusával
pub fn analyze_expressions_with_values_and_modulus(
    expressions: &[UcpExpr],
    initial_facts: UcpFacts,
    initial_value_facts: UcpValueFacts,
    field_modulus: &BigInt,
) -> UcpResult {
    analyze_expressions_with_optional_modulus(
        expressions,
        initial_facts,
        initial_value_facts,
        Some(field_modulus),
    )
}

fn analyze_expressions_with_optional_modulus(
    expressions: &[UcpExpr],
    initial_facts: UcpFacts,
    initial_value_facts: UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> UcpResult {
    //K halmaz: unique-nak ismert cellák
    let mut facts = initial_facts;
    //Delta: ismert értékek és domainek
    let mut value_facts = initial_value_facts;
    //Ha Delta már induláskor pontos értéket tud egy cellára, abból uniqueness is következik
    for (cell, domain) in value_facts.domains() {
        if domain.is_singleton() {
            facts.mark_unique(cell.clone());
        }
    }
    //Addig futunk, amíg valamelyik szabály új információt tanul
    let mut changed = true;

    while changed {
        changed = false;

        for expr in expressions {
            //Először érték/domain információt próbálunk tanulni a zero equationből
            let value_inferences = match field_modulus {
                Some(field_modulus) => infer_value_domains_from_zero_equation_with_modulus(
                    expr,
                    &value_facts,
                    field_modulus,
                ),
                None => infer_value_domains_from_zero_equation(expr, &value_facts),
            };

            for (cell, domain) in value_inferences {
                let is_exact = domain.is_singleton();
                changed |= value_facts.mark_domain(cell.clone(), domain);
                //Konkrét egyértékű domainből uniqueness is következik
                if is_exact {
                    changed |= facts.mark_unique(cell);
                }
            }

            //Ha az expression már unique, nincs mit assign szabállyal tanulni belőle
            if expression_is_unique(expr, &facts) {
                continue;
            }

            //Assign-szerű szabály: egyetlen lineáris ismeretlen cellát unique-nak jelöl
            if let Some(cell) = infer_assigned_cell_from_zero_equation(expr, &facts) {
                changed |= facts.mark_unique(cell);
            }
        }

        //Több constraintes all-but-one-0 szabály futtatása
        for inference in infer_all_but_one_zero(expressions, &facts, &value_facts) {
            if let Some(value) = inference.value {
                changed |= value_facts.mark_known(inference.cell.clone(), value);
            }
            changed |= facts.mark_unique(inference.cell);
        }

        if let Some(field_modulus) = field_modulus {
            //Base conversion szabály futtatása a circuit tényleges field modulusával
            for inference in infer_base_conversions_with_modulus(
                expressions,
                &facts,
                &value_facts,
                field_modulus,
            ) {
                if let Some(value) = inference.value {
                    changed |= value_facts.mark_known(inference.cell.clone(), value);
                }
                changed |= facts.mark_unique(inference.cell);
            }

            //BigInt-Mul/lineáris rendszer szabály futtatása a circuit tényleges field modulusával
            for inference in infer_bigint_mul_with_modulus(expressions, &facts, field_modulus) {
                changed |= facts.mark_unique(inference.cell);
            }
        }
    }

    //Fixpoint után minden expressiont a végső K alapján osztályozunk
    let mut unique_expressions = 0;
    let mut unresolved_expressions = 0;
    let mut expression_results = Vec::with_capacity(expressions.len());

    for (index, expr) in expressions.iter().enumerate() {
        //Expression unique, ha a végső facts alapján expression_is_unique igaz rá
        let status = if expression_is_unique(expr, &facts) {
            unique_expressions += 1;
            UcpExpressionStatus::Unique
        } else {
            unresolved_expressions += 1;
            UcpExpressionStatus::Unresolved
        };

        expression_results.push(UcpExpressionResult { index, status });
    }

    //A teljes eredmény visszaadása a végső K-val és Deltával együtt
    UcpResult {
        facts,
        value_facts,
        checked_expressions: expressions.len(),
        unique_expressions,
        unresolved_expressions,
        expression_results,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit_analyzer::ucp::cell::CellId;

    //Azt ellenőrzi, hogy az engine külön tudja választani a unique és unresolved expressionöket
    #[test]
    fn classifies_unique_and_unresolved_expressions() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let facts = UcpFacts::from_iter([x.clone()]);
        let expressions = vec![
            UcpExpr::constant(),
            UcpExpr::add(UcpExpr::var(x), UcpExpr::constant()),
            UcpExpr::mul(UcpExpr::var(y), UcpExpr::constant()),
        ];

        let result = analyze_expressions(&expressions, facts);

        assert_eq!(result.checked_expressions, 3);
        assert_eq!(result.unique_expressions, 2);
        assert_eq!(result.unresolved_expressions, 1);
        assert_eq!(result.unresolved_indices(), vec![2]);
        assert!(!result.all_expressions_unique());
    }

    //Azt ellenőrzi, hogy minden expression unique esetén a summary is all unique
    #[test]
    fn reports_all_unique_when_every_expression_is_known() {
        let x = CellId::instance(0, 0);
        let y = CellId::fixed(0, 0);
        let facts = UcpFacts::from_iter([x.clone(), y.clone()]);
        let expressions = vec![
            UcpExpr::var(x),
            UcpExpr::neg(UcpExpr::scale(UcpExpr::var(y))),
        ];

        let result = analyze_expressions(&expressions, facts);

        assert_eq!(result.checked_expressions, 2);
        assert_eq!(result.unique_expressions, 2);
        assert_eq!(result.unresolved_expressions, 0);
        assert!(result.unresolved_indices().is_empty());
        assert!(result.all_expressions_unique());
    }

    //Azt ellenőrzi, hogy egy zero equationből az assign szabály új advice cellát tanul
    #[test]
    fn propagates_single_unknown_from_zero_equation() {
        let known = CellId::instance(0, 0);
        let unknown = CellId::advice(0, 0);
        let facts = UcpFacts::from_iter([known.clone()]);
        let expressions = vec![UcpExpr::add(
            UcpExpr::var(known.clone()),
            UcpExpr::var(unknown.clone()),
        )];

        let result = analyze_expressions(&expressions, facts);

        assert!(result.facts.is_unique(&known));
        assert!(result.facts.is_unique(&unknown));
        assert_eq!(result.facts.unique_cells().len(), 2);
        assert!(result.all_expressions_unique());
    }

    //Azt ellenőrzi, hogy a target check csak a megadott output/target cellákat nézi
    #[test]
    fn checks_target_cells_against_final_facts() {
        let known = CellId::instance(0, 0);
        let inferred = CellId::advice(0, 0);
        let unresolved = CellId::advice(1, 0);
        let facts = UcpFacts::from_iter([known.clone()]);
        let expressions = vec![UcpExpr::add(
            UcpExpr::var(known),
            UcpExpr::var(inferred.clone()),
        )];

        let result = analyze_expressions(&expressions, facts);
        let targets = vec![inferred, unresolved.clone()];
        let target_check = result.check_targets(&targets);

        assert!(!result.all_targets_unique(&targets));
        assert!(!target_check.all_targets_unique());
        assert_eq!(target_check.checked_targets, 2);
        assert_eq!(target_check.unique_targets, 1);
        assert_eq!(target_check.unresolved_targets, vec![unresolved]);
    }

    //Azt ellenőrzi, hogy boolean domain önmagában még nem jelent uniqueness-t
    #[test]
    fn root_domain_does_not_make_boolean_cell_unique_by_itself() {
        use crate::circuit_analyzer::ucp::value::UcpValueDomain;
        use num_bigint::BigInt;

        let b = CellId::advice(0, 0);
        let expressions = vec![UcpExpr::mul(
            UcpExpr::var(b.clone()),
            UcpExpr::add(UcpExpr::var(b.clone()), UcpExpr::known_constant_i64(-1)),
        )];

        let result = analyze_expressions(&expressions, UcpFacts::new());

        assert!(!result.facts.is_unique(&b));
        assert_eq!(
            result.value_facts.domain(&b),
            Some(
                &UcpValueDomain::finite_set([BigInt::from(0), BigInt::from(1)])
                    .expect("non-empty boolean domain")
            )
        );
    }

    //Azt ellenőrzi, hogy all-but-one-0 szabály az engine-ben is unique-ként jelöli a kimeneteket
    #[test]
    fn all_but_one_zero_marks_one_hot_outputs_unique() {
        use num_bigint::BigInt;

        let x = CellId::instance(0, 0);
        let e = CellId::instance(1, 0);
        let y0 = CellId::advice(0, 0);
        let y1 = CellId::advice(1, 0);
        let y2 = CellId::advice(2, 0);
        let product = |y: &CellId, root: i64| {
            UcpExpr::mul(
                UcpExpr::var(y.clone()),
                UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(-root)),
            )
        };
        let expressions = vec![
            product(&y0, 0),
            product(&y1, 1),
            product(&y2, 2),
            UcpExpr::add(
                UcpExpr::add(UcpExpr::var(y0.clone()), UcpExpr::var(y1.clone())),
                UcpExpr::add(
                    UcpExpr::var(y2.clone()),
                    UcpExpr::neg(UcpExpr::var(e.clone())),
                ),
            ),
        ];
        let facts = UcpFacts::from_iter([x.clone(), e.clone()]);
        let mut value_facts = UcpValueFacts::new();
        value_facts.mark_known(x, BigInt::from(1));
        value_facts.mark_known(e, BigInt::from(1));

        let result = analyze_expressions_with_values(&expressions, facts, value_facts);

        assert!(result.facts.is_unique(&y0));
        assert!(result.facts.is_unique(&y1));
        assert!(result.facts.is_unique(&y2));
        assert_eq!(result.value_facts.known_value(&y0), Some(&BigInt::from(0)));
        assert_eq!(result.value_facts.known_value(&y1), Some(&BigInt::from(1)));
        assert_eq!(result.value_facts.known_value(&y2), Some(&BigInt::from(0)));
    }

    //Azt ellenőrzi, hogy base-conv szabály az engine-ben is unique-ként jelöli a biteket
    #[test]
    fn base_conv_marks_binary_decomposition_bits_unique() {
        use crate::circuit_analyzer::ucp::{expr::UcpScalar, value::UcpValueDomain};
        use num_bigint::BigInt;

        let x = CellId::instance(0, 0);
        let b0 = CellId::advice(0, 0);
        let b1 = CellId::advice(1, 0);
        let b2 = CellId::advice(2, 0);
        let expr = UcpExpr::add(
            UcpExpr::add(
                UcpExpr::var(b0.clone()),
                UcpExpr::scale_by(UcpExpr::var(b1.clone()), UcpScalar::known_i64(2)),
            ),
            UcpExpr::add(
                UcpExpr::scale_by(UcpExpr::var(b2.clone()), UcpScalar::known_i64(4)),
                UcpExpr::neg(UcpExpr::var(x.clone())),
            ),
        );
        let facts = UcpFacts::from_iter([x.clone()]);
        let boolean_domain =
            UcpValueDomain::finite_set([BigInt::from(0), BigInt::from(1)]).unwrap();
        let mut value_facts = UcpValueFacts::new();
        value_facts.mark_known(x, BigInt::from(5));
        value_facts.mark_domain(b0.clone(), boolean_domain.clone());
        value_facts.mark_domain(b1.clone(), boolean_domain.clone());
        value_facts.mark_domain(b2.clone(), boolean_domain);

        let result = analyze_expressions_with_values_and_modulus(
            &[expr],
            facts,
            value_facts,
            &BigInt::from(101),
        );

        assert!(result.facts.is_unique(&b0));
        assert!(result.facts.is_unique(&b1));
        assert!(result.facts.is_unique(&b2));
        assert_eq!(result.value_facts.known_value(&b0), Some(&BigInt::from(1)));
        assert_eq!(result.value_facts.known_value(&b1), Some(&BigInt::from(0)));
        assert_eq!(result.value_facts.known_value(&b2), Some(&BigInt::from(1)));
    }

    //Azt ellenőrzi, hogy a BigInt-Mul/lineáris rendszer szabály az engine-ben is fut
    #[test]
    fn bigint_mul_marks_full_rank_linear_system_unique() {
        let a = CellId::instance(0, 0);
        let b = CellId::instance(1, 0);
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let facts = UcpFacts::from_iter([a.clone(), b.clone()]);
        let expressions = vec![
            UcpExpr::add(
                UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::var(y.clone())),
                UcpExpr::neg(UcpExpr::var(a)),
            ),
            UcpExpr::add(
                UcpExpr::add(
                    UcpExpr::var(x.clone()),
                    UcpExpr::neg(UcpExpr::var(y.clone())),
                ),
                UcpExpr::neg(UcpExpr::var(b)),
            ),
        ];

        let result = analyze_expressions_with_values_and_modulus(
            &expressions,
            facts,
            UcpValueFacts::new(),
            &BigInt::from(101),
        );

        assert!(result.facts.is_unique(&x));
        assert!(result.facts.is_unique(&y));
        assert!(result.all_expressions_unique());
    }

    #[cfg(feature = "use_zcash_halo2_proofs")]
    //Azt ellenőrzi, hogy Halo2 gate expressionök UCP-re fordítva is elemezhetők
    #[test]
    fn classifies_plonkish_constraint_system_gate_expressions() {
        use crate::circuit_analyzer::halo2_proofs_libs::*;
        use crate::circuit_analyzer::ucp::facts::initial_facts;
        use crate::circuit_analyzer::ucp::plonkish::expression_to_ucp_expr;

        let mut cs = ConstraintSystem::<Fr>::default();
        let unknown_advice = cs.advice_column();
        let fixed = cs.fixed_column();
        let instance = cs.instance_column();

        cs.create_gate("ucp engine example", |meta| {
            let unknown = meta.query_advice(unknown_advice, Rotation::cur());
            let fixed = meta.query_fixed(fixed);
            let public = meta.query_instance(instance, Rotation::cur());

            vec![
                fixed + public.clone() - Expression::Constant(Fr::from(3)),
                unknown + public - Expression::Constant(Fr::from(5)),
            ]
        });

        let expressions: Vec<UcpExpr> = cs.gates[0]
            .polys
            .iter()
            .map(|expr| expression_to_ucp_expr(expr, 0, 0))
            .collect();
        let facts = initial_facts([CellId::instance(0, 0)], [CellId::fixed(0, 0)]);

        let result = analyze_expressions(&expressions, facts);

        assert_eq!(result.checked_expressions, 2);
        assert_eq!(result.unique_expressions, 2);
        assert_eq!(result.unresolved_expressions, 0);
        assert!(result.unresolved_indices().is_empty());
        assert!(result.facts.is_unique(&CellId::advice(0, 0)));
    }

    #[cfg(feature = "use_zcash_halo2_proofs")]
    //Azt ellenőrzi, hogy plonkish expressionökből automatikusan kigyűjthetők az initial facts elemei
    #[test]
    fn extracts_initial_facts_from_plonkish_expressions() {
        use crate::circuit_analyzer::halo2_proofs_libs::*;
        use crate::circuit_analyzer::ucp::facts::initial_facts_from_expressions;
        use crate::circuit_analyzer::ucp::plonkish::expression_to_ucp_expr;

        let mut cs = ConstraintSystem::<Fr>::default();
        let public = cs.instance_column();
        let fixed = cs.fixed_column();
        let x = cs.advice_column();

        cs.create_gate("auto initial facts", |meta| {
            let public = meta.query_instance(public, Rotation::cur());
            let fixed = meta.query_fixed(fixed);
            let x = meta.query_advice(x, Rotation::cur());

            vec![x + public + fixed - Expression::Constant(Fr::from(9))]
        });

        let expressions: Vec<UcpExpr> = cs.gates[0]
            .polys
            .iter()
            .map(|expr| expression_to_ucp_expr(expr, 0, 0))
            .collect();
        let facts = initial_facts_from_expressions(&expressions);

        assert!(facts.is_unique(&CellId::instance(0, 0)));
        assert!(facts.is_unique(&CellId::fixed(0, 0)));
        assert!(!facts.is_unique(&CellId::advice(0, 0)));

        let result = analyze_expressions(&expressions, facts);

        assert!(result.facts.is_unique(&CellId::advice(0, 0)));
        assert!(result.all_expressions_unique());
    }

    #[cfg(feature = "use_zcash_halo2_proofs")]
    //Azt ellenőrzi, hogy aktív selectoros assignment láncon végig tud propagálni az UCP
    #[test]
    fn propagates_through_selected_plonkish_assignment_chain() {
        use crate::circuit_analyzer::halo2_proofs_libs::*;
        use crate::circuit_analyzer::ucp::cell::CellId;
        use crate::circuit_analyzer::ucp::facts::initial_facts;
        use crate::circuit_analyzer::ucp::plonkish::expression_to_ucp_expr_with_enabled_selector_indices;
        use std::collections::HashSet;

        let mut cs = ConstraintSystem::<Fr>::default();

        let public = cs.instance_column();
        let x = cs.advice_column();
        let y = cs.advice_column();
        let z = cs.advice_column();
        let dead = cs.advice_column();

        let s_chain = cs.selector();
        let s_dead = cs.selector();

        cs.create_gate("ucp selected chain", |meta| {
            let s_chain = meta.query_selector(s_chain);
            let s_dead = meta.query_selector(s_dead);

            let public = meta.query_instance(public, Rotation::cur());
            let x = meta.query_advice(x, Rotation::cur());
            let y = meta.query_advice(y, Rotation::cur());
            let z = meta.query_advice(z, Rotation::cur());
            let dead = meta.query_advice(dead, Rotation::cur());

            vec![
                // x = 5 - public
                s_chain.clone() * (x.clone() + public - Expression::Constant(Fr::from(5))),
                // y = 7 - x
                s_chain.clone() * (y.clone() + x - Expression::Constant(Fr::from(7))),
                // z = 2 * y - 11
                s_chain
                    * (z.clone()
                        - Expression::Constant(Fr::from(2)) * y
                        - Expression::Constant(Fr::from(11))),
                // This gate is inactive, so it must not make `dead` unique.
                s_dead * (dead + z - Expression::Constant(Fr::from(13))),
            ]
        });

        let selector_indices = HashSet::new();
        let enabled_selector_indices = HashSet::from([s_chain.0]);
        let expressions: Vec<UcpExpr> = cs.gates[0]
            .polys
            .iter()
            .map(|poly| {
                expression_to_ucp_expr_with_enabled_selector_indices(
                    poly,
                    0,
                    0,
                    &selector_indices,
                    &enabled_selector_indices,
                )
            })
            .collect();

        let facts = initial_facts([CellId::instance(0, 0)], []);
        let result = analyze_expressions(&expressions, facts);

        assert!(result.facts.is_unique(&CellId::instance(0, 0)));
        assert!(result.facts.is_unique(&CellId::advice(0, 0)));
        assert!(result.facts.is_unique(&CellId::advice(1, 0)));
        assert!(result.facts.is_unique(&CellId::advice(2, 0)));

        // The inactive gate contains `dead`, but UCP must not learn it.
        assert!(!result.facts.is_unique(&CellId::advice(3, 0)));

        assert_eq!(result.checked_expressions, 4);
        assert_eq!(result.unique_expressions, 4);
        assert_eq!(result.unresolved_expressions, 0);
        assert!(result.unresolved_indices().is_empty());
        assert!(result.all_expressions_unique());
    }
}
