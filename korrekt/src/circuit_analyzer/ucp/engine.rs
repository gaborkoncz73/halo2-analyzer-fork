use super::{expr::UcpExpr, facts::UcpFacts, rules::expression_is_unique};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpExpressionStatus {
    Unique,
    Unresolved,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UcpExpressionResult {
    pub index: usize,
    pub status: UcpExpressionStatus,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UcpResult {
    pub facts: UcpFacts,
    pub checked_expressions: usize,
    pub unique_expressions: usize,
    pub unresolved_expressions: usize,
    pub expression_results: Vec<UcpExpressionResult>,
}

impl UcpResult {
    pub fn all_expressions_unique(&self) -> bool {
        self.unresolved_expressions == 0
    }

    pub fn unresolved_indices(&self) -> Vec<usize> {
        self.expression_results
            .iter()
            .filter_map(|result| match result.status {
                UcpExpressionStatus::Unique => None,
                UcpExpressionStatus::Unresolved => Some(result.index),
            })
            .collect()
    }
}

/// Runs the first lightweight UCP pass over already-extracted UCP expressions.
///
/// This phase only applies expression-level uniqueness rules. It does not
/// infer new unique cells yet; later propagation rules will extend the facts
/// in a fixpoint loop.
pub fn analyze_expressions(expressions: &[UcpExpr], initial_facts: UcpFacts) -> UcpResult {
    let mut unique_expressions = 0;
    let mut unresolved_expressions = 0;
    let mut expression_results = Vec::with_capacity(expressions.len());

    for (index, expr) in expressions.iter().enumerate() {
        let status = if expression_is_unique(expr, &initial_facts) {
            unique_expressions += 1;
            UcpExpressionStatus::Unique
        } else {
            unresolved_expressions += 1;
            UcpExpressionStatus::Unresolved
        };

        expression_results.push(UcpExpressionResult { index, status });
    }

    UcpResult {
        facts: initial_facts,
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

    #[test]
    fn keeps_initial_facts_unchanged_in_expression_only_phase() {
        let known = CellId::instance(0, 0);
        let unknown = CellId::advice(0, 0);
        let facts = UcpFacts::from_iter([known.clone()]);
        let expressions = vec![UcpExpr::add(
            UcpExpr::var(known.clone()),
            UcpExpr::var(unknown.clone()),
        )];

        let result = analyze_expressions(&expressions, facts);

        assert!(result.facts.is_unique(&known));
        assert!(!result.facts.is_unique(&unknown));
        assert_eq!(result.facts.unique_cells().len(), 1);
        assert!(!result.all_expressions_unique());
    }

    #[cfg(feature = "use_zcash_halo2_proofs")]
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
        assert_eq!(result.unique_expressions, 1);
        assert_eq!(result.unresolved_expressions, 1);
        assert_eq!(result.unresolved_indices(), vec![1]);
    }
}
