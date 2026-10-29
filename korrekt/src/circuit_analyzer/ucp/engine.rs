use super::{
    all_but_one::{infer_all_but_one_zero, infer_all_but_one_zero_with_modulus},
    base_conv::{finite_base_candidates, infer_base_conversions_with_modulus},
    bigint_mul::infer_bigint_mul_with_modulus,
    cell::CellId,
    expr::UcpExpr,
    facts::UcpFacts,
    lookup::{disjoint, entries, UcpLookup},
    rules::{
        expression_is_unique, infer_assigned_cell_from_zero_equation,
        infer_assigned_cell_from_zero_equation_with_modulus,
    },
    value::{
        expression_domain_with_modulus, infer_domains_from_expression_domain_with_modulus,
        infer_linear_system_values_with_modulus, UcpValueDomain, UcpValueFacts,
    },
};

#[path = "propagation_cache.rs"]
mod propagation_cache;
use num_bigint::BigInt;
use propagation_cache::PropagationCache;

// Egy kifejezés végső UCP-státuszát jelöli.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UcpExpressionStatus {
    // A végső K alapján igazoltan egyértelmű.
    Unique,
    // A végső K alapján nem igazolta az egyértelműségét.
    Unresolved,
}

// Egy kifejezés indexéhez rendeli a kiértékelés eredményét.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UcpExpressionResult {
    pub index: usize,
    pub status: UcpExpressionStatus,
}

// A megadott kimeneti célcellák egyértelműségi ellenőrzését összesíti.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UcpTargetCheck {
    pub checked_targets: usize,
    pub unique_targets: usize,
    pub unresolved_targets: Vec<CellId>,
}

impl UcpTargetCheck {
    // Azt jelzi, hogy minden célcella egyértelműsége igazolt-e.
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
    // A megvizsgált kifejezések számát tárolja.
    pub checked_expressions: usize,
    // Az igazoltan egyértelmű kifejezések számát tárolja.
    pub unique_expressions: usize,
    // A nem igazoltan egyértelmű kifejezések számát tárolja.
    pub unresolved_expressions: usize,
    // Index szerint tárolja a kifejezések státuszát.
    pub expression_results: Vec<UcpExpressionResult>,
}

impl UcpResult {
    // Azt jelzi, hogy minden kifejezés egyértelműsége igazolt-e.
    pub fn all_expressions_unique(&self) -> bool {
        self.unresolved_expressions == 0
    }

    // Visszaadja a nem igazoltan egyértelmű kifejezések indexeit.
    pub fn unresolved_indices(&self) -> Vec<usize> {
        self.expression_results
            .iter()
            .filter_map(|result| match result.status {
                UcpExpressionStatus::Unique => None,
                UcpExpressionStatus::Unresolved => Some(result.index),
            })
            .collect()
    }

    // Azt jelzi, hogy minden megadott célcella szerepel-e a végső K halmazban.
    pub fn all_targets_unique(&self, targets: &[CellId]) -> bool {
        targets.iter().all(|target| self.facts.is_unique(target))
    }

    // Kigyűjti a K halmazból hiányzó célcellákat.
    pub fn unresolved_targets(&self, targets: &[CellId]) -> Vec<CellId> {
        targets
            .iter()
            .filter(|target| !self.facts.is_unique(target))
            .cloned()
            .collect()
    }

    // Elkészíti a célcellák ellenőrzési összefoglalóját.
    pub fn check_targets(&self, targets: &[CellId]) -> UcpTargetCheck {
        let unresolved_targets = self.unresolved_targets(targets);

        UcpTargetCheck {
            checked_targets: targets.len(),
            unique_targets: targets.len() - unresolved_targets.len(),
            unresolved_targets,
        }
    }
}

// A megadott kezdeti K halmazból indít UCP-elemzést, kezdeti értékadatok nélkül.
pub fn analyze_expressions(expressions: &[UcpExpr], initial_facts: UcpFacts) -> UcpResult {
    analyze_expressions_with_values(expressions, initial_facts, UcpValueFacts::new())
}

// Kezdeti K és Delta alapján fixpontig következtet, modulusfüggő szabályok nélkül.
pub fn analyze_expressions_with_values(
    expressions: &[UcpExpr],
    initial_facts: UcpFacts,
    initial_value_facts: UcpValueFacts,
) -> UcpResult {
    analyze_expressions_with_optional_modulus(
        expressions,
        &[],
        &[],
        initial_facts,
        initial_value_facts,
        None,
    )
}

// A kapcsolás tényleges testmodulusával futtatja az UCP-fixpontszámítást.
pub fn analyze_expressions_with_values_and_modulus(
    expressions: &[UcpExpr],
    initial_facts: UcpFacts,
    initial_value_facts: UcpValueFacts,
    field_modulus: &BigInt,
) -> UcpResult {
    analyze_expressions_with_optional_modulus(
        expressions,
        &[],
        &[],
        initial_facts,
        initial_value_facts,
        Some(field_modulus),
    )
}

/// A nullával egyenlő kifejezéseket és a véges tagsági feltételeket közös Delta-fixpontban kezeli.
pub fn analyze_expressions_with_domains_and_modulus(
    expressions: &[UcpExpr],
    expression_domains: &[(UcpExpr, UcpValueDomain)],
    initial_facts: UcpFacts,
    initial_value_facts: UcpValueFacts,
    field_modulus: &BigInt,
) -> UcpResult {
    analyze_expressions_with_optional_modulus(
        expressions,
        expression_domains,
        &[],
        initial_facts,
        initial_value_facts,
        Some(field_modulus),
    )
}

pub fn analyze_expressions_with_relations_and_modulus(
    expressions: &[UcpExpr],
    expression_domains: &[(UcpExpr, UcpValueDomain)],
    lookups: &[UcpLookup],
    initial_facts: UcpFacts,
    initial_value_facts: UcpValueFacts,
    field_modulus: &BigInt,
) -> UcpResult {
    analyze_expressions_with_optional_modulus(
        expressions,
        expression_domains,
        lookups,
        initial_facts,
        initial_value_facts,
        Some(field_modulus),
    )
}

/// Az ütemezési szimulációban kikapcsolja a beágyazott jelöltvizsgálatot.
pub(crate) fn simulate_expressions_with_relations_and_modulus(
    expressions: &[UcpExpr],
    expression_domains: &[(UcpExpr, UcpValueDomain)],
    lookups: &[UcpLookup],
    facts: UcpFacts,
    values: UcpValueFacts,
    modulus: &BigInt,
) -> UcpResult {
    run(
        expressions,
        expression_domains,
        lookups,
        facts,
        values,
        Some(modulus),
        false,
        None,
    )
    .0
}

fn analyze_expressions_with_optional_modulus(
    expressions: &[UcpExpr],
    expression_domains: &[(UcpExpr, UcpValueDomain)],
    lookups: &[UcpLookup],
    initial_facts: UcpFacts,
    initial_value_facts: UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> UcpResult {
    run(
        expressions,
        expression_domains,
        lookups,
        initial_facts,
        initial_value_facts,
        field_modulus,
        true,
        None,
    )
    .0
}

// A feltételes vizsgálatot korlátozza; nem indít rekurzív próbákat, és félbeszakadásból nem állapít meg cáfolatot.
const MAX_PACKED_PROBES: usize = 256;
const MAX_CONDITIONAL_ROUNDS: usize = 16;

fn run(
    expressions: &[UcpExpr],
    expression_domains: &[(UcpExpr, UcpValueDomain)],
    lookups: &[UcpLookup],
    initial_facts: UcpFacts,
    initial_value_facts: UcpValueFacts,
    field_modulus: Option<&BigInt>,
    allow_probes: bool,
    round_limit: Option<usize>,
) -> (UcpResult, bool) {
    let mut cache = PropagationCache::new(expressions, field_modulus);
    run_cached(
        expressions,
        expression_domains,
        lookups,
        initial_facts,
        initial_value_facts,
        field_modulus,
        allow_probes,
        round_limit,
        &mut cache,
    )
}

#[allow(clippy::too_many_arguments)]
fn run_cached(
    expressions: &[UcpExpr],
    expression_domains: &[(UcpExpr, UcpValueDomain)],
    lookups: &[UcpLookup],
    initial_facts: UcpFacts,
    initial_value_facts: UcpValueFacts,
    field_modulus: Option<&BigInt>,
    allow_probes: bool,
    round_limit: Option<usize>,
    cache: &mut PropagationCache<'_>,
) -> (UcpResult, bool) {
    let _profile = super::profiling::scope(if allow_probes {
        "ucp.propagation"
    } else if round_limit.is_some() {
        "ucp.conditional"
    } else {
        "ucp.simulation"
    });
    // A kezdeti pontos tényekből levezetett sorok minden leszármazott hipotetikus ágban is érvényesek.
    cache.prepare_relations(&initial_value_facts);
    let mut inconsistent = false;
    let mut probes_left = MAX_PACKED_PROBES;
    let mut rounds = 0;
    // A K halmazban az igazoltan egyértelmű cellákat tartja nyilván.
    let mut facts = initial_facts;
    //Delta: ismert értékek és domainek
    let mut value_facts = initial_value_facts;
    // A kezdeti egyelemű lefedő domainekből egyértelműséget is bejegyez.
    for (cell, domain) in value_facts.domains() {
        if domain.is_singleton() {
            facts.mark_unique(cell.clone());
        }
    }
    // Addig ismétli a szabályokat, amíg új tényt tanul, vagy eléri a feltételes körkorlátot.
    let mut changed = true;

    while changed {
        if round_limit.is_some_and(|limit| rounds >= limit) {
            break;
        }
        rounds += 1;
        changed = false;

        for (index, expr) in expressions.iter().enumerate() {
            // A nullával egyenlő kifejezésből először érték- és domainkövetkeztetést végez.
            // Az új domainből származó pontos értéket a következő szabályok is felhasználhatják.
            let value_inferences = {
                let _profile = super::profiling::scope("ucp.equation_domains");
                cache.infer(index, &value_facts)
            };

            for (cell, domain) in value_inferences {
                changed |= learn_domain(
                    cell.clone(),
                    domain,
                    &mut value_facts,
                    field_modulus,
                    &mut inconsistent,
                );
                // Az egyelemű lefedő domainből egyértelműséget is bejegyez.
                if value_facts.known_value(&cell).is_some() {
                    changed |= facts.mark_unique(cell);
                }
            }

            // Az egyértelmű kifejezést kihagyja az új cellát kereső Assign-vizsgálatból.
            if expression_is_unique(expr, &facts) {
                continue;
            }

            // Az Assign szabállyal egyetlen lineáris ismeretlen cella egyértelműségét igazolja.
            let assigned = {
                let _profile = super::profiling::scope("ucp.assign");
                match field_modulus {
                    Some(modulus) => {
                        infer_assigned_cell_from_zero_equation_with_modulus(expr, &facts, modulus)
                    }
                    None => infer_assigned_cell_from_zero_equation(expr, &facts),
                }
            };
            if let Some(cell) = assigned {
                changed |= facts.mark_unique(cell);
            }
        }

        // Az All-But-One-0 szabályt több kényszeren együttesen alkalmazza.
        let all_but_one = {
            let _profile = super::profiling::scope("ucp.all_but_one");
            match field_modulus {
                Some(modulus) => {
                    infer_all_but_one_zero_with_modulus(expressions, &facts, &value_facts, modulus)
                }
                None => infer_all_but_one_zero(expressions, &facts, &value_facts),
            }
        };
        for inference in all_but_one {
            if let Some(value) = inference.value {
                changed |= learn_domain(
                    inference.cell.clone(),
                    UcpValueDomain::exact(value),
                    &mut value_facts,
                    field_modulus,
                    &mut inconsistent,
                );
            }
            changed |= facts.mark_unique(inference.cell);
        }

        if let Some(field_modulus) = field_modulus {
            {
                let _profile = super::profiling::scope("ucp.lookups");
                // A lookup-vetületeket újra feldolgozza, ha más egyenletekből új operandusértéket tanul.
                for (expr, domain) in expression_domains {
                    for (cell, domain) in infer_domains_from_expression_domain_with_modulus(
                        expr,
                        domain,
                        &value_facts,
                        field_modulus,
                    ) {
                        changed |= learn_domain(
                            cell.clone(),
                            domain,
                            &mut value_facts,
                            Some(field_modulus),
                            &mut inconsistent,
                        );
                        if value_facts.known_value(&cell).is_some() {
                            changed |= facts.mark_unique(cell);
                        }
                    }
                }
                for lookup in lookups {
                    for (cell, domain) in lookup.infer(&value_facts, field_modulus) {
                        changed |= learn_domain(
                            cell.clone(),
                            domain,
                            &mut value_facts,
                            Some(field_modulus),
                            &mut inconsistent,
                        );
                        if value_facts.known_value(&cell).is_some() {
                            changed |= facts.mark_unique(cell);
                        }
                    }
                }
            }
            // A rangvizsgálat mellett konkrét megoldást is keres, amely további Delta-következtetést indíthat.
            let linear_values = {
                let _profile = super::profiling::scope("ucp.linear_systems");
                infer_linear_system_values_with_modulus(expressions, &value_facts, field_modulus)
            };
            for (cell, value) in linear_values {
                changed |= learn_domain(
                    cell.clone(),
                    UcpValueDomain::exact(value),
                    &mut value_facts,
                    Some(field_modulus),
                    &mut inconsistent,
                );
                if value_facts.known_value(&cell).is_some() {
                    changed |= facts.mark_unique(cell);
                }
            }
            // Az alulhatározott lineáris sorokból is átviszi a tartomány- és intervallumkorlátokat.
            let (domains, conflict) = cache.infer_relations(&value_facts);
            inconsistent |= conflict;
            for (cell, domain) in domains {
                changed |= learn_domain(
                    cell.clone(),
                    domain,
                    &mut value_facts,
                    Some(field_modulus),
                    &mut inconsistent,
                );
                if value_facts.known_value(&cell).is_some() {
                    changed |= facts.mark_unique(cell);
                }
            }
            // A Base-Conv szabályt a kapcsolás tényleges testmodulusával futtatja.
            let base_conversions = {
                let _profile = super::profiling::scope("ucp.base_conversion");
                infer_base_conversions_with_modulus(
                    expressions,
                    &facts,
                    &value_facts,
                    field_modulus,
                )
            };
            for inference in base_conversions {
                if let Some(value) = inference.value {
                    changed |= learn_domain(
                        inference.cell.clone(),
                        UcpValueDomain::exact(value),
                        &mut value_facts,
                        Some(field_modulus),
                        &mut inconsistent,
                    );
                }
                changed |= facts.mark_unique(inference.cell);
            }

            // A BigInt-Mul szabályt a kapcsolás tényleges testmodulusával futtatja.
            let bigint_inferences = {
                let _profile = super::profiling::scope("ucp.bigint_mul");
                infer_bigint_mul_with_modulus(expressions, &facts, field_modulus)
            };
            for inference in bigint_inferences {
                changed |= facts.mark_unique(inference.cell);
            }
            if round_limit.is_some() {
                inconsistent |= constraints_inconsistent(
                    expressions,
                    expression_domains,
                    lookups,
                    &value_facts,
                    field_modulus,
                    cache,
                );
            }
            if inconsistent {
                break;
            }
            // A rendes fixpont után külön másolaton kipróbálja a csomagolt értékek jelöltjeit.
            // Csak bizonyított ellentmondásnál zár ki értéket; a hipotetikus tényeket nem másolja vissza.
            if !changed && allow_probes && probes_left > 0 {
                for candidate in finite_base_candidates(expressions, &value_facts, field_modulus) {
                    let mut kept = std::collections::BTreeSet::new();
                    for (value, digits) in candidate.branches {
                        // Elfogyott keretnél megtartja a nem vizsgált jelöltet a lefedés megőrzéséhez.
                        if probes_left == 0 {
                            kept.insert(value);
                            continue;
                        }
                        probes_left -= 1;
                        let Some(digits) = digits else {
                            continue;
                        };
                        let mut hypothetical = value_facts.for_hypothetical_reasoning();
                        let mut refuted = false;
                        for (cell, exact) in
                            std::iter::once((candidate.packed.clone(), value.clone())).chain(digits)
                        {
                            learn_domain(
                                cell,
                                UcpValueDomain::exact(exact),
                                &mut hypothetical,
                                Some(field_modulus),
                                &mut refuted,
                            );
                        }
                        // A feltételes futásban kikapcsolja a további jelöltpróbákat, és körkorlátot ad.
                        if !refuted {
                            refuted = run_cached(
                                expressions,
                                expression_domains,
                                lookups,
                                facts.clone(),
                                hypothetical,
                                Some(field_modulus),
                                false,
                                Some(MAX_CONDITIONAL_ROUNDS),
                                cache,
                            )
                            .1;
                        }
                        if !refuted {
                            kept.insert(value);
                        }
                    }
                    if let Some(domain) = UcpValueDomain::finite_set(kept) {
                        changed |= learn_domain(
                            candidate.packed.clone(),
                            domain,
                            &mut value_facts,
                            Some(field_modulus),
                            &mut inconsistent,
                        );
                        if value_facts.known_value(&candidate.packed).is_some() {
                            changed |= facts.mark_unique(candidate.packed);
                        }
                    }
                }
            }
        }
    }

    // A végső K alapján osztályozza a kifejezéseket.
    let mut unique_expressions = 0;
    let mut unresolved_expressions = 0;
    let mut expression_results = Vec::with_capacity(expressions.len());

    for (index, expr) in expressions.iter().enumerate() {
        // A kifejezést az expression_is_unique eredménye alapján minősíti egyértelműnek.
        let status = if expression_is_unique(expr, &facts) {
            unique_expressions += 1;
            UcpExpressionStatus::Unique
        } else {
            unresolved_expressions += 1;
            UcpExpressionStatus::Unresolved
        };

        expression_results.push(UcpExpressionResult { index, status });
    }

    // A végső K és Delta mellett visszaadja az osztályozás eredményét.
    (
        UcpResult {
            facts,
            value_facts,
            checked_expressions: expressions.len(),
            unique_expressions,
            unresolved_expressions,
            expression_results,
        },
        inconsistent,
    )
}

// A domainütközést külön jelzi; a tároló önmagában nem reprezentál üres megoldáshalmazt.
fn learn_domain(
    cell: CellId,
    domain: UcpValueDomain,
    values: &mut UcpValueFacts,
    modulus: Option<&BigInt>,
    inconsistent: &mut bool,
) -> bool {
    if let (Some(modulus), Some(existing)) = (modulus, values.domain(&cell)) {
        *inconsistent |= disjoint(existing, &domain, modulus);
    }
    values.mark_domain(cell, domain)
}

fn constraints_inconsistent(
    expressions: &[UcpExpr],
    domains: &[(UcpExpr, UcpValueDomain)],
    lookups: &[UcpLookup],
    values: &UcpValueFacts,
    modulus: &BigInt,
    cache: &mut PropagationCache<'_>,
) -> bool {
    let _profile = super::profiling::scope("ucp.consistency");
    expressions.iter().enumerate().any(|(index, _)| {
        cache
            .evaluate(index, values)
            .is_some_and(|domain| !entries(&domain).contains(&BigInt::from(0)))
    }) || domains.iter().any(|(expr, required)| {
        expression_domain_with_modulus(expr, values, modulus)
            .is_some_and(|domain| disjoint(&domain, required, modulus))
    }) || lookups
        .iter()
        .any(|lookup| lookup.inconsistent(values, modulus))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit_analyzer::ucp::cell::CellId;

    #[test]
    fn propagation_cache_matches_uncached_conditional_reasoning() {
        let x = CellId::advice(0, 0);
        let a = CellId::advice(1, 0);
        let b = CellId::advice(2, 0);
        let expressions = [
            UcpExpr::mul(
                UcpExpr::var(a.clone()),
                UcpExpr::add(
                    UcpExpr::var(a.clone()),
                    UcpExpr::known_constant((-1).into()),
                ),
            ),
            UcpExpr::mul(
                UcpExpr::var(b.clone()),
                UcpExpr::add(
                    UcpExpr::var(b.clone()),
                    UcpExpr::known_constant((-1).into()),
                ),
            ),
            UcpExpr::add(
                UcpExpr::var(x.clone()),
                UcpExpr::neg(UcpExpr::add(
                    UcpExpr::var(a.clone()),
                    UcpExpr::scale_by(
                        UcpExpr::var(b.clone()),
                        super::super::expr::UcpScalar::known_i64(2),
                    ),
                )),
            ),
        ];
        let lookup = UcpLookup::new(
            vec![UcpExpr::var(a.clone()), UcpExpr::var(b.clone())],
            vec![vec![0.into(), 1.into()], vec![1.into(), 0.into()]],
        )
        .unwrap();
        for modulus in [17, 31, 97].map(BigInt::from) {
            for target in 0..4 {
                let mut values = UcpValueFacts::new();
                values.mark_domain(
                    x.clone(),
                    UcpValueDomain::finite_set([target.into(), ((target + 1) % 4).into()]).unwrap(),
                );
                let mut cached = PropagationCache::new(&expressions, Some(&modulus));
                let mut uncached = PropagationCache::with_capacity(&expressions, Some(&modulus), 0);
                let actual = run_cached(
                    &expressions,
                    &[],
                    &[lookup.clone()],
                    UcpFacts::new(),
                    values.clone(),
                    Some(&modulus),
                    true,
                    None,
                    &mut cached,
                );
                let expected = run_cached(
                    &expressions,
                    &[],
                    &[lookup.clone()],
                    UcpFacts::new(),
                    values,
                    Some(&modulus),
                    true,
                    None,
                    &mut uncached,
                );
                assert_eq!(actual, expected);
            }
        }
    }

    #[test]
    fn relational_lookup_domains_join_the_equation_fixpoint() {
        let cells: Vec<_> = (0..3).map(|row| CellId::advice(0, row)).collect();
        let digit_domain = UcpValueDomain::finite_set((0..4).map(BigInt::from)).unwrap();
        let memberships: Vec<_> = (0..2)
            .map(|row| {
                (
                    UcpExpr::add(
                        UcpExpr::var(cells[row].clone()),
                        UcpExpr::scale_by(
                            UcpExpr::var(cells[row + 1].clone()),
                            super::super::expr::UcpScalar::known_i64(-4),
                        ),
                    ),
                    digit_domain.clone(),
                )
            })
            .collect();
        let modulus = BigInt::from(97);
        let unresolved = analyze_expressions_with_domains_and_modulus(
            &[],
            &memberships,
            UcpFacts::new(),
            UcpValueFacts::new(),
            &modulus,
        );
        assert!(
            unresolved.value_facts.domains().is_empty(),
            "No assumed final zero"
        );
        let result = analyze_expressions_with_domains_and_modulus(
            &[UcpExpr::var(cells[2].clone())],
            &memberships,
            UcpFacts::new(),
            UcpValueFacts::new(),
            &modulus,
        );
        assert_eq!(
            result.value_facts.domain(&cells[0]),
            Some(&UcpValueDomain::finite_set((0..16).map(BigInt::from)).unwrap())
        );
        assert_eq!(result.value_facts.domain(&cells[1]), Some(&digit_domain));
        assert_eq!(
            result.value_facts.known_value(&cells[2]),
            Some(&BigInt::from(0))
        );
        assert!(!result.facts.is_unique(&cells[0]));
    }

    #[test]
    fn relational_lookup_projection_preserves_holes() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(0, 1);
        let holes = UcpValueDomain::finite_set([BigInt::from(0), BigInt::from(2)]).unwrap();
        let mut values = UcpValueFacts::new();
        values.mark_domain(y.clone(), holes.clone());
        let expr = UcpExpr::add(
            UcpExpr::var(x.clone()),
            UcpExpr::scale_by(
                UcpExpr::var(y),
                super::super::expr::UcpScalar::known_i64(-4),
            ),
        );
        let result = analyze_expressions_with_domains_and_modulus(
            &[],
            &[(expr, holes)],
            UcpFacts::new(),
            values,
            &BigInt::from(97),
        );
        assert_eq!(
            result.value_facts.domain(&x),
            Some(&UcpValueDomain::finite_set([0, 2, 8, 10].into_iter().map(BigInt::from)).unwrap())
        );
    }

    #[test]
    fn lookup_domain_intersection_can_establish_uniqueness() {
        let x = CellId::advice(0, 0);
        let mut values = UcpValueFacts::new();
        values.mark_domain(
            x.clone(),
            UcpValueDomain::finite_set([0, 1].into_iter().map(BigInt::from)).unwrap(),
        );
        let domain = UcpValueDomain::finite_set([1, 2].into_iter().map(BigInt::from)).unwrap();
        let result = analyze_expressions_with_domains_and_modulus(
            &[],
            &[(UcpExpr::var(x.clone()), domain)],
            UcpFacts::new(),
            values,
            &BigInt::from(97),
        );
        assert_eq!(result.value_facts.known_value(&x), Some(&BigInt::from(1)));
        assert!(result.facts.is_unique(&x));
    }

    // A teszt ellenőrzi az egyértelmű és a még nem igazolt kifejezések megkülönböztetését.
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

    // A teszt ellenőrzi, hogy minden egyértelmű kifejezés esetén az összesítés is sikert jelez.
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

    // A teszt ellenőrzi, hogy az Assign szabály egy egyenletből új advice cellát határoz meg.
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

    // A teszt ellenőrzi, hogy a célcella-ellenőrzés csak a megadott célokra vonatkozik.
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

    // A teszt ellenőrzi, hogy a {0,1} domain önmagában nem igazol egyértelműséget.
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

    // A teszt ellenőrzi, hogy az All-But-One-0 szabály a kimenetek egyértelműségét bejegyzi.
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

    // A teszt ellenőrzi, hogy a Base-Conv szabály a bitek egyértelműségét bejegyzi.
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

    // A teszt ellenőrzi, hogy már egyértelmű cellák értékvisszaállítása is elindít nemlineáris következtetést.
    #[test]
    fn linear_system_values_unlock_nonlinear_value_inference() {
        let u = CellId::instance(0, 0);
        let v = CellId::instance(1, 0);
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let out = CellId::advice(2, 0);
        let facts = UcpFacts::from_iter([u.clone(), v.clone(), x.clone(), y.clone()]);
        let mut values = UcpValueFacts::new();
        values.mark_known(u.clone(), BigInt::from(10));
        values.mark_known(v.clone(), BigInt::from(2));
        let expressions = vec![
            UcpExpr::add(
                UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::var(y.clone())),
                UcpExpr::neg(UcpExpr::var(u)),
            ),
            UcpExpr::add(
                UcpExpr::add(
                    UcpExpr::var(x.clone()),
                    UcpExpr::neg(UcpExpr::var(y.clone())),
                ),
                UcpExpr::neg(UcpExpr::var(v)),
            ),
            UcpExpr::add(
                UcpExpr::mul(UcpExpr::var(x.clone()), UcpExpr::var(x.clone())),
                UcpExpr::neg(UcpExpr::var(out.clone())),
            ),
        ];
        let result = analyze_expressions_with_values_and_modulus(
            &expressions,
            facts,
            values,
            &BigInt::from(101),
        );
        for (cell, value) in [(x, 6), (y, 4), (out, 36)] {
            assert!(result.facts.is_unique(&cell));
            assert_eq!(
                result.value_facts.known_value(&cell),
                Some(&BigInt::from(value))
            );
        }
    }

    // A teszt ellenőrzi a BigInt-Mul szabály beillesztését az UCP-futásba.
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
    // A teszt ellenőrzi a Halo2-kapuk UCP-re fordított kifejezéseinek elemzését.
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
    // A teszt ellenőrzi a kezdeti tények kigyűjtését PLONKish kifejezésekből.
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
    // A teszt ellenőrzi az aktív szelektorral vezérelt értékadási lánc propagációját.
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
                // Az inaktív kapuból nem állapíthatja meg a dead cella egyértelműségét.
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

        // A teszt ellenőrzi, hogy az inaktív kapuban szereplő dead celláról nem tanul új tényt.
        assert!(!result.facts.is_unique(&CellId::advice(3, 0)));

        assert_eq!(result.checked_expressions, 4);
        assert_eq!(result.unique_expressions, 4);
        assert_eq!(result.unresolved_expressions, 0);
        assert!(result.unresolved_indices().is_empty());
        assert!(result.all_expressions_unique());
    }
}
