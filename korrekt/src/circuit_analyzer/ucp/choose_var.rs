//Ez a modul a cikk ChooseVar(C, V) lépésének heurisztikus Plonkish megfelelője.
// A következtetési fixpont elérése után azt a cellát választja SMT-vizsgálatra,
// amelytől a legtöbb további UCP-következtetést várja.

use super::{
    cell::{CellId, CellKind},
    engine::simulate_expressions_with_relations_and_modulus,
    expr::UcpExpr,
    facts::UcpFacts,
    rules::expression_is_unique,
    value::UcpValueFacts,
};
use num_bigint::BigInt;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

#[derive(Clone, Debug, Eq, PartialEq)]
struct CandidateScore {
    cell: CellId,
    // A cella egyértelműségét feltételezve ennyi célcella lenne egyértelmű.
    unique_targets_after_simulation: usize,
    // Ennyi új célcella egyértelműségét várja a szimulációtól.
    newly_unique_targets: usize,
    // Azt jelzi, hogy a vizsgált cella célcella-e.
    is_target: bool,
    // A szimulációban újonnan egyértelművé váló cellák számát tárolja.
    newly_unique_cells: usize,
    // A szimulációban egyértelművé váló kifejezések számát tárolja.
    newly_unique_expressions: usize,
    // Ennyi kifejezésben szerepel, ahol egy további ismeretlen cella egyértelműségét segítheti.
    bridge_expressions: usize,
    // A még nem igazoltan egyértelmű kifejezések közötti előfordulásait számolja.
    unresolved_expression_count: usize,
    // A kifejezések közötti összes előfordulását számolja.
    expression_count: usize,
    // A célcelláktól mért gráftávolságot tárolja; a kisebbet részesíti előnyben.
    target_distance: usize,
}

// A cikk szerinti V = (O unio W) \ K halmazból választ cellát SMT-vizsgálatra.
pub(crate) fn choose_query_cell(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    value_facts: &UcpValueFacts,
    field_modulus: &BigInt,
    output_cells: &[CellId],
    witness_cells: &[CellId],
    queried_cells: &HashSet<CellId>,
) -> Option<CellId> {
    let _profile = super::profiling::scope("scheduler.choose_query");
    let candidates = collect_candidate_cells(output_cells, witness_cells, facts, queried_cells);
    if candidates.is_empty() {
        return None;
    }

    let expression_infos = expression_infos(expressions, facts);
    let target_distances = target_distances(&expression_infos, output_cells);
    let target_set: HashSet<CellId> = output_cells.iter().cloned().collect();
    let baseline_unique_expressions = count_unique_expressions(expressions, facts);
    let baseline_unique_targets = count_unique_targets(output_cells, facts);
    let baseline_unique_cells = facts.unique_cells().len();

    candidates
        .into_iter()
        .map(|cell| {
            score_candidate(
                cell,
                expressions,
                facts,
                value_facts,
                field_modulus,
                output_cells,
                &target_set,
                &expression_infos,
                &target_distances,
                baseline_unique_expressions,
                baseline_unique_targets,
                baseline_unique_cells,
            )
        })
        .max_by(compare_scores)
        .map(|score| score.cell)
}

fn collect_candidate_cells(
    output_cells: &[CellId],
    witness_cells: &[CellId],
    facts: &UcpFacts,
    queried_cells: &HashSet<CellId>,
) -> BTreeSet<CellId> {
    let mut candidates = BTreeSet::new();

    // Az O halmazból a kimeneti célcellákat veszi figyelembe.
    for output in output_cells {
        if !facts.is_unique(output) && !queried_cells.contains(output) {
            candidates.insert(output.clone());
        }
    }

    // A W halmazból az advice cellákat veszi figyelembe; instance és fixed cellát nem kérdez le.
    for witness in witness_cells {
        if matches!(witness.kind, CellKind::Advice)
            && !facts.is_unique(witness)
            && !queried_cells.contains(witness)
        {
            candidates.insert(witness.clone());
        }
    }

    candidates
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ExpressionInfo {
    cells: BTreeSet<CellId>,
    unresolved_cells: BTreeSet<CellId>,
    is_unique: bool,
}

fn expression_infos(expressions: &[UcpExpr], facts: &UcpFacts) -> Vec<ExpressionInfo> {
    expressions
        .iter()
        .map(|expr| {
            let mut cells = BTreeSet::new();
            collect_cells(expr, &mut cells);
            let unresolved_cells = cells
                .iter()
                .filter(|cell| matches!(cell.kind, CellKind::Advice) && !facts.is_unique(cell))
                .cloned()
                .collect();

            ExpressionInfo {
                cells,
                unresolved_cells,
                is_unique: expression_is_unique(expr, facts),
            }
        })
        .collect()
}

fn target_distances(
    expression_infos: &[ExpressionInfo],
    target_cells: &[CellId],
) -> HashMap<CellId, usize> {
    let mut graph: BTreeMap<CellId, BTreeSet<CellId>> = BTreeMap::new();

    for info in expression_infos {
        let advice_cells: Vec<CellId> = info
            .cells
            .iter()
            .filter(|cell| matches!(cell.kind, CellKind::Advice))
            .cloned()
            .collect();

        for left in &advice_cells {
            for right in &advice_cells {
                if left != right {
                    graph.entry(left.clone()).or_default().insert(right.clone());
                }
            }
        }
    }

    let mut distances = HashMap::new();
    let mut queue = VecDeque::new();

    for target in target_cells {
        if matches!(target.kind, CellKind::Advice) && distances.insert(target.clone(), 0).is_none()
        {
            queue.push_back(target.clone());
        }
    }

    while let Some(cell) = queue.pop_front() {
        let distance = distances[&cell];
        for next in graph.get(&cell).into_iter().flatten() {
            if distances.contains_key(next) {
                continue;
            }
            distances.insert(next.clone(), distance + 1);
            queue.push_back(next.clone());
        }
    }

    distances
}

#[allow(clippy::too_many_arguments)]
fn score_candidate(
    cell: CellId,
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    value_facts: &UcpValueFacts,
    field_modulus: &BigInt,
    target_cells: &[CellId],
    target_set: &HashSet<CellId>,
    expression_infos: &[ExpressionInfo],
    target_distances: &HashMap<CellId, usize>,
    baseline_unique_expressions: usize,
    baseline_unique_targets: usize,
    baseline_unique_cells: usize,
) -> CandidateScore {
    let mut simulated_facts = facts.clone();
    simulated_facts.mark_unique(cell.clone());
    let simulated = simulate_expressions_with_relations_and_modulus(
        expressions,
        &[],
        &[],
        simulated_facts,
        value_facts.for_hypothetical_reasoning(),
        field_modulus,
    );

    let expression_count = expression_infos
        .iter()
        .filter(|info| info.cells.contains(&cell))
        .count();
    let unresolved_expression_count = expression_infos
        .iter()
        .filter(|info| !info.is_unique && info.cells.contains(&cell))
        .count();
    let bridge_expressions = expression_infos
        .iter()
        .filter(|info| info.unresolved_cells.contains(&cell) && info.unresolved_cells.len() == 2)
        .count();
    let unique_targets_after_simulation = count_unique_targets(target_cells, &simulated.facts);

    CandidateScore {
        newly_unique_targets: unique_targets_after_simulation
            .saturating_sub(baseline_unique_targets),
        unique_targets_after_simulation,
        is_target: target_set.contains(&cell),
        newly_unique_cells: simulated
            .facts
            .unique_cells()
            .len()
            .saturating_sub(baseline_unique_cells),
        newly_unique_expressions: simulated
            .unique_expressions
            .saturating_sub(baseline_unique_expressions),
        bridge_expressions,
        unresolved_expression_count,
        expression_count,
        target_distance: target_distances.get(&cell).cloned().unwrap_or(usize::MAX),
        cell,
    }
}

fn compare_scores(left: &CandidateScore, right: &CandidateScore) -> Ordering {
    left.unique_targets_after_simulation
        .cmp(&right.unique_targets_after_simulation)
        .then(left.newly_unique_targets.cmp(&right.newly_unique_targets))
        // Elsősorban a várható UCP-következtetési hasznot rangsorolja; holtversenyben célcellát választ.
        .then(left.newly_unique_cells.cmp(&right.newly_unique_cells))
        .then(
            left.newly_unique_expressions
                .cmp(&right.newly_unique_expressions),
        )
        .then(left.is_target.cmp(&right.is_target))
        .then(left.bridge_expressions.cmp(&right.bridge_expressions))
        .then(
            left.unresolved_expression_count
                .cmp(&right.unresolved_expression_count),
        )
        .then(left.expression_count.cmp(&right.expression_count))
        // A távolságot fordított sorrendben hasonlítja össze, hogy a kisebb legyen kedvezőbb.
        .then(right.target_distance.cmp(&left.target_distance))
        // Holtversenyben a kisebb CellId-t választja, így determinisztikus marad a sorrend.
        .then(right.cell.cmp(&left.cell))
}

fn count_unique_expressions(expressions: &[UcpExpr], facts: &UcpFacts) -> usize {
    expressions
        .iter()
        .filter(|expr| expression_is_unique(expr, facts))
        .count()
}

fn count_unique_targets(target_cells: &[CellId], facts: &UcpFacts) -> usize {
    target_cells
        .iter()
        .filter(|target| facts.is_unique(target))
        .count()
}

fn collect_cells(expr: &UcpExpr, cells: &mut BTreeSet<CellId>) {
    match expr {
        UcpExpr::Var(cell) => {
            cells.insert(cell.clone());
        }
        UcpExpr::Const(_) => {}
        UcpExpr::Neg(inner) | UcpExpr::Scale(inner, _) => collect_cells(inner, cells),
        UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
            collect_cells(left, cells);
            collect_cells(right, cells);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit_analyzer::ucp::expr::UcpExpr;

    fn modulus() -> BigInt {
        BigInt::from(101)
    }

    // A teszt ellenőrzi, hogy több célcellát segítő köztes cellát választ.
    #[test]
    fn chooses_cell_with_best_ucp_simulated_gain() {
        let x = CellId::advice(0, 0);
        let e = CellId::instance(0, 0);
        let target_a = CellId::advice(1, 0);
        let target_b = CellId::advice(2, 0);
        let expressions = vec![
            UcpExpr::mul(UcpExpr::var(target_a.clone()), UcpExpr::var(x.clone())),
            UcpExpr::mul(
                UcpExpr::var(target_b.clone()),
                UcpExpr::add(UcpExpr::var(x.clone()), UcpExpr::known_constant_i64(-1)),
            ),
            UcpExpr::add(
                UcpExpr::add(
                    UcpExpr::var(target_a.clone()),
                    UcpExpr::var(target_b.clone()),
                ),
                UcpExpr::neg(UcpExpr::var(e.clone())),
            ),
        ];

        let chosen = choose_query_cell(
            &expressions,
            &UcpFacts::from_iter([e]),
            &UcpValueFacts::new(),
            &modulus(),
            &[target_a.clone(), target_b.clone()],
            &[x, target_a, target_b],
            &HashSet::new(),
        );

        assert_eq!(chosen, Some(CellId::advice(0, 0)));
    }

    // A teszt ellenőrzi, hogy valódi holtversenyben célcellát választ.
    #[test]
    fn prefers_target_when_gain_is_tied() {
        let target = CellId::advice(0, 0);
        let other = CellId::advice(1, 0);
        let expressions = vec![UcpExpr::add(
            UcpExpr::var(target.clone()),
            UcpExpr::var(other.clone()),
        )];

        let chosen = choose_query_cell(
            &expressions,
            &UcpFacts::new(),
            &UcpValueFacts::new(),
            &modulus(),
            &[target.clone()],
            &[target.clone(), other],
            &HashSet::new(),
        );

        assert_eq!(chosen, Some(target));
    }

    // A teszt ellenőrzi, hogy a már lekérdezett cellákat kihagyja.
    #[test]
    fn skips_already_queried_cells() {
        let first = CellId::advice(0, 0);
        let second = CellId::advice(1, 0);
        let expressions = vec![UcpExpr::var(first.clone()), UcpExpr::var(second.clone())];
        let queried = HashSet::from([first.clone()]);

        let chosen = choose_query_cell(
            &expressions,
            &UcpFacts::new(),
            &UcpValueFacts::new(),
            &modulus(),
            &[],
            &[first, second.clone()],
            &queried,
        );

        assert_eq!(chosen, Some(second));
    }

    // A teszt ellenőrzi, hogy nem vesz fel automatikusan minden hivatkozott advice cellát,
    // hanem kizárólag az explicit V = O unio W halmazból választ.
    #[test]
    fn uses_explicit_output_and_witness_candidate_set() {
        let allowed = CellId::advice(0, 0);
        let decoy = CellId::advice(1, 0);
        let expressions = vec![UcpExpr::var(allowed.clone()), UcpExpr::var(decoy)];

        let chosen = choose_query_cell(
            &expressions,
            &UcpFacts::new(),
            &UcpValueFacts::new(),
            &modulus(),
            &[],
            &[allowed.clone()],
            &HashSet::new(),
        );

        assert_eq!(chosen, Some(allowed));
    }
}
