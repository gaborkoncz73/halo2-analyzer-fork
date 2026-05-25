//Ez a modul a cikk ChooseVar(C, V) lépésének heurisztikus Plonkish megfelelője.
//A cél az, hogy amikor az UCP fixpoint megakad, ne véletlenszerű/első advice cellát
//kérdezzünk SMT-től, hanem azt, amelyik várhatóan a legtöbb további UCP propagációt indítja el.

use super::{
    cell::{CellId, CellKind},
    engine::analyze_expressions_with_values_and_modulus,
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
    //Hány target lenne unique, ha ezt a cellát SMT unique-nak bizonyítaná
    unique_targets_after_simulation: usize,
    //Hány új targetet tanulnánk
    newly_unique_targets: usize,
    //Maga a cella target-e
    is_target: bool,
    //Hány új unique cellát tanulna az UCP szimuláció
    newly_unique_cells: usize,
    //Hány expression válna unique-ká
    newly_unique_expressions: usize,
    //Hány olyan expressionben szerepel, ahol egy második unknown cellát nyithat meg
    bridge_expressions: usize,
    //Hány még unresolved expressionben szerepel
    unresolved_expression_count: usize,
    //Hány expressionben szerepel összesen
    expression_count: usize,
    //Target graph távolság: kisebb jobb
    target_distance: usize,
}

//Kiválasztja, melyik cellára kérdezzünk rá SMT-vel
pub(crate) fn choose_query_cell(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    value_facts: &UcpValueFacts,
    field_modulus: &BigInt,
    target_cells: &[CellId],
    queried_cells: &HashSet<CellId>,
) -> Option<CellId> {
    let candidates = collect_candidate_cells(expressions, facts, target_cells, queried_cells);
    if candidates.is_empty() {
        return None;
    }

    let expression_infos = expression_infos(expressions, facts);
    let target_distances = target_distances(&expression_infos, target_cells);
    let target_set: HashSet<CellId> = target_cells.iter().cloned().collect();
    let baseline_unique_expressions = count_unique_expressions(expressions, facts);
    let baseline_unique_targets = count_unique_targets(target_cells, facts);
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
                target_cells,
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
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    target_cells: &[CellId],
    queried_cells: &HashSet<CellId>,
) -> BTreeSet<CellId> {
    let mut candidates = BTreeSet::new();

    //Targetek mindig jelöltek lehetnek, mert ezek döntik el a végső választ
    for target in target_cells {
        if !facts.is_unique(target) && !queried_cells.contains(target) {
            candidates.insert(target.clone());
        }
    }

    //Nem-target esetben csak advice cellát kérdezünk SMT-vel
    for expr in expressions {
        collect_advice_cells(expr, &mut candidates);
    }

    candidates
        .into_iter()
        .filter(|cell| !facts.is_unique(cell) && !queried_cells.contains(cell))
        .collect()
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
    let simulated = analyze_expressions_with_values_and_modulus(
        expressions,
        simulated_facts,
        value_facts.clone(),
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
        //Előbb a várható UCP "lavina" számít; targetet csak valódi döntetlenben preferálunk
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
        //Távolságnál a kisebb jobb, ezért fordítva hasonlítjuk
        .then(right.target_distance.cmp(&left.target_distance))
        //Deterministikus tie-break: kisebb CellId nyer
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

fn collect_advice_cells(expr: &UcpExpr, cells: &mut BTreeSet<CellId>) {
    match expr {
        UcpExpr::Var(cell) => {
            if matches!(cell.kind, CellKind::Advice) {
                cells.insert(cell.clone());
            }
        }
        UcpExpr::Const(_) => {}
        UcpExpr::Neg(inner) | UcpExpr::Scale(inner, _) => collect_advice_cells(inner, cells),
        UcpExpr::Add(left, right) | UcpExpr::Mul(left, right) => {
            collect_advice_cells(left, cells);
            collect_advice_cells(right, cells);
        }
    }
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

    //Azt ellenőrzi, hogy ha egy köztes cella több targetet nyit meg, azt választjuk
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
            &[target_a, target_b],
            &HashSet::new(),
        );

        assert_eq!(chosen, Some(x));
    }

    //Azt ellenőrzi, hogy valódi holtversenyben target cellát választunk
    #[test]
    fn prefers_target_when_gain_is_tied() {
        let target = CellId::advice(0, 0);
        let other = CellId::advice(1, 0);
        let expressions = vec![UcpExpr::add(
            UcpExpr::var(target.clone()),
            UcpExpr::var(other),
        )];

        let chosen = choose_query_cell(
            &expressions,
            &UcpFacts::new(),
            &UcpValueFacts::new(),
            &modulus(),
            &[target.clone()],
            &HashSet::new(),
        );

        assert_eq!(chosen, Some(target));
    }

    //Azt ellenőrzi, hogy a már lekérdezett cellákat kihagyjuk
    #[test]
    fn skips_already_queried_cells() {
        let first = CellId::advice(0, 0);
        let second = CellId::advice(1, 0);
        let expressions = vec![UcpExpr::var(first.clone()), UcpExpr::var(second.clone())];
        let queried = HashSet::from([first]);

        let chosen = choose_query_cell(
            &expressions,
            &UcpFacts::new(),
            &UcpValueFacts::new(),
            &modulus(),
            &[],
            &queried,
        );

        assert_eq!(chosen, Some(second));
    }
}
