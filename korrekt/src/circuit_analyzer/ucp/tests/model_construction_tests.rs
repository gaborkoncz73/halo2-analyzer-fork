//! A modellepito csak javaslatot ad; a kizarasait kimeritoen ellenorzott kis rendszereken veti ossze.
use super::*;
use crate::circuit_analyzer::ucp::expr::{UcpExpr, UcpScalar};
use std::collections::BTreeMap;

const P: i64 = 101;

fn var(cell: &CellId) -> UcpExpr {
    UcpExpr::var(cell.clone())
}

fn constant(value: i64) -> UcpExpr {
    UcpExpr::known_constant_i64(value)
}

fn minus(left: UcpExpr, right: UcpExpr) -> UcpExpr {
    UcpExpr::add(left, UcpExpr::scale_by(right, UcpScalar::known_i64(-1)))
}

fn problem(expressions: Vec<UcpExpr>, domains: &[(CellId, Vec<i64>)]) -> UcpProblem {
    let mut values = UcpValueFacts::new();
    for (cell, entries) in domains {
        values.mark_domain(
            cell.clone(),
            UcpValueDomain::finite_set(entries.iter().map(|v| BigInt::from(*v))).unwrap(),
        );
    }
    UcpProblem {
        expressions,
        expression_domains: Vec::new(),
        lookups: Vec::new(),
        initial_facts: UcpFacts::new(),
        target_cells: Vec::new(),
        output_cells: Vec::new(),
        witness_cells: domains.iter().map(|(cell, _)| cell.clone()).collect(),
        initial_value_facts: values,
        field_modulus: P.into(),
    }
}

fn run(problem: &UcpProblem, cell: &CellId, value: i64) -> ModelConstruction {
    let knowledge = problem.analyze_with_values(UcpFacts::new(), problem.initial_value_facts.clone());
    construct_model(problem, &knowledge, cell, &value.into(), &|_, _| true)
}

// Minden kielegito ertekadast felsorol, az UCP-szabalyoktol fuggetlenul.
fn solutions(cells: &[(CellId, Vec<i64>)], holds: &dyn Fn(&[i64]) -> bool) -> Vec<Vec<i64>> {
    let mut all = vec![Vec::new()];
    for (_, entries) in cells {
        all = all
            .into_iter()
            .flat_map(|prefix: Vec<i64>| {
                entries.iter().map(move |value| {
                    let mut next = prefix.clone();
                    next.push(*value);
                    next
                })
            })
            .collect();
    }
    all.retain(|assignment| holds(assignment));
    all
}

#[test]
fn propagation_builds_a_full_candidate_and_refutes_an_excluded_value() {
    let (x, y) = (CellId::advice(0, 0), CellId::advice(1, 0));
    let domains = [(x.clone(), vec![1, 2, 3]), (y.clone(), vec![5, 6])];
    let problem = problem(
        vec![minus(UcpExpr::add(var(&x), var(&y)), constant(7))],
        &domains,
    );
    let ModelConstruction::Candidate(model) = run(&problem, &x, 1) else {
        panic!("expected a candidate");
    };
    assert_eq!(model.known_value(&y), Some(&BigInt::from(6)));
}

#[test]
fn a_contradicting_candidate_is_refuted_after_propagation() {
    let cells: Vec<_> = (0..3).map(|column| CellId::advice(column, 0)).collect();
    let domains: Vec<_> = cells.iter().map(|cell| (cell.clone(), vec![0, 1])).collect();
    let sum = |left: &CellId, right: &CellId| {
        minus(UcpExpr::add(var(left), var(right)), constant(1))
    };
    let problem = problem(
        vec![
            sum(&cells[0], &cells[1]),
            sum(&cells[1], &cells[2]),
            sum(&cells[0], &cells[2]),
        ],
        &domains,
    );
    assert_eq!(run(&problem, &cells[0], 0), ModelConstruction::Refuted);
}

#[test]
fn decisions_prefer_values_not_seen_yet() {
    let (x, y) = (CellId::advice(0, 0), CellId::advice(1, 0));
    let domains = [(x.clone(), vec![1, 2]), (y.clone(), vec![5, 6])];
    let problem = problem(Vec::new(), &domains);
    let knowledge = problem.analyze_with_values(UcpFacts::new(), problem.initial_value_facts.clone());
    let answer = construct_model(&problem, &knowledge, &x, &1.into(), &|cell, value| {
        !(cell == &y && *value == BigInt::from(5))
    });
    let ModelConstruction::Candidate(model) = answer else {
        panic!("expected a candidate");
    };
    assert_eq!(model.known_value(&y), Some(&BigInt::from(6)));
}

#[test]
fn free_cells_stay_free_for_the_solver() {
    let (x, free) = (CellId::advice(0, 0), CellId::advice(1, 0));
    let domains = [(x.clone(), vec![1, 2])];
    let problem = problem(vec![minus(var(&free), var(&free))], &domains);
    let ModelConstruction::Candidate(model) = run(&problem, &x, 1) else {
        panic!("expected a candidate");
    };
    assert_eq!(model.known_value(&x), Some(&BigInt::from(1)));
    assert_eq!(model.known_value(&free), None);
}

// Refuted csak valoban megoldas nelkuli jeloltre johet, es minden kesz ertekadas kielegito.
#[test]
fn refutations_and_full_candidates_match_exhaustive_search() {
    let cells: Vec<_> = (0..3).map(|column| CellId::advice(column, 0)).collect();
    let domains: Vec<_> = cells
        .iter()
        .zip([vec![0, 1, 2, 3], vec![1, 2, 4], vec![0, 2, 5]])
        .map(|(cell, entries)| (cell.clone(), entries))
        .collect();
    type Holds = fn(&[i64]) -> bool;
    let systems: Vec<(Vec<UcpExpr>, Holds)> = vec![
        (
            vec![minus(
                UcpExpr::mul(var(&cells[0]), var(&cells[1])),
                var(&cells[2]),
            )],
            |v| (v[0] * v[1] - v[2]).rem_euclid(P) == 0,
        ),
        (
            vec![
                minus(UcpExpr::add(var(&cells[0]), var(&cells[1])), constant(3)),
                minus(UcpExpr::mul(var(&cells[1]), var(&cells[2])), constant(4)),
            ],
            |v| (v[0] + v[1] - 3).rem_euclid(P) == 0 && (v[1] * v[2] - 4).rem_euclid(P) == 0,
        ),
        (
            vec![UcpExpr::mul(
                minus(var(&cells[0]), var(&cells[1])),
                minus(var(&cells[1]), var(&cells[2])),
            )],
            |v| ((v[0] - v[1]) * (v[1] - v[2])).rem_euclid(P) == 0,
        ),
    ];
    let mut refuted = 0;
    let mut built = 0;
    for (expressions, holds) in systems {
        let all = solutions(&domains, &holds);
        let problem = problem(expressions, &domains);
        let knowledge =
            problem.analyze_with_values(UcpFacts::new(), problem.initial_value_facts.clone());
        for (index, (cell, _)) in domains.iter().enumerate() {
            let Some(UcpValueDomain::FiniteSet(entries)) = knowledge.value_facts.domain(cell)
            else {
                continue;
            };
            for value in entries.clone() {
                let small = i64::try_from(value.clone()).unwrap();
                let feasible = all.iter().any(|row| row[index] == small);
                match construct_model(&problem, &knowledge, cell, &value, &|_, _| true) {
                    ModelConstruction::Refuted => {
                        assert!(!feasible, "{cell} = {value} refuted but feasible");
                        refuted += 1;
                    }
                    ModelConstruction::Candidate(model) => {
                        let row: BTreeMap<_, _> = domains
                            .iter()
                            .map(|(cell, _)| (cell.clone(), model.known_value(cell).cloned()))
                            .collect();
                        let row: Option<Vec<i64>> = domains
                            .iter()
                            .map(|(cell, _)| {
                                row[cell].clone().map(|v| i64::try_from(v).unwrap())
                            })
                            .collect();
                        let row = row.expect("every finite cell receives a value");
                        assert!(holds(&row), "{row:?} does not satisfy the system");
                        assert_eq!(row[index], small);
                        built += 1;
                    }
                    ModelConstruction::GaveUp => {}
                }
            }
        }
    }
    assert!(built > 0, "no full candidate was built ({refuted} refutations)");
}
