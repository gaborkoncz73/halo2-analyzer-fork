//! Megoldo nelkuli modellepites es jeloltkizaras a meglevo UCP-szabalyokkal.
//!
//! Egy jelolt ertek feltetelezese mellett propagal, a meg nyitott veges domainekben dont,
//! es visszalep, ha a szabalyok ellentmondast talalnak. A kesz ertekadas csak javaslat:
//! megvalosithatosagot kizarolag az eredeti SMT-kodolas SAT-valasza igazol.
//! Kizarast az ad, ha a feltevesbol minden eset ellentmondasra vezet. Ez ugyanarra a
//! szabalyhelyessegre epul, mint a K es Delta, ezert nem igazol tobbet a fixpontnal.

use super::{
    cell::{CellId, CellKind},
    engine::{propagate_hypothesis, UcpResult},
    extractor::UcpProblem,
    facts::UcpFacts,
    value::{UcpValueDomain, UcpValueFacts},
};
use num_bigint::BigInt;

// A keretek a munkat korlatozzak. Tullepeskor nincs allitas, a hivo a solverhez fordul.
const MAX_PROPAGATIONS: usize = 48;
const MAX_BRANCH_VALUES: usize = 16;

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum ModelConstruction {
    /// Az ertekadas pontos reszet adja. A nem kozolt cellakat a solver toltheti ki.
    Candidate(UcpValueFacts),
    /// Minden megvizsgalt eset ellentmondott, tehat a jelolt nem megvalosithato.
    Refuted,
    GaveUp,
}

/// Az `unseen` a meg nem latott ertekeket veszi elore, hogy egy modell tobb cella jeloltjet is igazolja.
pub(crate) fn construct_model(
    problem: &UcpProblem,
    knowledge: &UcpResult,
    cell: &CellId,
    value: &BigInt,
    unseen: &dyn Fn(&CellId, &BigInt) -> bool,
) -> ModelConstruction {
    let _profile = super::profiling::scope("ucp.model_construction");
    let mut values = knowledge.value_facts.for_hypothetical_reasoning();
    if !assume(&mut values, cell, value) {
        return ModelConstruction::GaveUp;
    }
    let mut budget = MAX_PROPAGATIONS;
    search(problem, &knowledge.facts, values, unseen, &mut budget)
}

/// Jelolt feltetelezese nelkul epit ertekadast, a gyorsproba elso modelljehez.
pub(crate) fn construct_unassumed_model(
    problem: &UcpProblem,
    knowledge: &UcpResult,
    unseen: &dyn Fn(&CellId, &BigInt) -> bool,
) -> ModelConstruction {
    let _profile = super::profiling::scope("ucp.model_construction");
    let mut budget = MAX_PROPAGATIONS;
    search(
        problem,
        &knowledge.facts,
        knowledge.value_facts.for_hypothetical_reasoning(),
        unseen,
        &mut budget,
    )
}

// A jelolt a lefedo domainbol szarmazik, ezert sikeres szukites utan pontos ertek marad.
fn assume(values: &mut UcpValueFacts, cell: &CellId, value: &BigInt) -> bool {
    values.mark_known(cell.clone(), value.clone());
    values.known_value(cell) == Some(value)
}

fn search(
    problem: &UcpProblem,
    facts: &UcpFacts,
    values: UcpValueFacts,
    unseen: &dyn Fn(&CellId, &BigInt) -> bool,
    budget: &mut usize,
) -> ModelConstruction {
    if *budget == 0 {
        return ModelConstruction::GaveUp;
    }
    *budget -= 1;
    let (result, conflict) = propagate_hypothesis(problem, facts.clone(), values);
    if conflict {
        return ModelConstruction::Refuted;
    }
    let Some((cell, entries)) = next_decision(problem, &result.value_facts) else {
        return ModelConstruction::Candidate(exact_values(&result.value_facts));
    };
    let (fresh, known): (Vec<_>, Vec<_>) = entries.into_iter().partition(|v| unseen(&cell, v));
    let mut exhausted = true;
    let total = fresh.len() + known.len();
    for value in fresh.into_iter().chain(known).take(MAX_BRANCH_VALUES) {
        let mut branch = result.value_facts.clone();
        if !assume(&mut branch, &cell, &value) {
            exhausted = false;
            continue;
        }
        match search(problem, &result.facts, branch, unseen, budget) {
            model @ ModelConstruction::Candidate(_) => return model,
            ModelConstruction::Refuted => {}
            ModelConstruction::GaveUp => exhausted = false,
        }
    }
    // Esetszetvalasztas csak akkor zar ki, ha a lefedo domain minden erteket megvizsgalta.
    if exhausted && total <= MAX_BRANCH_VALUES {
        ModelConstruction::Refuted
    } else {
        ModelConstruction::GaveUp
    }
}

// A legkisebb nyitott veges domainben dont, igy a legkevesebb esetet nyitja meg.
fn next_decision(problem: &UcpProblem, values: &UcpValueFacts) -> Option<(CellId, Vec<BigInt>)> {
    problem
        .witness_cells
        .iter()
        .filter_map(|cell| match values.domain(cell)? {
            UcpValueDomain::FiniteSet(entries) if entries.len() >= 2 => {
                Some((entries.len(), cell, entries))
            }
            _ => None,
        })
        .min_by(|left, right| left.0.cmp(&right.0).then_with(|| left.1.cmp(right.1)))
        .map(|(_, cell, entries)| (cell.clone(), entries.iter().cloned().collect()))
}

fn exact_values(values: &UcpValueFacts) -> UcpValueFacts {
    let mut exact = UcpValueFacts::new();
    for (cell, value) in values.known_values() {
        if cell.kind == CellKind::Advice {
            exact.mark_known(cell, value);
        }
    }
    exact
}

#[cfg(test)]
#[path = "tests/model_construction_tests.rs"]
mod tests;
