#![allow(dead_code, unused_imports)]

// A kinyeres az eles forrasfajlokat hasznalja, nem azok masolatat.
#[path = "../../../src/circuit_analyzer/ucp/cell.rs"]
pub mod cells;
pub use cells as cell;
#[path = "../../../src/circuit_analyzer/ucp/expr.rs"]
pub mod expressions;
pub use expressions as expr;
#[path = "../../../src/circuit_analyzer/ucp/facts.rs"]
pub mod knowledge;
pub use knowledge as facts;
#[path = "../../../src/circuit_analyzer/ucp/rules.rs"]
pub mod rules;
#[path = "../../../src/circuit_analyzer/ucp/recovery_loop.rs"]
pub mod recovery_loop;
#[path = "../../../src/circuit_analyzer/ucp/profiling.rs"]
pub mod profiling;

// A domainmodul tesztjei a teljes analyzer engine-jet igenylik; azok az eles crate-ben futnak.
// A kinyeres valtozatlanul az eles modult hasznalja, helyettesito fuggvenytorzs nelkul.
#[cfg(not(test))]
#[path = "../../../src/circuit_analyzer/ucp/value.rs"]
pub mod domains;
#[cfg(not(test))]
pub use domains as value;

// A Charon belepopontjai a valodi metodusokat hivjak; nem helyettesitik azok torzset.
pub fn mark_unique(facts: &mut knowledge::UcpFacts, cell: cells::CellId) -> bool {
    facts.mark_unique(cell)
}

pub fn mark_initial_unique(facts: &mut knowledge::UcpFacts, cell: cells::CellId) -> bool {
    facts.mark_initial_unique(cell)
}

#[cfg(not(test))]
pub mod domain_entrypoints {
    use super::{cells::CellId, domains::UcpValueFacts};
    use num_bigint::BigInt;

    pub fn complete(values: &UcpValueFacts, cell: &CellId) -> bool {
        values.domain_is_complete(cell)
    }

    pub fn known<'a>(values: &'a UcpValueFacts, cell: &CellId) -> Option<&'a BigInt> {
        values.known_value(cell)
    }

    pub fn hypothetical(values: &UcpValueFacts) -> UcpValueFacts {
        values.for_hypothetical_reasoning()
    }

    pub fn bounded(value: BigInt) -> Option<BigInt> {
        super::domains::bounded_value(value)
    }

    pub fn normalize(value: BigInt, modulus: &BigInt) -> Option<BigInt> {
        super::domains::normalize_field_value(value, modulus)
    }

    pub(crate) fn certify(
        values: &mut UcpValueFacts,
        cell: &CellId,
        samples: &std::collections::BTreeSet<BigInt>,
        modulus: &BigInt,
    ) -> Result<bool, super::domains::CompleteDomainError> {
        values.try_mark_complete_from_samples(cell, samples, modulus)
    }

    pub fn merge(
        values: &mut UcpValueFacts,
        cell: CellId,
        domain: super::domains::UcpValueDomain,
    ) -> bool {
        values.mark_domain(cell, domain)
    }
}

pub mod circuit_analyzer {
    pub mod ucp {
        pub use crate::{cell, profiling};
    }
}
