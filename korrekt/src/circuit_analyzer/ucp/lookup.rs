//! A véges rendezett n-esek tagsági feltételeivel megőrzi az oszlopok közötti korrelációkat.

use super::{
    base_conv::{infer_table_digits, BaseEquations},
    cell::CellId,
    expr::UcpExpr,
    value::{
        expression_domain_with_modulus, infer_domains_from_expression_domain_with_modulus,
        normalize_field_value, UcpValueDomain, UcpValueFacts, MAX_FINITE_DOMAIN_SIZE,
    },
};
use num_bigint::BigInt;
use std::{collections::BTreeSet, sync::Arc};

pub(crate) const MAX_LOOKUP_ARITY: usize = 16;
// A nagy egyoszlopos tablat csak helyierteki felbontason keresztul szuri, soha nem tarolja domainkent.
pub(crate) const MAX_LARGE_TABLE_ROWS: usize = 1 << 20;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UcpLookup {
    inputs: Vec<UcpExpr>,
    tuples: Vec<Vec<BigInt>>,
    large_column: Option<Arc<Vec<BigInt>>>,
}

impl UcpLookup {
    /// A túl nagy vagy hiányos táblát egészében elutasítja; csonkított relációt nem tart meg.
    pub fn new(inputs: Vec<UcpExpr>, tuples: Vec<Vec<BigInt>>) -> Option<Self> {
        if inputs.is_empty()
            || inputs.len() > MAX_LOOKUP_ARITY
            || tuples.iter().any(|tuple| tuple.len() != inputs.len())
        {
            return None;
        }
        let tuples: BTreeSet<_> = tuples.into_iter().collect();
        if tuples.is_empty() || tuples.len() > MAX_FINITE_DOMAIN_SIZE {
            return None;
        }
        Some(Self {
            inputs,
            tuples: tuples.into_iter().collect(),
            large_column: None,
        })
    }

    /// A domainkorlatnal nagyobb egyoszlopos tablat kozos, valtoztathatatlan listakent tartja meg.
    pub(crate) fn large(input: UcpExpr, column: Arc<Vec<BigInt>>) -> Self {
        Self {
            inputs: vec![input],
            tuples: Vec::new(),
            large_column: Some(column),
        }
    }

    pub(crate) fn is_large(&self) -> bool {
        self.large_column.is_some()
    }

    // A tabla ertekeit szamjegyekre bontja, es a tobbi cella domainje alapjan szuri a sorokat.
    pub(crate) fn infer_large(
        &self,
        equations: &BaseEquations,
        values: &UcpValueFacts,
        modulus: &BigInt,
    ) -> Vec<(CellId, UcpValueDomain)> {
        match &self.large_column {
            Some(column) => infer_table_digits(&self.inputs[0], column, equations, values, modulus),
            None => Vec::new(),
        }
    }

    pub fn inputs(&self) -> &[UcpExpr] {
        &self.inputs
    }

    // A teljes sorokat szűri a jelenlegi bemeneti domainekkel; ismeretlen domainnel nem zár ki sort.
    fn supported_rows(&self, values: &UcpValueFacts, modulus: &BigInt) -> Option<Vec<Vec<BigInt>>> {
        if self.is_large() {
            return None;
        }
        let domains: Vec<_> = self
            .inputs
            .iter()
            .map(|expr| {
                expression_domain_with_modulus(expr, values, modulus).map(|domain| entries(&domain))
            })
            .collect();
        let mut rows = Vec::new();
        for tuple in &self.tuples {
            let normalized: Vec<_> = tuple
                .iter()
                .map(|v| normalize_field_value(v.clone(), modulus))
                .collect::<Option<_>>()?;
            if normalized
                .iter()
                .zip(&domains)
                .all(|(value, domain)| domain.as_ref().is_none_or(|domain| domain.contains(value)))
            {
                rows.push(normalized);
            }
        }
        Some(rows)
    }

    pub(crate) fn inconsistent(&self, values: &UcpValueFacts, modulus: &BigInt) -> bool {
        self.supported_rows(values, modulus)
            .is_some_and(|rows| rows.is_empty())
    }

    pub(crate) fn infer(
        &self,
        values: &UcpValueFacts,
        modulus: &BigInt,
    ) -> Vec<(CellId, UcpValueDomain)> {
        let Some(rows) = self.supported_rows(values, modulus) else {
            return Vec::new();
        };
        if rows.is_empty() {
            return Vec::new();
        }
        // A megmaradt sorokat oszloponként vetíti vissza; a vetületből nem állapít meg teljességet.
        let mut inferences = Vec::new();
        for (index, expr) in self.inputs.iter().enumerate() {
            let Some(domain) =
                UcpValueDomain::finite_set(rows.iter().map(|row| row[index].clone()))
            else {
                continue;
            };
            inferences.extend(infer_domains_from_expression_domain_with_modulus(
                expr, &domain, values, modulus,
            ));
        }
        inferences
    }
}

pub(crate) fn entries(domain: &UcpValueDomain) -> BTreeSet<BigInt> {
    match domain {
        UcpValueDomain::Exact(value) => [value.clone()].into(),
        UcpValueDomain::FiniteSet(values) => values.clone(),
    }
}

// Csak sikeres testbeli normalizálás után állapít meg diszjunkt domaineket.
pub(crate) fn disjoint(left: &UcpValueDomain, right: &UcpValueDomain, modulus: &BigInt) -> bool {
    let normalize = |domain: &UcpValueDomain| {
        entries(domain)
            .into_iter()
            .map(|value| normalize_field_value(value, modulus))
            .collect::<Option<BTreeSet<_>>>()
    };
    match (normalize(left), normalize(right)) {
        (Some(left), Some(right)) => left.is_disjoint(&right),
        _ => false,
    }
}
