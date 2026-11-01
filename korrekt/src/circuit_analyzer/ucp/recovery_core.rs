//! A recovery bizonyitekainak szemantikai allapotatmenetei, solver- es riportfuggoseg nelkul.
//! Az eles adapter ezeket hivja; a Charon/Aeneas ugyanezt a kodot nyeri ki.

use super::{
    cell::CellId,
    facts::UcpFacts,
    value::{normalize_field_value, CompleteDomainError, UcpValueDomain, UcpValueFacts},
};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet, HashSet};

// A W halmaz: az eredeti kontextus kielegito ertekadasaibol szarmazo normalizalt mintak.
#[derive(Default)]
pub(crate) struct RecoveryEvidence {
    pub(super) feasible: BTreeMap<CellId, BTreeSet<BigInt>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct UnsupportedSample;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CertificationError {
    UniqueWithSamples(CellId),
    Domain(CellId, CompleteDomainError),
}

impl RecoveryEvidence {
    pub(crate) fn try_remember_sample(
        &mut self,
        cell: &CellId,
        sample: BigInt,
        modulus: &BigInt,
    ) -> Result<(), UnsupportedSample> {
        let value = normalize_field_value(sample, modulus).ok_or(UnsupportedSample)?;
        self.feasible.entry(cell.clone()).or_default().insert(value);
        Ok(())
    }

    fn try_remember_list(
        &mut self,
        cell: &CellId,
        samples: Vec<BigInt>,
        modulus: &BigInt,
    ) -> Result<(), UnsupportedSample> {
        for sample in samples {
            self.try_remember_sample(cell, sample, modulus)?;
        }
        Ok(())
    }

    fn try_remember_model(
        &mut self,
        models: &BTreeMap<CellId, BTreeSet<BigInt>>,
        modulus: &BigInt,
    ) -> Result<(), UnsupportedSample> {
        for (cell, values) in models {
            let samples: Vec<BigInt> = values.iter().map(|value| value.clone()).collect();
            self.try_remember_list(cell, samples, modulus)?;
        }
        Ok(())
    }

    /// Csak a teljessegi jelolest frissitve nem ker uj UCP-kort.
    /// Ha a testbeli azonositas tobb jeloltet egyetlen ertekre von ossze, uj propagaciot ker.
    pub(crate) fn try_certify_complete_domains(
        &self,
        facts: &UcpFacts,
        values: &mut UcpValueFacts,
        modulus: &BigInt,
    ) -> Result<bool, CertificationError> {
        let mut exact_added = false;
        for (cell, samples) in &self.feasible {
            if samples.len() >= 2 && facts.is_unique(cell) {
                return Err(CertificationError::UniqueWithSamples(cell.clone()));
            }
            let was_exact = values.known_value(cell).is_some();
            if let Err(error) = values.try_mark_complete_from_samples(cell, samples, modulus) {
                return Err(CertificationError::Domain(cell.clone(), error));
            }
            if !was_exact && values.known_value(cell).is_some() {
                exact_added = true;
            }
        }
        Ok(exact_added)
    }

    // Ket kulonbozo teljes modellertek domainlefedes nelkul is bizonyitja a nemegyertelmuseget.
    pub(crate) fn record_non_unique_cells(&self, non_unique: &mut HashSet<CellId>) {
        for (cell, samples) in &self.feasible {
            if samples.len() >= 2 {
                non_unique.insert(cell.clone());
            }
        }
    }
}

// Egy keresesi lepes igazolt eredmenye, nyomkoveto adatok nelkul.
pub(crate) struct EstablishedEvidence {
    pub(crate) cell: CellId,
    pub(crate) samples: Vec<BigInt>,
    pub(crate) model_samples: BTreeMap<CellId, BTreeSet<BigInt>>,
    pub(crate) domain: Option<UcpValueDomain>,
    pub(crate) unique: bool,
    pub(crate) non_unique: bool,
}

// Csak igazolt kovetkeztetest olvaszt be. A megvalosithato mintakat kulon W-ben orzi meg;
// onmagaban egy modellertek nem jogosit lefedo domain vagy egyertelmuseg bejegyzesere.
pub(crate) fn merge_established_evidence(
    evidence: &mut RecoveryEvidence,
    facts: &mut UcpFacts,
    values: &mut UcpValueFacts,
    non_unique: &mut HashSet<CellId>,
    established: EstablishedEvidence,
    modulus: &BigInt,
) -> Result<bool, UnsupportedSample> {
    let EstablishedEvidence {
        cell,
        samples,
        model_samples,
        domain,
        unique,
        non_unique: is_non_unique,
    } = established;
    evidence.try_remember_list(&cell, samples, modulus)?;
    evidence.try_remember_model(&model_samples, modulus)?;
    let mut changed = false;
    if unique {
        changed = facts.mark_unique(cell.clone());
    }
    if let Some(domain) = domain {
        if values.mark_domain(cell.clone(), domain) {
            changed = true;
        }
    }
    if is_non_unique {
        non_unique.insert(cell);
    }
    Ok(changed)
}

// A beolvasztas zaro lepese: teljesseget igazol, majd a mintakbol non-unique cimket kepez.
pub(crate) fn finish_merge(
    evidence: &RecoveryEvidence,
    facts: &UcpFacts,
    values: &mut UcpValueFacts,
    non_unique: &mut HashSet<CellId>,
    modulus: &BigInt,
) -> Result<bool, CertificationError> {
    let exact_added = evidence.try_certify_complete_domains(facts, values, modulus)?;
    evidence.record_non_unique_cells(non_unique);
    Ok(exact_added)
}
