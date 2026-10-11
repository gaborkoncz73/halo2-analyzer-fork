use anyhow::{ensure, Result};
use num_bigint::BigInt;
use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VerificationMethod {
    Specific,
    Random,
    None,
}

#[derive(Debug, Clone)]
pub struct VerificationInput {
    pub instance_cells: HashMap<String, BigInt>,
    pub iterations: u128,
}

impl VerificationInput {
    /// Accepts small integers or full-width BigInt observations without truncation.
    pub fn new<I, V>(instance_cells: I, iterations: u128) -> Self
    where
        I: IntoIterator<Item = (String, V)>,
        V: Into<BigInt>,
    {
        Self {
            instance_cells: instance_cells
                .into_iter()
                .map(|(name, value)| (name, value.into()))
                .collect(),
            iterations,
        }
    }

    /// Reject oversized raw inputs before field reduction or solver construction.
    pub(crate) fn validate_public_values(&self) -> Result<()> {
        for (name, value) in &self.instance_cells {
            ensure!(
                value.bits() <= crate::circuit_analyzer::ucp::value::MAX_VALUE_BITS,
                "Public observation for {} exceeds the {}-bit input limit",
                name,
                crate::circuit_analyzer::ucp::value::MAX_VALUE_BITS
            );
        }
        Ok(())
    }
}
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LookupMethod {
    Uninterpreted,
    Interpreted,
    InlineConstraints,
    None,
}
#[derive(Debug, Clone)]
pub struct AnalyzerInput {
    pub verification_method: VerificationMethod,
    pub verification_input: VerificationInput,
    pub lookup_method: LookupMethod,
}

#[derive(Debug, PartialEq, Eq)]
pub enum AnalyzerOutputStatus {
    Invalid,
    Underconstrained,
    Overconstrained,
    NotUnderconstrained,
    NotUnderconstrainedLocal,
    NotUnderconstrainedLocalUninterpretedLookups,
    UnusedCustomGates,
    NoUnusedCustomGates,
    UnconstrainedCells,
    NoUnconstrainedCells,
    UnusedColumns,
    NoUnusedColumns,
}

#[derive(Debug)]
pub struct AnalyzerOutput {
    pub output_status: AnalyzerOutputStatus,
}

#[derive(Debug, Clone)]
pub enum AnalyzerType {
    UnusedGates,
    UnconstrainedCells,
    UnusedColumns,
    UnderconstrainedCircuit,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constructor_accepts_existing_i64_maps_without_narrowing() {
        let input = VerificationInput::new(HashMap::from([("I-0-0".into(), i64::MIN)]), 3);
        assert_eq!(input.instance_cells["I-0-0"], BigInt::from(i64::MIN));
        assert_eq!(input.iterations, 3);
        input.validate_public_values().unwrap();
    }

    #[test]
    fn full_width_decimal_observations_roundtrip_without_truncation() {
        let value = -(BigInt::from(1) << 253usize);
        let parsed: BigInt = value.to_string().parse().unwrap();
        let input = VerificationInput::new([("I-0-0".into(), parsed)], 1);
        assert_eq!(input.instance_cells["I-0-0"], value);
        input.validate_public_values().unwrap();
    }

    #[test]
    fn raw_observation_bit_limit_includes_the_boundary_for_both_signs() {
        let bits = crate::circuit_analyzer::ucp::value::MAX_VALUE_BITS as usize;
        let largest = (BigInt::from(1) << bits) - BigInt::from(1);
        for value in [largest.clone(), -&largest] {
            VerificationInput::new([("I-0-0".into(), value)], 1)
                .validate_public_values()
                .unwrap();
        }
        for value in [&largest + 1, -(&largest + BigInt::from(1))] {
            assert!(VerificationInput::new([("I-0-0".into(), value)], 1)
                .validate_public_values()
                .is_err());
        }
    }
}
