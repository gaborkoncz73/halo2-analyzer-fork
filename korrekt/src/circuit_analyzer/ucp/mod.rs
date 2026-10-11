pub mod all_but_one;
pub mod base_conv;
pub mod bigint_mul;
pub mod cell;
pub mod choose_var;
pub mod engine;
pub mod expr;
pub mod extractor;
pub mod facts;
pub mod pipeline;
pub mod plonkish;
pub mod privacy;
pub mod privacy_discovery;
pub mod privacy_domain;
pub mod privacy_observation;
pub(crate) mod privacy_subset;
pub mod privacy_validation;
pub mod rules;
pub mod value;

#[cfg(test)]
mod demo_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod pipeline_comparison_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod sample_circuit_demo_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod privacy_measurement_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod privacy_profile_measurement_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod privacy_domain_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod privacy_discovery_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod privacy_observation_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod external_circuit_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod external_range_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod soundness_regression_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod wide_value_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod external_poseidon_tests;
