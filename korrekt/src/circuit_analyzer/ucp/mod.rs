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
pub mod rules;
pub mod value;

#[cfg(test)]
mod demo_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod pipeline_comparison_tests;

#[cfg(all(test, feature = "use_zcash_halo2_proofs"))]
mod sample_circuit_demo_tests;
