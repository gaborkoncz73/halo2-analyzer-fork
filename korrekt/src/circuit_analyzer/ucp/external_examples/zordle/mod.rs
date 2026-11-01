//! A Zordle (ZK Wordle) kapcsolas vizsgalata; az eredetet es az eltereseket a README rogziti.

mod compat {
    // Csak a rogzitett forkbol hianyzo regi FieldExt nevet potolja, uj kenyszert nem ad hozza.
    pub use zcash_halo2_proofs::{circuit, dev, pasta, plonk, poly};

    pub mod arithmetic {
        pub trait FieldExt: ff::PrimeField + From<u64> {
            fn zero() -> Self {
                Self::ZERO
            }
            fn one() -> Self {
                Self::ONE
            }
        }

        impl<F: ff::PrimeField + From<u64>> FieldExt for F {}
    }
}

#[allow(
    dead_code,
    unused_imports,
    unused_variables,
    unused_mut,
    unexpected_cfgs
)]
mod wordle;

mod tests;
