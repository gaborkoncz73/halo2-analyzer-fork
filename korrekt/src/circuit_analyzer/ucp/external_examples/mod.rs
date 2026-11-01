//! Valtozatlan logikaju kulso Halo2-kapcsolatok vizsgalata a privat visszaallitassal.
//! A modul kizarolag tesztforditaskor kapcsolodik az elemzohoz.

#[cfg(feature = "use_zcash_halo2_proofs")]
mod zordle;

#[cfg(feature = "use_pse_halo2_proofs")]
mod summa;
