import Proofs.DomainMerge
import Mathlib.Data.Nat.Size

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000

def repairedRemainder (value modulus : Int) : Int :=
  let remainder := value.tmod modulus
  if remainder < 0 then remainder + modulus else remainder

def centeredRepresentative (value modulus : Int) : Int :=
  let remainder := value % modulus
  if remainder > modulus / 2 then remainder - modulus else remainder

theorem repaired_remainder_is_emod {value modulus : Int} (positive : 0 < modulus) :
    repairedRemainder value modulus = value % modulus := by
  have nonnegative := Int.emod_nonneg value (by omega : modulus ≠ 0)
  have below := Int.emod_lt_of_pos value positive
  unfold repairedRemainder
  rw [Int.tmod_eq_emod]
  by_cases regular : 0 ≤ value ∨ modulus ∣ value
  · simp only [ite_eq_left regular, Int.natCast_zero, Int.sub_zero]
    split <;> omega
  · simp only [ite_eq_right regular, Int.natAbs_of_nonneg (by omega : 0 ≤ modulus)]
    split <;> omega

theorem centered_preserves_residue {value modulus : Int} (_positive : 0 < modulus) :
    centeredRepresentative value modulus % modulus = value % modulus := by
  unfold centeredRepresentative
  dsimp only
  split <;> simp

theorem centered_eq_iff_same_residue {left right modulus : Int} (positive : 0 < modulus) :
    centeredRepresentative left modulus = centeredRepresentative right modulus ↔
      left % modulus = right % modulus := by
  constructor
  · intro same
    have residues := congrArg (fun value => value % modulus) same
    simpa only [centered_preserves_residue positive] using residues
  · intro same
    simp only [centeredRepresentative, same]

theorem centered_idempotent {value modulus : Int} (positive : 0 < modulus) :
    centeredRepresentative (centeredRepresentative value modulus) modulus =
      centeredRepresentative value modulus :=
  (centered_eq_iff_same_residue positive).mpr (centered_preserves_residue positive)

theorem centered_range {value modulus : Int} (positive : 0 < modulus) :
    -(modulus / 2) ≤ centeredRepresentative value modulus ∧
      centeredRepresentative value modulus ≤ modulus / 2 := by
  have nonnegative := Int.emod_nonneg value (by omega : modulus ≠ 0)
  have below := Int.emod_lt_of_pos value positive
  unfold centeredRepresentative
  dsimp only
  split <;> omega

theorem centered_magnitude {value modulus : Int} (positive : 0 < modulus) :
    (centeredRepresentative value modulus).natAbs ≤ modulus.natAbs := by
  have range := centered_range (value := value) positive
  apply Int.ofNat_le.mp
  rw [Int.natAbs_of_nonneg (by omega : 0 ≤ modulus)]
  by_cases sign : 0 ≤ centeredRepresentative value modulus
  · rw [Int.natAbs_of_nonneg sign]
    omega
  · rw [Int.ofNat_natAbs_of_nonpos (by omega)]
    omega

-- A maradek es az osztas a Rust elojeles egeszmuveleteit hasznalja.
-- Az eredmenyt csak a kinyert kod es a matematikai reprezentans egyezese utan ertelmezi.
theorem bigint_le_model (left right : Int) :
    core.cmp.impls.PartialOrdShared.le
      num_bigint.bigint.BigInt.Insts.CoreCmpPartialOrdBigInt left right = .ok (decide (left ≤ right)) := by
  simp [core.cmp.impls.PartialOrdShared.le, core.cmp.PartialOrd.le.default,
    core.cmp.PartialOrd.le_body, num_bigint.bigint.BigInt.Insts.CoreCmpPartialOrdBigInt.partial_cmp,
    Int.compare_eq_lt, le_iff_lt_or_eq]

theorem bigint_lt_model (left right : Int) :
    core.cmp.PartialOrd.lt.trait_default
      num_bigint.bigint.BigInt.Insts.CoreCmpPartialOrdBigInt left right = .ok (decide (left < right)) := by
  simp [core.cmp.PartialOrd.lt.trait_default, core.cmp.PartialOrd.lt.default,
    core.cmp.PartialOrd.lt_body, num_bigint.bigint.BigInt.Insts.CoreCmpPartialOrdBigInt.partial_cmp,
    Int.compare_eq_lt]

theorem bigint_gt_model (left right : Int) :
    core.cmp.PartialOrd.gt.trait_default
      num_bigint.bigint.BigInt.Insts.CoreCmpPartialOrdBigInt left right = .ok (decide (right < left)) := by
  simp [core.cmp.PartialOrd.gt.trait_default, core.cmp.PartialOrd.gt.default,
    core.cmp.PartialOrd.gt_body, num_bigint.bigint.BigInt.Insts.CoreCmpPartialOrdBigInt.partial_cmp,
    Int.compare_eq_gt]

theorem rust_normalization_body_matches (value modulus : Int) (valid : 1 < modulus)
    (fits : modulus.natAbs.size ≤ 4096) :
    domains.normalize_field_value value modulus = domains.bounded_value (centeredRepresentative value modulus) := by
  have positive : 0 < modulus := by omega
  have nonzero : modulus ≠ 0 := by omega
  have representable : modulus.natAbs.size < 2^64 := by omega
  have divTwo := Int.tdiv_eq_ediv_of_nonneg (b := 2) (by omega : 0 ≤ modulus)
  have modulusBits : num_bigint.bigint.BigInt.impl.bits modulus =
      .ok (U64.ofNatCore modulus.natAbs.size representable) := by
    simp only [num_bigint.bigint.BigInt.impl.bits, dite_eq_left representable]
  simp only [domains.normalize_field_value,
    num_bigint.bigint.BigInt.Insts.CoreConvertFromI32.from, bind_ok,
    bigint_le_model, bigint_lt_model, bigint_gt_model, decide_eq_true_eq]
  simp only [modulusBits, bind_ok,
    UScalar.lt_equiv, UScalar.ofNatCore_val_eq, domains.MAX_VALUE_BITS]
  simp [show ¬ modulus ≤ 1 by omega, show ¬ 4096 < modulus.natAbs.size by omega]
  simp only [
    num_bigint.bigint.BigInt.Insts.CoreOpsArithRemShared0BigIntBigInt.rem, nonzero,
    num_bigint.bigint.BigInt.Insts.CoreOpsArithAddAssignShared0BigInt.add_assign,
    num_bigint.bigint.BigInt.Insts.CoreOpsArithSubAssignShared0BigInt.sub_assign,
    Shared0BigInt.Insts.CoreOpsArithDivBigIntBigInt.div, divTwo, OfNat.ofNat_ne_zero]
  have repair := repaired_remainder_is_emod (value := value) positive
  dsimp only [repairedRemainder] at repair
  unfold centeredRepresentative
  by_cases negative : value.tmod modulus < 0
  all_goals simp only [negative, ite_true, ite_false, bind_ok] at repair ⊢
  all_goals rw [repair]
  all_goals split_ifs <;> simp_all

theorem rust_normalization_succeeds (value modulus : Int) (valid : 1 < modulus)
    (fits : modulus.natAbs.size ≤ 4096) :
    domains.normalize_field_value value modulus = .ok (some (centeredRepresentative value modulus)) := by
  rw [rust_normalization_body_matches value modulus valid fits]
  apply rust_bounded_value_accepts_supported
  exact (Nat.size_le_size (centered_magnitude (by omega : 0 < modulus))).trans fits

theorem rust_normalization_preserves_residue (value modulus : Int) (valid : 1 < modulus)
    (fits : modulus.natAbs.size ≤ 4096) (result : Int)
    (returned : domains.normalize_field_value value modulus = .ok (some result)) :
    result % modulus = value % modulus := by
  rw [rust_normalization_succeeds value modulus valid fits] at returned
  have same := Option.some.inj (Result.ok_injective returned)
  rw [← same]
  exact centered_preserves_residue (by omega)

theorem rust_normalization_identifies_aliases (left right modulus : Int) (valid : 1 < modulus)
    (fits : modulus.natAbs.size ≤ 4096) :
    domains.normalize_field_value left modulus = domains.normalize_field_value right modulus ↔
      left % modulus = right % modulus := by
  rw [rust_normalization_succeeds left modulus valid fits,
    rust_normalization_succeeds right modulus valid fits]
  simp only [Result.ok.injEq, Option.some.injEq]
  exact centered_eq_iff_same_residue (by omega)

theorem rust_normalization_is_idempotent (value modulus : Int) (valid : 1 < modulus)
    (fits : modulus.natAbs.size ≤ 4096) (result : Int)
    (returned : domains.normalize_field_value value modulus = .ok (some result)) :
    domains.normalize_field_value result modulus = .ok (some result) := by
  rw [rust_normalization_succeeds value modulus valid fits] at returned
  have same := Option.some.inj (Result.ok_injective returned)
  rw [← same, rust_normalization_succeeds _ modulus valid fits, centered_idempotent (by omega)]

theorem rust_normalization_rejects_invalid_modulus (value modulus : Int) (invalid : modulus ≤ 1) :
    domains.normalize_field_value value modulus = .ok none := by
  simp only [domains.normalize_field_value,
    num_bigint.bigint.BigInt.Insts.CoreConvertFromI32.from, bind_ok, bigint_le_model, decide_eq_true_eq]
  simp [invalid]

theorem rust_normalization_rejects_oversized_modulus (value modulus : Int) (valid : 1 < modulus)
    (representable : modulus.natAbs.size < 2^64) (oversized : 4096 < modulus.natAbs.size) :
    domains.normalize_field_value value modulus = .ok none := by
  have modulusBits : num_bigint.bigint.BigInt.impl.bits modulus =
      .ok (U64.ofNatCore modulus.natAbs.size representable) := by
    simp only [num_bigint.bigint.BigInt.impl.bits, dite_eq_left representable]
  simp only [domains.normalize_field_value,
    num_bigint.bigint.BigInt.Insts.CoreConvertFromI32.from, bind_ok, bigint_le_model, decide_eq_true_eq]
  simp [
    show ¬ modulus ≤ 1 by omega, modulusBits, domains.MAX_VALUE_BITS,
    UScalar.lt_equiv, oversized]

end SourceProof
