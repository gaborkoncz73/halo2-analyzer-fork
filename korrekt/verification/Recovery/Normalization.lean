import Recovery.FiniteDomains

/-!
A value.rs normalizalasanak egeszszam-szemantikai modelljet bizonyitja.
A Rust/BigInt elojeles maradekat Int.tmod modellezi, nem a Lean % muvelete.
A BigInt muveletek es az Int kozotti programfinomitas ettol meg nem bizonyitott.
-/

namespace Recovery

def repairRemainder (value modulus : Int) : Int :=
  let remainder := value.tmod modulus
  if remainder < 0 then remainder + modulus else remainder

def centerResidue (residue modulus : Int) : Int :=
  if residue > modulus / 2 then residue - modulus else residue

def normalizeRepresentative (value modulus : Int) : Int :=
  centerResidue (repairRemainder value modulus) modulus

-- A bits <= limit matematikai megfeleloje; a BigInt.bits implementaciojat nem modellezi.
abbrev FitsBits (limit : Nat) (value : Int) : Prop := value.natAbs < 2 ^ limit

def normalizeField (limit : Nat) (value modulus : Int) : Option Int :=
  if modulus <= 1 then none else
    if FitsBits limit modulus then
      let result := normalizeRepresentative value modulus
      if FitsBits limit result then some result else none
    else none

theorem repaired_remainder_eq_emod {value modulus : Int} (positive : 0 < modulus) :
    repairRemainder value modulus = value % modulus := by
  have nonnegative := Int.emod_nonneg value (by omega : Not (modulus = 0))
  have below := Int.emod_lt_of_pos value positive
  unfold repairRemainder
  rw [Int.tmod_eq_emod]
  by_cases regular : 0 <= value \/ modulus ∣ value
  · simp only [ite_eq_left regular, Int.natCast_zero, Int.sub_zero]
    split <;> omega
  · simp only [ite_eq_right regular, Int.natAbs_of_nonneg (by omega : 0 <= modulus)]
    split <;> omega

theorem normalize_representative_eq_center {value modulus : Int} (positive : 0 < modulus) :
    normalizeRepresentative value modulus = centerResidue (value % modulus) modulus := by
  unfold normalizeRepresentative
  rw [repaired_remainder_eq_emod positive]

theorem normalization_preserves_residue {value modulus : Int} (positive : 0 < modulus) :
    normalizeRepresentative value modulus % modulus = value % modulus := by
  rw [normalize_representative_eq_center positive]
  unfold centerResidue
  split
  · simp
  · simp

theorem normalization_same_residue {left right modulus : Int} (positive : 0 < modulus)
    (same : left % modulus = right % modulus) :
    normalizeRepresentative left modulus = normalizeRepresentative right modulus := by
  rw [normalize_representative_eq_center positive, normalize_representative_eq_center positive, same]

theorem normalization_eq_iff_same_residue {left right modulus : Int} (positive : 0 < modulus) :
    normalizeRepresentative left modulus = normalizeRepresentative right modulus <->
      left % modulus = right % modulus := by
  constructor
  · intro same
    have residues := congrArg (fun value => value % modulus) same
    simpa only [normalization_preserves_residue positive] using residues
  · exact normalization_same_residue positive

theorem normalization_idempotent {value modulus : Int} (positive : 0 < modulus) :
    normalizeRepresentative (normalizeRepresentative value modulus) modulus =
      normalizeRepresentative value modulus := by
  exact normalization_same_residue positive (normalization_preserves_residue positive)

theorem normalization_zero {modulus : Int} (positive : 0 < modulus) :
    normalizeRepresentative 0 modulus = 0 := by
  have halfNonnegative : 0 <= modulus / 2 := Int.ediv_nonneg (by omega) (by decide)
  rw [normalize_representative_eq_center positive]
  simp [centerResidue, show Not ((0 : Int) > modulus / 2) by omega]

theorem normalization_zero_iff {value modulus : Int} (positive : 0 < modulus) :
    normalizeRepresentative value modulus = 0 <-> value % modulus = 0 := by
  have equivalence := normalization_eq_iff_same_residue (left := value) (right := 0) positive
  simpa only [normalization_zero positive, Int.zero_emod] using equivalence

-- A normalizalt mintak kulonbozosege pontosan a maradekosztalyok kulonbozoseget jelenti.
theorem normalization_distinct_iff {left right modulus : Int} (positive : 0 < modulus) :
    Not (normalizeRepresentative left modulus = normalizeRepresentative right modulus) <->
      Not (left % modulus = right % modulus) := by
  exact not_congr (normalization_eq_iff_same_residue positive)

theorem normalization_range {value modulus : Int} (positive : 0 < modulus) :
    -(modulus / 2) <= normalizeRepresentative value modulus /\
      normalizeRepresentative value modulus <= modulus / 2 := by
  have nonnegative := Int.emod_nonneg value (by omega : Not (modulus = 0))
  have below := Int.emod_lt_of_pos value positive
  rw [normalize_representative_eq_center positive]
  unfold centerResidue
  split <;> omega

theorem normalization_preserves_bit_bound {value modulus : Int} {limit : Nat}
    (positive : 0 < modulus) (fits : FitsBits limit modulus) :
    FitsBits limit (normalizeRepresentative value modulus) := by
  have range := normalization_range (value := value) positive
  have magnitude : (normalizeRepresentative value modulus).natAbs <= modulus.natAbs := by
    apply Int.ofNat_le.mp
    rw [Int.natAbs_of_nonneg (by omega : 0 <= modulus)]
    by_cases sign : 0 <= normalizeRepresentative value modulus
    · rw [Int.natAbs_of_nonneg sign]
      omega
    · rw [Int.ofNat_natAbs_of_nonpos (by omega)]
      omega
  exact Nat.lt_of_le_of_lt magnitude fits

theorem valid_modulus_normalizes {value modulus : Int} {limit : Nat}
    (valid : 1 < modulus) (fits : FitsBits limit modulus) :
    normalizeField limit value modulus = some (normalizeRepresentative value modulus) := by
  simp [normalizeField, show Not (modulus <= 1) by omega, fits,
    normalization_preserves_bit_bound (by omega : 0 < modulus) fits]

theorem invalid_modulus_rejected {value modulus : Int} {limit : Nat} (invalid : modulus <= 1) :
    normalizeField limit value modulus = none := by
  simp [normalizeField, invalid]

theorem oversized_modulus_rejected {value modulus : Int} {limit : Nat}
    (oversized : Not (FitsBits limit modulus)) : normalizeField limit value modulus = none := by
  simp [normalizeField, oversized]

theorem normalize_field_success {value modulus result : Int} {limit : Nat}
    (success : normalizeField limit value modulus = some result) :
    1 < modulus /\ FitsBits limit modulus /\ FitsBits limit result /\
      result = normalizeRepresentative value modulus := by
  unfold normalizeField at success
  split at success
  · cases success
  · rename_i valid
    split at success
    · rename_i fits
      dsimp only at success
      split at success
      · rename_i resultFits
        have same := (Option.some.inj success).symm
        subst result
        exact ⟨by omega, fits, resultFits, rfl⟩
      · cases success
    · cases success

theorem normalized_addition_preserves_residue {left right modulus : Int} (positive : 0 < modulus) :
    (normalizeRepresentative left modulus + normalizeRepresentative right modulus) % modulus =
      (left + right) % modulus := by
  rw [Int.add_emod, normalization_preserves_residue positive,
    normalization_preserves_residue positive, <- Int.add_emod]

theorem normalized_multiplication_preserves_residue {left right modulus : Int} (positive : 0 < modulus) :
    (normalizeRepresentative left modulus * normalizeRepresentative right modulus) % modulus =
      (left * right) % modulus := by
  rw [Int.mul_emod, normalization_preserves_residue positive,
    normalization_preserves_residue positive, <- Int.mul_emod]

end Recovery
