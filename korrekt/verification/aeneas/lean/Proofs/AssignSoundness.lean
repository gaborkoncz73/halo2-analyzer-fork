import Proofs.AssignImplementation

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000

theorem scalar_nonzero_sound {F : Type} [Field F] (p : Nat) [CharP F p]
    (constants : Constants F) (path : List Bool) (scalar : expressions.UcpScalar)
    (detected : scalarNonzero scalar (Option.some (p : Int)) = true) :
    scalarValue constants path scalar ≠ 0 := by
  cases scalar with
  | Zero => simp [scalarNonzero] at detected
  | Unknown => simp [scalarNonzero] at detected
  | NonZero => exact constants.nonzero_valid path
  | Known value =>
      simp only [scalarNonzero] at detected
      split at detected
      · have notDivisible : ¬(p : Int) ∣ value := by
          simpa only [Int.dvd_iff_tmod_eq_zero, decide_eq_true_eq] using detected
        exact fun zero => notDivisible ((CharP.intCast_eq_zero_iff F p value).mp zero)
      · cases detected

theorem scalar_zero_of_rejected {F : Type} [Field F] (p : Nat) [CharP F p]
    (positive : 1 < (p : Int)) (constants : Constants F) (path : List Bool)
    (scalar : expressions.UcpScalar) (notUnknown : scalar ≠ .Unknown)
    (rejected : scalarNonzero scalar (Option.some (p : Int)) = false) :
    scalarValue constants path scalar = 0 := by
  cases scalar <;>
    simp_all [scalarNonzero, scalarValue, CharP.intCast_eq_zero_iff F p,
      Int.dvd_iff_tmod_eq_zero]

-- Ervenyes eredmenynel a jelolt hianya stabil kifejezest, jelenlete visszafordithatosagot jelent.
def Explains {F : Type} (left right : cells.CellId -> F) (analysis : rules.AssignAnalysis)
    (leftValue rightValue : F) : Prop :=
  analysis.valid = true -> match analysis.candidate with
    | Option.none => leftValue = rightValue
    | Option.some cell => leftValue = rightValue -> left cell = right cell

theorem explains_fixed {F : Type} (left right : cells.CellId -> F) {x y : F} (equal : x = y) :
    Explains left right noCandidate x y := by
  intro _
  exact equal

theorem explains_invalid {F : Type} (left right : cells.CellId -> F) (x y : F) :
    Explains left right invalidAnalysis x y := by
  intro impossible
  cases impossible

theorem explains_map {F : Type} (left right : cells.CellId -> F)
    (analysis : rules.AssignAnalysis) (x y : F) (f : F -> F)
    (injective : Function.Injective f) (sound : Explains left right analysis x y) :
    Explains left right analysis (f x) (f y) := by
  intro valid
  specialize sound valid
  cases h : analysis.candidate with
  | none => simpa only [h] using congrArg f (by simpa only [h] using sound : x = y)
  | some cell =>
      simp only [h] at sound ⊢
      exact fun same => sound (injective same)

theorem explains_merge {F : Type} [AddGroup F] (left right : cells.CellId -> F)
    (first second : rules.AssignAnalysis) (a b c d : F)
    (firstSound : Explains left right first a b)
    (secondSound : Explains left right second c d) :
    Explains left right (mergeAnalysis first second) (a + c) (b + d) := by
  cases first with
  | mk firstCandidate firstValid =>
    cases second with
    | mk secondCandidate secondValid =>
      cases firstValid <;> cases secondValid <;> cases firstCandidate <;> cases secondCandidate <;>
        simp_all [Explains, mergeAnalysis, noCandidate, invalidAnalysis, withCandidate]

theorem nonzero_constant_witness (expression : expressions.UcpExpr) (modulus : Option Int)
    (detected : nonzeroConstant expression modulus = true) :
    Exists fun scalar => expression = .Const scalar /\ scalarNonzero scalar modulus = true := by
  cases expression <;> simp_all [nonzeroConstant]

-- A bizonyitas a teljes rekurziv Assign-elemzest kezeli, nem csak az affin mintak peldait.
theorem assign_spec_sound {F : Type} [Field F] (p : Nat) [CharP F p]
    (positive : 1 < (p : Int)) (constants : Constants F) (known : cells.CellId -> Bool)
    (left right : cells.CellId -> F)
    (agree : forall cell, known cell = true -> left cell = right cell)
    (expression : expressions.UcpExpr) (path : List Bool) :
    Explains left right (assignSpec known (Option.some (p : Int)) expression)
      (evaluate constants left expression path) (evaluate constants right expression path) := by
  induction expression generalizing path with
  | Var cell =>
      rw [assignSpec.eq_def]
      dsimp only
      split
      · apply explains_fixed
        exact agree cell (by assumption)
      · intro _ equal
        exact equal
  | Const scalar =>
      simp only [assignSpec, uniqueSpec, ite_true]
      exact explains_fixed left right rfl
  | Neg inner ih =>
      rw [assignSpec.eq_def]
      dsimp only
      split
      · apply explains_fixed
        exact unique_spec_sound constants known left right agree (.Neg inner) path (by assumption)
      · exact explains_map left right _ _ _ Neg.neg neg_injective (ih (false :: path))
  | Add first second ihFirst ihSecond =>
      rw [assignSpec.eq_def]
      dsimp only
      split
      · apply explains_fixed
        exact unique_spec_sound constants known left right agree (.Add first second) path (by assumption)
      · exact explains_merge left right _ _ _ _ _ _ (ihFirst _) (ihSecond _)
  | Scale inner scalar ih =>
      rw [assignSpec.eq_def]
      dsimp only
      by_cases unique : uniqueSpec known (.Scale inner scalar) = true
      · rw [ite_eq_left unique]
        apply explains_fixed
        exact unique_spec_sound constants known left right agree (.Scale inner scalar) path unique
      · rw [ite_eq_right unique]
        by_cases nonzero : scalarNonzero scalar (Option.some (p : Int)) = true
        · rw [ite_eq_left nonzero]
          exact explains_map left right _ _ _
            (fun value => value * scalarValue constants path scalar)
            (mul_left_injective₀ (scalar_nonzero_sound p constants path scalar nonzero)) (ih _)
        · rw [ite_eq_right nonzero]
          cases scalar with
          | Unknown => exact explains_invalid left right _ _
          | NonZero => simp [scalarNonzero] at nonzero
          | Zero => apply explains_fixed; simp [evaluate, scalarValue]
          | Known value =>
              have zero := scalar_zero_of_rejected p positive constants path (.Known value)
                (by simp) (Bool.eq_false_iff.mpr nonzero)
              apply explains_fixed
              simp only [evaluate, zero, mul_zero]
  | Mul first second ihFirst ihSecond =>
      rw [assignSpec.eq_def]
      dsimp only
      split
      · apply explains_fixed
        exact unique_spec_sound constants known left right agree (.Mul first second) path (by assumption)
      · split
        · apply explains_fixed
          exact unique_spec_sound constants known left right agree (.Mul first second) path (by assumption)
        · split
          · obtain ⟨scalar, rfl, nonzero⟩ := nonzero_constant_witness first _ (by assumption)
            exact explains_map left right _ _ _
              (fun value => scalarValue constants (false :: path) scalar * value)
              (mul_right_injective₀ (scalar_nonzero_sound p constants _ scalar nonzero)) (ihSecond _)
          · split
            · obtain ⟨scalar, rfl, nonzero⟩ := nonzero_constant_witness second _ (by assumption)
              exact explains_map left right _ _ _
                (fun value => value * scalarValue constants (true :: path) scalar)
                (mul_left_injective₀ (scalar_nonzero_sound p constants _ scalar nonzero)) (ihFirst _)
            · exact explains_invalid left right _ _

-- A publikus Rust-belepopont altal visszaadott cella minden megoldasban azonos erteku.
theorem rust_assign_sound {F : Type} [Field F] (p : Nat) [CharP F p]
    (positive : 1 < (p : Int)) (constants : Constants F)
    (context : (cells.CellId -> F) -> Prop) (facts : knowledge.UcpFacts)
    (knownSound : forall cell, facts.unique_cells cell = true ->
      forall left right, context left -> context right -> left cell = right cell)
    (expression : expressions.UcpExpr) (cell : cells.CellId)
    (equation : forall assignment, context assignment -> evaluate constants assignment expression [] = 0)
    (returned : rules.infer_assigned_cell_from_zero_equation_with_modulus expression facts
      (p : Int) = .ok (Option.some cell)) :
    forall left right, context left -> context right -> left cell = right cell := by
  simp only [rules.infer_assigned_cell_from_zero_equation_with_modulus,
    num_bigint.bigint.BigInt.Insts.CoreConvertFromI32.from,
    core.cmp.impls.PartialOrdShared.le, core.cmp.PartialOrd.le.default,
    core.cmp.PartialOrd.le_body,
    num_bigint.bigint.BigInt.Insts.CoreCmpPartialOrdBigInt.partial_cmp] at returned
  simp [Int.compare_eq_ite_lt, positive, not_lt_of_ge (le_of_lt positive),
    rules.infer_assigned_cell_with_optional_modulus, assign_matches_spec] at returned
  split at returned
  next valid =>
    have candidate : (assignSpec facts.unique_cells (Option.some (p : Int)) expression).candidate =
        Option.some cell := by simpa using returned
    intro left right leftValid rightValid
    have sound := assign_spec_sound p positive constants facts.unique_cells left right
      (fun id known => knownSound id known left right leftValid rightValid) expression []
    simp only [Explains, candidate] at sound
    exact sound valid ((equation left leftValid).trans (equation right rightValid).symm)
  next invalid => simp at returned

end SourceProof
