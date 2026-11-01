import Proofs.AssignSoundness
import Proofs.RecoveryKnowledge

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

noncomputable def insertedFacts (facts : knowledge.UcpFacts) (cell : cells.CellId) : knowledge.UcpFacts := by
  classical
  exact ⟨fun key => if key = cell then true else facts.unique_cells key⟩

theorem rust_mark_unique_matches_insert (facts : knowledge.UcpFacts) (cell : cells.CellId) :
    knowledge.UcpFacts.impl.mark_unique facts cell =
      .ok (!facts.unique_cells cell, insertedFacts facts cell) := by
  simp [knowledge.UcpFacts.impl.mark_unique, std.collections.hash.set.HashSet.impl.insert, insertedFacts]

def KnownSound {Value : Type} (context : OriginalContext cells.CellId Value) (facts : knowledge.UcpFacts) : Prop :=
  forall cell, facts.unique_cells cell = true -> forall left right,
    context left -> context right -> left cell = right cell

theorem rust_mark_unique_preserves_soundness {Value : Type}
    (context : OriginalContext cells.CellId Value) (facts next : knowledge.UcpFacts)
    (cell : cells.CellId) (changed : Bool) (before : KnownSound context facts)
    (established : forall left right, context left -> context right -> left cell = right cell)
    (returned : knowledge.UcpFacts.impl.mark_unique facts cell = .ok (changed, next)) :
    KnownSound context next := by
  classical
  have outputs := Result.ok_injective ((rust_mark_unique_matches_insert facts cell).symm.trans returned)
  have same := congrArg Prod.snd outputs
  change insertedFacts facts cell = next at same
  rw [← same]
  intro key member
  by_cases equal : key = cell
  · subst key
    exact established
  · exact before key (by simpa [insertedFacts, equal] using member)

theorem rust_mark_unique_preserves_other_cells
    (facts next : knowledge.UcpFacts) (cell other : cells.CellId) (changed : Bool)
    (different : other ≠ cell)
    (returned : knowledge.UcpFacts.impl.mark_unique facts cell = .ok (changed, next)) :
    next.unique_cells other = facts.unique_cells other := by
  have outputs := Result.ok_injective ((rust_mark_unique_matches_insert facts cell).symm.trans returned)
  have same := congrArg Prod.snd outputs
  change insertedFacts facts cell = next at same
  rw [← same]
  simp [insertedFacts, different]

theorem rust_mark_unique_reports_actual_progress
    (facts next : knowledge.UcpFacts) (cell : cells.CellId) (changed : Bool)
    (returned : knowledge.UcpFacts.impl.mark_unique facts cell = .ok (changed, next)) :
    changed = !facts.unique_cells cell := by
  have outputs := Result.ok_injective ((rust_mark_unique_matches_insert facts cell).symm.trans returned)
  exact (congrArg Prod.fst outputs).symm

theorem rust_initial_advice_is_not_assumed_unique (facts : knowledge.UcpFacts) (cell : cells.CellId)
    (advice : cell.kind = .Advice) :
    knowledge.UcpFacts.impl.mark_initial_unique facts cell = .ok (false, facts) := by
  simp [knowledge.UcpFacts.impl.mark_initial_unique, advice]

theorem rust_mark_initial_unique_preserves_soundness {Value : Type}
    (context : OriginalContext cells.CellId Value) (facts next : knowledge.UcpFacts)
    (cell : cells.CellId) (changed : Bool) (before : KnownSound context facts)
    (publicSound : cell.kind = .Instance ∨ cell.kind = .Fixed ->
      forall left right, context left -> context right -> left cell = right cell)
    (returned : knowledge.UcpFacts.impl.mark_initial_unique facts cell = .ok (changed, next)) :
    KnownSound context next := by
  cases kind : cell.kind with
  | Advice =>
      rw [rust_initial_advice_is_not_assumed_unique facts cell kind] at returned
      have same : facts = next := congrArg Prod.snd (Result.ok_injective returned)
      simpa [← same] using before
  | Instance =>
      simp only [knowledge.UcpFacts.impl.mark_initial_unique, kind] at returned
      exact rust_mark_unique_preserves_soundness context facts next cell changed before
        (publicSound (Or.inl kind)) returned
  | Fixed =>
      simp only [knowledge.UcpFacts.impl.mark_initial_unique, kind] at returned
      exact rust_mark_unique_preserves_soundness context facts next cell changed before
        (publicSound (Or.inr kind)) returned

-- Az Assign tenyleges eredmenyet a tenyleges Rust-K-frissites koveti, modellbeli helyettesites nelkul.
theorem rust_assign_then_insert_is_sound {F : Type} [Field F] (p : Nat) [CharP F p]
    (positive : 1 < (p : Int)) (constants : Constants F)
    (context : OriginalContext cells.CellId F) (facts next : knowledge.UcpFacts)
    (before : KnownSound context facts) (expression : expressions.UcpExpr) (cell : cells.CellId)
    (equation : forall assignment, context assignment -> evaluate constants assignment expression [] = 0)
    (inferred : rules.infer_assigned_cell_from_zero_equation_with_modulus expression facts
      (p : Int) = .ok (Option.some cell))
    (changed : Bool)
    (inserted : knowledge.UcpFacts.impl.mark_unique facts cell = .ok (changed, next)) :
    KnownSound context next := by
  apply rust_mark_unique_preserves_soundness context facts next cell changed before
    (rust_assign_sound p positive constants context facts before expression cell equation inferred) inserted

end SourceProof
