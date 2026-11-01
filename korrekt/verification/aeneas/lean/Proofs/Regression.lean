import Proofs.AssignSoundness

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

def emptyFacts : knowledge.UcpFacts := ⟨fun _ => false⟩
def firstCell : cells.CellId := ⟨.Advice, 0#usize, 0#i32⟩
def secondCell : cells.CellId := ⟨.Advice, 1#usize, 0#i32⟩

-- A regressziok a forrasbol generalt fuggvenyekre vonatkoznak, nem kulon Rust-masolatra.
theorem zero_product_is_unique (expression : expressions.UcpExpr) :
    rules.expression_is_unique (.Mul (.Const .Zero) expression) emptyFacts = .ok true := by
  rw [uniqueness_matches_spec]
  rfl

theorem repeated_candidate_is_rejected :
    rules.analyze_assign_candidate (.Add (.Var firstCell) (.Var firstCell)) emptyFacts
      (Option.some 5) = .ok invalidAnalysis := by
  rw [assign_matches_spec]
  simp [assignSpec, uniqueSpec, emptyFacts, mergeAnalysis, withCandidate, invalidAnalysis]

theorem unknown_factor_is_rejected :
    rules.analyze_assign_candidate (.Scale (.Var firstCell) .Unknown) emptyFacts
      (Option.some 5) = .ok invalidAnalysis := by
  rw [assign_matches_spec]
  simp [assignSpec, uniqueSpec, emptyFacts, scalarZero, scalarNonzero]

theorem modulus_multiple_is_not_inverted (p : Nat) (positive : 1 < (p : Int)) :
    rules.analyze_assign_candidate (.Scale (.Var firstCell) (.Known (p : Int))) emptyFacts
      (Option.some (p : Int)) = .ok noCandidate := by
  rw [assign_matches_spec]
  simp [assignSpec, uniqueSpec, scalarZero, scalarNonzero, emptyFacts, positive]

theorem nonlinear_product_is_rejected :
    rules.analyze_assign_candidate (.Mul (.Var firstCell) (.Var secondCell)) emptyFacts
      (Option.some 5) = .ok invalidAnalysis := by
  rw [assign_matches_spec]
  simp [assignSpec, uniqueSpec, emptyFacts, zeroConstant, nonzeroConstant]

theorem nonzero_factor_finds_candidate :
    rules.analyze_assign_candidate (.Mul (.Const .NonZero) (.Var firstCell)) emptyFacts
      (Option.some 5) = .ok (withCandidate firstCell) := by
  rw [assign_matches_spec]
  simp [assignSpec, uniqueSpec, emptyFacts, zeroConstant, nonzeroConstant, scalarZero, scalarNonzero]

end SourceProof
