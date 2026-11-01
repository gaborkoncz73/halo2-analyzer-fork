import Proofs.Semantics
import Mathlib.Algebra.CharP.Basic

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000

def scalarNonzero (scalar : expressions.UcpScalar) (modulus : Option Int) : Bool :=
  match scalar with
  | .NonZero => true
  | .Known value => match modulus with
      | Option.none => decide (value ≠ 0)
      | Option.some p => if 1 < p then decide (value.tmod p ≠ 0) else false
  | _ => false

def nonzeroConstant (expression : expressions.UcpExpr) (modulus : Option Int) : Bool :=
  match expression with
  | .Const scalar => scalarNonzero scalar modulus
  | _ => false

@[simp] theorem scalar_nonzero_correct (scalar : expressions.UcpScalar) (modulus : Option Int) :
    expressions.UcpScalar.impl.is_non_zero_with_modulus scalar modulus =
      .ok (scalarNonzero scalar modulus) := by
  cases scalar <;> cases modulus <;>
    simp [expressions.UcpScalar.impl.is_non_zero_with_modulus, 
      expressions.UcpScalar.impl.is_statically_non_zero, scalarNonzero,
      num_bigint.bigint.BigInt.Insts.CoreConvertFromI32.from,
      num_bigint.bigint.BigInt.Insts.CoreCmpPartialEqBigInt.eq,
      core.cmp.impls.PartialEqShared.ne,
      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      core.cmp.impls.PartialOrdShared.gt,
      core.cmp.PartialOrd.gt.default,
      core.cmp.PartialOrd.gt_body,
      num_bigint.bigint.BigInt.Insts.CoreCmpPartialOrdBigInt.partial_cmp,
      Shared1BigInt.Insts.CoreOpsArithRemShared0BigIntBigInt.rem,
      Int.compare_eq_gt]
  split_ifs <;> simp_all

@[simp] theorem nonzero_constant_correct (expression : expressions.UcpExpr) (modulus : Option Int) :
    rules.is_non_zero_constant expression modulus = .ok (nonzeroConstant expression modulus) := by
  cases expression <;> simp [rules.is_non_zero_constant, nonzeroConstant]
  split <;> simp_all

@[simp] theorem cell_clone_correct (cell : cells.CellId) :
    cells.CellId.Insts.CoreCloneClone.clone cell = .ok cell := by
  cases cell with
  | mk kind column row =>
    cases kind <;>
      simp [cells.CellId.Insts.CoreCloneClone.clone,
        cells.CellKind.Insts.CoreCloneClone.clone, core.clone.impls.CloneUsize.clone,
        core.clone.impls.CloneI32.clone, lift]

def noCandidate : rules.AssignAnalysis := ⟨Option.none, true⟩
def invalidAnalysis : rules.AssignAnalysis := ⟨Option.none, false⟩
def withCandidate (cell : cells.CellId) : rules.AssignAnalysis := ⟨Option.some cell, true⟩

def mergeAnalysis (left right : rules.AssignAnalysis) : rules.AssignAnalysis :=
  if left.valid && right.valid then
    match left.candidate, right.candidate with
    | Option.none, Option.none => noCandidate
    | Option.some cell, Option.none | Option.none, Option.some cell => withCandidate cell
    | Option.some _, Option.some _ => invalidAnalysis
  else invalidAnalysis

@[simp] theorem merge_analysis_correct (left right : rules.AssignAnalysis) :
    rules.AssignAnalysis.impl.merge_add left right = .ok (mergeAnalysis left right) := by
  cases left with
  | mk l lv =>
    cases right with
    | mk r rv =>
      cases lv <;> cases rv <;> cases l <;> cases r <;>
        rfl

def assignSpec (known : cells.CellId -> Bool) (modulus : Option Int)
    (expression : expressions.UcpExpr) : rules.AssignAnalysis :=
    if uniqueSpec known expression then noCandidate else
      match expression with
      | .Var cell => withCandidate cell
      | .Const _ => noCandidate
      | .Neg inner => assignSpec known modulus inner
      | .Add left right => mergeAnalysis (assignSpec known modulus left) (assignSpec known modulus right)
      | .Scale inner scalar =>
          if scalarNonzero scalar modulus then assignSpec known modulus inner
          else match scalar with
            | .Unknown => invalidAnalysis
            | _ => noCandidate
      | .Mul left right =>
          if zeroConstant left || zeroConstant right ||
              (uniqueSpec known left && uniqueSpec known right) then noCandidate
          else if nonzeroConstant left modulus then assignSpec known modulus right
          else if nonzeroConstant right modulus then assignSpec known modulus left
          else invalidAnalysis
termination_by expression

-- Az egesz rekurziv Assign-jeloltkereseshez bizonyitja a forras es a specifikacio egyezeset.
theorem assign_matches_spec (expression : expressions.UcpExpr) (facts : knowledge.UcpFacts)
    (modulus : Option Int) :
    rules.analyze_assign_candidate expression facts modulus =
      .ok (assignSpec facts.unique_cells modulus expression) := by
  induction expression with
  | Var cell =>
      simp [rules.analyze_assign_candidate, uniqueness_matches_spec, assignSpec, uniqueSpec,
        rules.AssignAnalysis.impl.none, rules.AssignAnalysis.impl.candidate, noCandidate, withCandidate]
      split_ifs <;> simp_all
  | Const scalar =>
      simp [rules.analyze_assign_candidate, uniqueness_matches_spec, assignSpec, uniqueSpec,
        rules.AssignAnalysis.impl.none, noCandidate]
  | Neg inner ih =>
      simp [rules.analyze_assign_candidate, uniqueness_matches_spec, assignSpec, uniqueSpec, ih,
        rules.AssignAnalysis.impl.none, noCandidate]
      split_ifs <;> simp_all
  | Add left right ihLeft ihRight =>
      simp [rules.analyze_assign_candidate, uniqueness_matches_spec, assignSpec, ihLeft, ihRight,
        rules.AssignAnalysis.impl.none, noCandidate]
      split_ifs <;> simp_all
  | Scale inner scalar ih =>
      cases scalar <;>
        simp [rules.analyze_assign_candidate, uniqueness_matches_spec, assignSpec, ih,
          rules.AssignAnalysis.impl.none, rules.AssignAnalysis.impl.invalid, noCandidate, invalidAnalysis] <;>
        split_ifs <;> simp_all
  | Mul left right ihLeft ihRight =>
      simp only [rules.analyze_assign_candidate, uniqueness_matches_spec]
      simp [rules.analyze_product_assign_candidate, uniqueness_matches_spec, ihLeft, ihRight,
        assignSpec, uniqueSpec, rules.AssignAnalysis.impl.none, rules.AssignAnalysis.impl.invalid,
        noCandidate, invalidAnalysis]
      split_ifs <;> simp_all

end SourceProof
