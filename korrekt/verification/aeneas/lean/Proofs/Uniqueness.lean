import UcpVerified.Funs
import Mathlib.Algebra.Field.Basic

open Aeneas Aeneas.Std
open ucp_verified

namespace SourceProof

set_option maxHeartbeats 2000000

def scalarZero : expressions.UcpScalar -> Bool
  | .Zero => true
  | .Known value => decide (value = 0)
  | _ => false

def zeroConstant : expressions.UcpExpr -> Bool
  | .Const scalar => scalarZero scalar
  | _ => false

def uniqueSpec (known : cells.CellId -> Bool) : expressions.UcpExpr -> Bool
  | .Var cell => known cell
  | .Const _ => true
  | .Neg inner => uniqueSpec known inner
  | .Add left right => uniqueSpec known left && uniqueSpec known right
  | .Mul left right => zeroConstant left || zeroConstant right ||
      (uniqueSpec known left && uniqueSpec known right)
  | .Scale inner scalar => scalarZero scalar || uniqueSpec known inner

@[simp] theorem scalar_is_zero_correct (scalar : expressions.UcpScalar) :
    expressions.UcpScalar.impl.is_zero scalar = .ok (scalarZero scalar) := by
  cases scalar <;>
    simp [expressions.UcpScalar.impl.is_zero, scalarZero,
      num_bigint.bigint.BigInt.Insts.CoreConvertFromI32.from,
      num_bigint.bigint.BigInt.Insts.CoreCmpPartialEqBigInt.eq]
  split <;> simp_all

@[simp] theorem zero_constant_correct (expression : expressions.UcpExpr) :
    rules.is_zero_constant expression = .ok (zeroConstant expression) := by
  cases expression <;> simp [rules.is_zero_constant, zeroConstant]
  split <;> simp_all

@[simp] theorem known_cell_correct (facts : knowledge.UcpFacts) (cell : cells.CellId) :
    knowledge.UcpFacts.impl.is_unique facts cell = .ok (facts.unique_cells cell) := by
  simp [knowledge.UcpFacts.impl.is_unique, std.collections.hash.set.HashSet.impl.contains,
    core.borrow.Borrow.Blanket.borrow]

-- A tetel az automatikusan generalt fuggveny osszes veges kifejezesfajat lefedi.
theorem uniqueness_matches_spec (expression : expressions.UcpExpr) (facts : knowledge.UcpFacts) :
    rules.expression_is_unique expression facts = .ok (uniqueSpec facts.unique_cells expression) := by
  induction expression with
  | Var cell => simp [rules.expression_is_unique, uniqueSpec]
  | Const scalar => simp [rules.expression_is_unique, uniqueSpec]
  | Neg inner ih => simpa [rules.expression_is_unique, uniqueSpec] using ih
  | Add left right ihLeft ihRight =>
      rw [rules.expression_is_unique, ihLeft, ihRight]
      cases hLeft : uniqueSpec facts.unique_cells left <;> simp [uniqueSpec, hLeft]
  | Mul left right ihLeft ihRight =>
      rw [rules.expression_is_unique, zero_constant_correct, zero_constant_correct]
      cases hLeft : zeroConstant left <;> cases hRight : zeroConstant right <;>
        simp [hLeft, hRight, ihLeft, ihRight, uniqueSpec]
      split <;> simp_all
  | Scale inner scalar ih =>
      cases scalar <;>
        simp [rules.expression_is_unique, uniqueSpec, scalarZero, ih,
          num_bigint.bigint.BigInt.Insts.CoreConvertFromI32.from,
          num_bigint.bigint.BigInt.Insts.CoreCmpPartialEqBigInt.eq]
      split <;> simp_all

end SourceProof
