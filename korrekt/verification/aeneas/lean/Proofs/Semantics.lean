import Proofs.Uniqueness

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

-- Az absztrakt konstansok helyenkent kulon erteket kaphatnak, de nem fuggnek a witnesstol.
structure Constants (F : Type) [Zero F] where
  nonzero : List Bool -> F
  unknown : List Bool -> F
  nonzero_valid : forall path, nonzero path ≠ 0

def scalarValue {F : Type} [Ring F] (constants : Constants F) (path : List Bool) :
    expressions.UcpScalar -> F
  | .Zero => 0
  | .Known value => (value : F)
  | .NonZero => constants.nonzero path
  | .Unknown => constants.unknown path

def evaluate {F : Type} [Ring F] (constants : Constants F) (assignment : cells.CellId -> F) :
    expressions.UcpExpr -> List Bool -> F
  | .Var cell, _ => assignment cell
  | .Const scalar, path => scalarValue constants path scalar
  | .Neg inner, path => -evaluate constants assignment inner (false :: path)
  | .Add left right, path => evaluate constants assignment left (false :: path) +
      evaluate constants assignment right (true :: path)
  | .Mul left right, path => evaluate constants assignment left (false :: path) *
      evaluate constants assignment right (true :: path)
  | .Scale inner scalar, path => evaluate constants assignment inner (false :: path) *
      scalarValue constants path scalar

theorem scalar_zero_sound {F : Type} [Ring F] (constants : Constants F) (path : List Bool)
    (scalar : expressions.UcpScalar) (zero : scalarZero scalar = true) :
    scalarValue constants path scalar = 0 := by
  cases scalar <;> simp_all [scalarZero, scalarValue]

theorem zero_constant_sound {F : Type} [Ring F] (constants : Constants F)
    (assignment : cells.CellId -> F) (expression : expressions.UcpExpr) (path : List Bool)
    (zero : zeroConstant expression = true) : evaluate constants assignment expression path = 0 := by
  cases expression <;> simp only [zeroConstant] at zero
  case Const scalar => exact scalar_zero_sound constants path scalar zero
  all_goals cases zero

-- Az osszes K-ban szereplo cella egyezese elegendo a felismert kifejezes egyezesehez.
theorem unique_spec_sound {F : Type} [Ring F] (constants : Constants F)
    (known : cells.CellId -> Bool) (left right : cells.CellId -> F)
    (agree : forall cell, known cell = true -> left cell = right cell)
    (expression : expressions.UcpExpr) (path : List Bool)
    (unique : uniqueSpec known expression = true) :
    evaluate constants left expression path = evaluate constants right expression path := by
  induction expression generalizing path with
  | Var cell => exact agree cell unique
  | Const scalar => rfl
  | Neg inner ih => exact congrArg Neg.neg (ih _ unique)
  | Add first second ihFirst ihSecond =>
      obtain ⟨hFirst, hSecond⟩ := Bool.and_eq_true_iff.mp unique
      exact congrArg₂ (fun x y : F => x + y) (ihFirst _ hFirst) (ihSecond _ hSecond)
  | Mul first second ihFirst ihSecond =>
      rcases Bool.or_eq_true_iff.mp unique with zero | both
      · rcases Bool.or_eq_true_iff.mp zero with firstZero | secondZero
        · simp only [evaluate, zero_constant_sound constants left first _ firstZero,
            zero_constant_sound constants right first _ firstZero, zero_mul]
        · simp only [evaluate, zero_constant_sound constants left second _ secondZero,
            zero_constant_sound constants right second _ secondZero, mul_zero]
      · obtain ⟨hFirst, hSecond⟩ := Bool.and_eq_true_iff.mp both
        exact congrArg₂ (fun x y : F => x * y) (ihFirst _ hFirst) (ihSecond _ hSecond)
  | Scale inner scalar ih =>
      rcases Bool.or_eq_true_iff.mp unique with zero | innerUnique
      · simp only [evaluate, scalar_zero_sound constants path scalar zero, mul_zero]
      · exact congrArg (fun value => value * scalarValue constants path scalar) (ih _ innerUnique)

-- A tetel kozvetlenul az Aeneas altal generalt Rust-fuggveny eredmenyebol kovetkeztet.
theorem rust_uniqueness_sound {F : Type} [Ring F] (constants : Constants F)
    (context : (cells.CellId -> F) -> Prop) (facts : knowledge.UcpFacts)
    (knownSound : forall cell, facts.unique_cells cell = true ->
      forall left right, context left -> context right -> left cell = right cell)
    (expression : expressions.UcpExpr)
    (accepted : rules.expression_is_unique expression facts = .ok true) :
    forall left right, context left -> context right -> forall path,
      evaluate constants left expression path = evaluate constants right expression path := by
  have detected : uniqueSpec facts.unique_cells expression = true := by
    have same := (uniqueness_matches_spec expression facts).symm.trans accepted
    simpa using same
  intro left right leftValid rightValid path
  exact unique_spec_sound constants facts.unique_cells left right
    (fun cell known => knownSound cell known left right leftValid rightValid) expression path detected

end SourceProof
