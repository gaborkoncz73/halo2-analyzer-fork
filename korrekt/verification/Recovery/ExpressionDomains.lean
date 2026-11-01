import Recovery.FiniteDomains

/-!
Az ismert konstansokat tartalmazo kifejezesek rekurziv domain-kiertekeleset modellezi.
Az eredmeny lefedeset strukturalis indukcioval igazolja, korrelalt reszfak mellett is.
A nullaertek-felismero gyorsitasok es az ismeretlen UcpScalar-esetek meg nem szerepelnek benne.
-/

namespace Recovery

structure Arithmetic (Value : Type) where
  zero : Value
  one : Value
  add : Value -> Value -> Value
  mul : Value -> Value -> Value
  neg : Value -> Value

inductive Expression (Cell Value : Type) where
  | var (cell : Cell)
  | const (value : Value)
  | add (left right : Expression Cell Value)
  | mul (left right : Expression Cell Value)
  | neg (inner : Expression Cell Value)
  | scale (inner : Expression Cell Value) (coefficient : Value)

variable {Cell Value : Type}

def evaluate (ops : Arithmetic Value) (assignment : Assignment Cell Value) :
    Expression Cell Value -> Value
  | .var cell => assignment cell
  | .const value => value
  | .add left right => ops.add (evaluate ops assignment left) (evaluate ops assignment right)
  | .mul left right => ops.mul (evaluate ops assignment left) (evaluate ops assignment right)
  | .neg inner => ops.neg (evaluate ops assignment inner)
  | .scale inner coefficient => ops.mul (evaluate ops assignment inner) coefficient

def expressionDomain (limit : Nat) (ops : Arithmetic Value)
    (facts : Cell -> Option (List Value)) : Expression Cell Value -> Option (List Value)
  | .var cell => facts cell
  | .const value => boundedList limit [value]
  | .add left right => do
      let l <- expressionDomain limit ops facts left
      let r <- expressionDomain limit ops facts right
      boundedCombine limit ops.add l r
  | .mul left right => do
      let l <- expressionDomain limit ops facts left
      let r <- expressionDomain limit ops facts right
      boundedCombine limit ops.mul l r
  | .neg inner => do
      let values <- expressionDomain limit ops facts inner
      boundedMap limit ops.neg values
  | .scale inner coefficient => do
      let values <- expressionDomain limit ops facts inner
      boundedMap limit (fun value => ops.mul value coefficient) values

def FactsCover (ctx : Context Cell Value) (facts : Cell -> Option (List Value)) : Prop :=
  forall cell values, facts cell = some values -> Covers ctx cell (ListDomain values)

-- A tetel nem tesz fel fuggetlenseget a reszkifejezesek valtozoirol.
theorem expression_domain_sound
    {ctx : Context Cell Value} {facts : Cell -> Option (List Value)}
    {ops : Arithmetic Value} {limit : Nat} (factsSound : FactsCover ctx facts)
    (expr : Expression Cell Value) {output : List Value}
    (success : expressionDomain limit ops facts expr = some output)
    (assignment : Assignment Cell Value) (valid : ctx assignment) :
    evaluate ops assignment expr ∈ output := by
  induction expr generalizing output with
  | var cell => exact factsSound cell output success assignment valid
  | const value =>
      exact bounded_list_preserves_member success (by simp [evaluate])
  | add left right leftSound rightSound =>
      obtain ⟨l, leftResult, rest⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨r, rightResult, combined⟩ := Option.bind_eq_some_iff.mp rest
      exact bounded_combine_preserves_pair combined (leftSound leftResult) (rightSound rightResult)
  | mul left right leftSound rightSound =>
      obtain ⟨l, leftResult, rest⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨r, rightResult, combined⟩ := Option.bind_eq_some_iff.mp rest
      exact bounded_combine_preserves_pair combined (leftSound leftResult) (rightSound rightResult)
  | neg inner innerSound =>
      obtain ⟨values, innerResult, mapped⟩ := Option.bind_eq_some_iff.mp success
      exact bounded_map_preserves_member mapped (innerSound innerResult)
  | scale inner coefficient innerSound =>
      obtain ⟨values, innerResult, mapped⟩ := Option.bind_eq_some_iff.mp success
      exact bounded_map_preserves_member (op := fun value => ops.mul value coefficient)
        mapped (innerSound innerResult)

end Recovery
