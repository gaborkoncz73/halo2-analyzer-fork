import Recovery.FieldReasoning

/-!
A kifejezeselemzo ismert skalaros Var/Const/Op/Zero es Assign szabalyait bizonyitja.
A K tenyei csak egyertelmuseget jelentenek, nem ismert konkret erteket vagy nemnullasagot.
-/

namespace Recovery

variable {Cell Value : Type}

def Stable (ctx : Context Cell Value) (value : Assignment Cell Value -> Value) : Prop :=
  forall left right, ctx left -> ctx right -> value left = value right

def zeroConstant [DecidableEq Value] (ops : Arithmetic Value) : Expression Cell Value -> Bool
  | .const value => decide (value = ops.zero)
  | _ => false

def uniqueExpression [DecidableEq Value] (ops : Arithmetic Value) (known : Cell -> Bool) :
    Expression Cell Value -> Bool
  | .var cell => known cell
  | .const _ => true
  | .neg inner => uniqueExpression ops known inner
  | .scale inner scalar => if scalar = ops.zero then true else uniqueExpression ops known inner
  | .add left right => uniqueExpression ops known left && uniqueExpression ops known right
  | .mul left right => (zeroConstant ops left || zeroConstant ops right) ||
      (uniqueExpression ops known left && uniqueExpression ops known right)

theorem zero_constant_evaluates_zero [DecidableEq Value]
    {ops : Arithmetic Value} {expr : Expression Cell Value} (detected : zeroConstant ops expr = true)
    (assignment : Assignment Cell Value) : evaluate ops assignment expr = ops.zero := by
  cases expr <;> simp only [zeroConstant] at detected
  case const value =>
    have zero : value = ops.zero := of_decide_eq_true detected
    exact zero
  all_goals cases detected

theorem unique_expression_sound [DecidableEq Value]
    {ctx : Context Cell Value} {ops : Arithmetic Value} {known : Cell -> Bool}
    (laws : CommutativeRingLaws ops) (knownSound : forall cell, known cell = true -> Unique ctx cell)
    (expr : Expression Cell Value) (detected : uniqueExpression ops known expr = true) :
    Stable ctx (fun assignment => evaluate ops assignment expr) := by
  induction expr with
  | var cell => exact knownSound cell detected
  | const value => intro _ _ _ _; rfl
  | neg inner innerSound =>
      intro left right leftValid rightValid
      change ops.neg (evaluate ops left inner) = ops.neg (evaluate ops right inner)
      exact congrArg ops.neg (innerSound detected left right leftValid rightValid)
  | scale inner scalar innerSound =>
      by_cases zero : scalar = ops.zero
      · intro left right _ _
        simp only [evaluate, zero, laws.mul_zero]
      · have innerDetected : uniqueExpression ops known inner = true := by
          simpa only [uniqueExpression, ite_eq_right zero] using detected
        intro left right leftValid rightValid
        change ops.mul (evaluate ops left inner) scalar = ops.mul (evaluate ops right inner) scalar
        exact congrArg (fun value => ops.mul value scalar)
          (innerSound innerDetected left right leftValid rightValid)
  | add first second firstSound secondSound =>
      obtain ⟨firstDetected, secondDetected⟩ := Bool.and_eq_true_iff.mp detected
      intro left right leftValid rightValid
      change ops.add (evaluate ops left first) (evaluate ops left second) =
        ops.add (evaluate ops right first) (evaluate ops right second)
      have firstEqual : evaluate ops left first = evaluate ops right first :=
        firstSound firstDetected left right leftValid rightValid
      have secondEqual : evaluate ops left second = evaluate ops right second :=
        secondSound secondDetected left right leftValid rightValid
      rw [firstEqual, secondEqual]
  | mul first second firstSound secondSound =>
      rcases Bool.or_eq_true_iff.mp detected with zero | both
      · rcases Bool.or_eq_true_iff.mp zero with firstZero | secondZero
        · intro left right _ _
          change ops.mul (evaluate ops left first) (evaluate ops left second) =
            ops.mul (evaluate ops right first) (evaluate ops right second)
          rw [zero_constant_evaluates_zero firstZero left,
            zero_constant_evaluates_zero firstZero right, laws.zero_mul, laws.zero_mul]
        · intro left right _ _
          change ops.mul (evaluate ops left first) (evaluate ops left second) =
            ops.mul (evaluate ops right first) (evaluate ops right second)
          rw [zero_constant_evaluates_zero secondZero left,
            zero_constant_evaluates_zero secondZero right, laws.mul_zero, laws.mul_zero]
      · obtain ⟨firstDetected, secondDetected⟩ := Bool.and_eq_true_iff.mp both
        intro left right leftValid rightValid
        change ops.mul (evaluate ops left first) (evaluate ops left second) =
          ops.mul (evaluate ops right first) (evaluate ops right second)
        have firstEqual : evaluate ops left first = evaluate ops right first :=
          firstSound firstDetected left right leftValid rightValid
        have secondEqual : evaluate ops left second = evaluate ops right second :=
          secondSound secondDetected left right leftValid rightValid
        rw [firstEqual, secondEqual]

-- Az Assign nem igenyel konkret e erteket: a ket modellbeli egyenlosege elegendo.
theorem assign_from_stable_remainder
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {coefficient : Value} {remainder : Assignment Cell Value -> Value}
    (laws : CommutativeRingLaws ops) (domain : NoZeroDivisors ops)
    (nonzero : Not (coefficient = ops.zero)) (stable : Stable ctx remainder)
    (equation : forall assignment, ctx assignment ->
      ops.add (ops.mul coefficient (assignment cell)) (remainder assignment) = ops.zero) :
    Unique ctx cell := by
  intro left right leftValid rightValid
  have sameRest := stable left right leftValid rightValid
  have sameSum := (equation left leftValid).trans (equation right rightValid).symm
  rw [sameRest] at sameSum
  exact laws.mul_left_cancel_nonzero domain nonzero (laws.add_right_cancel sameSum)

end Recovery
