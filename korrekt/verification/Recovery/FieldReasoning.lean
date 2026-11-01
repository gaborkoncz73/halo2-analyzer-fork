import Recovery.Algebra

/-!
A Root, Assign es All-But-One szabalyokhoz a gyurutulajdonsagok mellett
a nullosztok hianyat is megkoveteli. Ezt a feltetelt nem allitja tetszoleges modulusra.
-/

namespace Recovery

variable {Value : Type} {ops : Arithmetic Value}

structure NoZeroDivisors (ops : Arithmetic Value) : Prop where
  mul_eq_zero : forall a b, ops.mul a b = ops.zero -> a = ops.zero \/ b = ops.zero

namespace CommutativeRingLaws

variable (laws : CommutativeRingLaws ops)

include laws

theorem neg_zero : ops.neg ops.zero = ops.zero := by
  have inverse := laws.add_neg ops.zero
  simpa only [laws.zero_add] using inverse

theorem neg_eq_zero_iff (value : Value) : ops.neg value = ops.zero <-> value = ops.zero := by
  constructor
  · intro zero
    have inverse := laws.add_neg value
    simpa only [zero, laws.add_zero] using inverse
  · intro zero
    rw [zero, laws.neg_zero]

theorem difference_eq_zero_iff (left right : Value) :
    ops.add left (ops.neg right) = ops.zero <-> left = right := by
  constructor
  · intro zero
    have shifted := congrArg (fun value => ops.add value right) zero
    simpa only [laws.add_assoc, laws.neg_add_self, laws.add_zero, laws.zero_add] using shifted
  · intro same
    rw [same, laws.add_neg]

theorem add_right_cancel {left right rest : Value}
    (same : ops.add left rest = ops.add right rest) : left = right := by
  apply laws.add_left_cancel (a := rest)
  rw [laws.add_comm rest left, laws.add_comm rest right]
  exact same

theorem mul_right_cancel_nonzero (domain : NoZeroDivisors ops)
    {left right factor : Value} (nonzero : Not (factor = ops.zero))
    (same : ops.mul left factor = ops.mul right factor) : left = right := by
  have zero : ops.mul (ops.add left (ops.neg right)) factor = ops.zero := by
    rw [laws.add_mul, <- laws.neg_mul, same, laws.add_neg]
  rcases domain.mul_eq_zero _ _ zero with difference | impossible
  · exact (laws.difference_eq_zero_iff left right).mp difference
  · exact False.elim (nonzero impossible)

theorem mul_left_cancel_nonzero (domain : NoZeroDivisors ops)
    {left right factor : Value} (nonzero : Not (factor = ops.zero))
    (same : ops.mul factor left = ops.mul factor right) : left = right := by
  apply laws.mul_right_cancel_nonzero domain nonzero
  rw [laws.mul_comm left factor, laws.mul_comm right factor]
  exact same

end CommutativeRingLaws

end Recovery
