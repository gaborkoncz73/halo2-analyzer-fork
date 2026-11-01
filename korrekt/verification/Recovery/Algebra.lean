import Recovery.ExpressionDomains

/-!
Az algebrai szabalyok szabvanyos kommutativ gyurutulajdonsagokbol kovetkeznek.
Ezek strukturalt tetelfeltetelek, nem globalis axiomak. A konkret BigInt/test
implementacio megfelelese meg kulon bizonyitasi kotelezettseg.
-/

namespace Recovery

variable {Value : Type}

structure CommutativeRingLaws (ops : Arithmetic Value) : Prop where
  add_assoc : forall a b c, ops.add (ops.add a b) c = ops.add a (ops.add b c)
  add_comm : forall a b, ops.add a b = ops.add b a
  add_zero : forall a, ops.add a ops.zero = a
  add_neg : forall a, ops.add a (ops.neg a) = ops.zero
  mul_assoc : forall a b c, ops.mul (ops.mul a b) c = ops.mul a (ops.mul b c)
  mul_comm : forall a b, ops.mul a b = ops.mul b a
  mul_one : forall a, ops.mul a ops.one = a
  mul_zero : forall a, ops.mul a ops.zero = ops.zero
  mul_add : forall a b c, ops.mul a (ops.add b c) = ops.add (ops.mul a b) (ops.mul a c)

namespace CommutativeRingLaws

variable {ops : Arithmetic Value} (laws : CommutativeRingLaws ops)

include laws

theorem zero_add (a : Value) : ops.add ops.zero a = a := by
  rw [laws.add_comm, laws.add_zero]

theorem one_mul (a : Value) : ops.mul ops.one a = a := by
  rw [laws.mul_comm, laws.mul_one]

theorem zero_mul (a : Value) : ops.mul ops.zero a = ops.zero := by
  rw [laws.mul_comm, laws.mul_zero]

theorem neg_add_self (a : Value) : ops.add (ops.neg a) a = ops.zero := by
  rw [laws.add_comm, laws.add_neg]

theorem add_left_cancel {a b c : Value} (same : ops.add a b = ops.add a c) : b = c := by
  have cancelled := congrArg (ops.add (ops.neg a)) same
  simpa only [<- laws.add_assoc, laws.neg_add_self, laws.zero_add] using cancelled

theorem add_mul (a b c : Value) :
    ops.mul (ops.add a b) c = ops.add (ops.mul a c) (ops.mul b c) := by
  rw [laws.mul_comm (ops.add a b) c, laws.mul_add, laws.mul_comm c a, laws.mul_comm c b]

theorem add_four (a b c d : Value) :
    ops.add (ops.add a b) (ops.add c d) = ops.add (ops.add a c) (ops.add b d) := by
  rw [laws.add_assoc a b, <- laws.add_assoc b c d, laws.add_comm b c,
    laws.add_assoc c b d, <- laws.add_assoc a c]

theorem neg_add (a b : Value) :
    ops.neg (ops.add a b) = ops.add (ops.neg a) (ops.neg b) := by
  apply laws.add_left_cancel (a := ops.add a b)
  rw [laws.add_neg, laws.add_four, laws.add_neg, laws.add_neg, laws.add_zero]

theorem neg_mul (a b : Value) : ops.neg (ops.mul a b) = ops.mul (ops.neg a) b := by
  apply laws.add_left_cancel (a := ops.mul a b)
  rw [laws.add_neg, <- laws.add_mul, laws.add_neg, laws.zero_mul]

-- Csak igazolt baloldali inverzzel oszt; puszta nemnullasagot nem hasznal oszthatosagkent.
theorem solve_affine {a x b rhs inverse : Value}
    (equation : ops.add (ops.mul a x) b = rhs)
    (inverseCorrect : ops.mul inverse a = ops.one) :
    ops.mul (ops.add rhs (ops.neg b)) inverse = x := by
  have numerator : ops.add rhs (ops.neg b) = ops.mul a x := by
    rw [<- equation, laws.add_assoc, laws.add_neg, laws.add_zero]
  calc
    ops.mul (ops.add rhs (ops.neg b)) inverse = ops.mul (ops.mul a x) inverse := by rw [numerator]
    _ = ops.mul inverse (ops.mul a x) := laws.mul_comm _ _
    _ = ops.mul (ops.mul inverse a) x := (laws.mul_assoc _ _ _).symm
    _ = x := by rw [inverseCorrect, laws.one_mul]

end CommutativeRingLaws

end Recovery
