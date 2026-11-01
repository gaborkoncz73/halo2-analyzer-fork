import Recovery.AffineProjection

/-!
Az affin felbontas epitolepeseit es rekurziv, korlatos modelljet bizonyitja.
Ket celvaltozo-fuggo tenyezo szorzatabol nem hagyja el a negyzetes tagot:
a szorzast csak az egyik egyutthatodomain pontos {0} alakjanal fogadja el.
-/

namespace Recovery

variable {Cell Value : Type}

def addAffine (limit : Nat) (ops : Arithmetic Value)
    (left right : AffineCover Value) : Option (AffineCover Value) := do
  let coefficients <- boundedCombine limit ops.add left.coefficients right.coefficients
  let remainders <- boundedCombine limit ops.add left.remainders right.remainders
  pure { coefficients, remainders }

def negateAffine (limit : Nat) (ops : Arithmetic Value)
    (cover : AffineCover Value) : Option (AffineCover Value) := do
  let coefficients <- boundedMap limit ops.neg cover.coefficients
  let remainders <- boundedMap limit ops.neg cover.remainders
  pure { coefficients, remainders }

def scaleAffine (limit : Nat) (ops : Arithmetic Value)
    (cover : AffineCover Value) (coefficient : Value) : Option (AffineCover Value) := do
  let coefficients <- boundedMap limit (fun a => ops.mul a coefficient) cover.coefficients
  let remainders <- boundedMap limit (fun b => ops.mul b coefficient) cover.remainders
  pure { coefficients, remainders }

def multiplyAffine (limit : Nat) (ops : Arithmetic Value)
    (dependent : AffineCover Value) (independent : List Value) : Option (AffineCover Value) := do
  let coefficients <- boundedCombine limit ops.mul dependent.coefficients independent
  let remainders <- boundedCombine limit ops.mul dependent.remainders independent
  pure { coefficients, remainders }

def splitAffine [DecidableEq Cell] [DecidableEq Value]
    (limit : Nat) (ops : Arithmetic Value) (facts : Cell -> Option (List Value))
    (target : Cell) : Expression Cell Value -> Option (AffineCover Value)
  | .var cell =>
      if cell = target then some { coefficients := [ops.one], remainders := [ops.zero] }
      else facts cell |>.map (fun values => { coefficients := [ops.zero], remainders := values })
  | .const value => some { coefficients := [ops.zero], remainders := [value] }
  | .add left right => do
      let l <- splitAffine limit ops facts target left
      let r <- splitAffine limit ops facts target right
      addAffine limit ops l r
  | .neg inner => do
      let cover <- splitAffine limit ops facts target inner
      negateAffine limit ops cover
  | .scale inner coefficient =>
      if coefficient = ops.zero then
        some { coefficients := [ops.zero], remainders := [ops.zero] }
      else do
        let cover <- splitAffine limit ops facts target inner
        scaleAffine limit ops cover coefficient
  | .mul left right => do
      let l <- splitAffine limit ops facts target left
      let r <- splitAffine limit ops facts target right
      if l.coefficients = [ops.zero] then multiplyAffine limit ops r l.remainders
      else if r.coefficients = [ops.zero] then multiplyAffine limit ops l r.remainders
      else none

theorem affine_add_sound
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {left right : Expression Cell Value} {l r output : AffineCover Value} {limit : Nat}
    (laws : CommutativeRingLaws ops)
    (leftSound : AffineSound ctx ops cell left l) (rightSound : AffineSound ctx ops cell right r)
    (success : addAffine limit ops l r = some output) :
    AffineSound ctx ops cell (.add left right) output := by
  obtain ⟨coefficients, coefficientResult, remainder⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨remainders, remainderResult, recorded⟩ := Option.bind_eq_some_iff.mp remainder
  have same : { coefficients, remainders : AffineCover Value } = output := Option.some.inj recorded
  subst output
  intro assignment valid
  obtain ⟨a, hasA, b, hasB, leftEquation⟩ := leftSound assignment valid
  obtain ⟨c, hasC, d, hasD, rightEquation⟩ := rightSound assignment valid
  refine ⟨ops.add a c, bounded_combine_preserves_pair coefficientResult hasA hasC,
    ops.add b d, bounded_combine_preserves_pair remainderResult hasB hasD, ?_⟩
  change ops.add (evaluate ops assignment left) (evaluate ops assignment right) = _
  rw [leftEquation, rightEquation, laws.add_four, laws.add_mul]

theorem affine_negate_sound
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {expr : Expression Cell Value} {cover output : AffineCover Value} {limit : Nat}
    (laws : CommutativeRingLaws ops) (sound : AffineSound ctx ops cell expr cover)
    (success : negateAffine limit ops cover = some output) :
    AffineSound ctx ops cell (.neg expr) output := by
  obtain ⟨coefficients, coefficientResult, remainder⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨remainders, remainderResult, recorded⟩ := Option.bind_eq_some_iff.mp remainder
  have same : { coefficients, remainders : AffineCover Value } = output := Option.some.inj recorded
  subst output
  intro assignment valid
  obtain ⟨a, hasA, b, hasB, equation⟩ := sound assignment valid
  refine ⟨ops.neg a, bounded_map_preserves_member coefficientResult hasA,
    ops.neg b, bounded_map_preserves_member remainderResult hasB, ?_⟩
  change ops.neg (evaluate ops assignment expr) = _
  rw [equation, laws.neg_add, laws.neg_mul]

theorem affine_scale_sound
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {expr : Expression Cell Value} {cover output : AffineCover Value} {limit : Nat} {scalar : Value}
    (laws : CommutativeRingLaws ops) (sound : AffineSound ctx ops cell expr cover)
    (success : scaleAffine limit ops cover scalar = some output) :
    AffineSound ctx ops cell (.scale expr scalar) output := by
  obtain ⟨coefficients, coefficientResult, remainder⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨remainders, remainderResult, recorded⟩ := Option.bind_eq_some_iff.mp remainder
  have same : { coefficients, remainders : AffineCover Value } = output := Option.some.inj recorded
  subst output
  intro assignment valid
  obtain ⟨a, hasA, b, hasB, equation⟩ := sound assignment valid
  refine ⟨ops.mul a scalar,
    bounded_map_preserves_member (op := fun value => ops.mul value scalar) coefficientResult hasA,
    ops.mul b scalar,
    bounded_map_preserves_member (op := fun value => ops.mul value scalar) remainderResult hasB, ?_⟩
  change ops.mul (evaluate ops assignment expr) scalar = _
  rw [equation, laws.add_mul, laws.mul_assoc a (assignment cell) scalar,
    laws.mul_comm (assignment cell) scalar, <- laws.mul_assoc]

theorem zero_affine_remainder_covers
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {expr : Expression Cell Value} {cover : AffineCover Value}
    (laws : CommutativeRingLaws ops) (sound : AffineSound ctx ops cell expr cover)
    (zero : cover.coefficients = [ops.zero]) :
    forall assignment, ctx assignment -> evaluate ops assignment expr ∈ cover.remainders := by
  intro assignment valid
  obtain ⟨a, hasA, b, hasB, equation⟩ := sound assignment valid
  have same : a = ops.zero := by simpa [zero] using hasA
  rw [same, laws.zero_mul, laws.zero_add] at equation
  rw [equation]
  exact hasB

theorem affine_multiply_sound
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {left right : Expression Cell Value} {dependent output : AffineCover Value}
    {independent : List Value} {limit : Nat}
    (laws : CommutativeRingLaws ops) (sound : AffineSound ctx ops cell left dependent)
    (rightCover : forall assignment, ctx assignment -> evaluate ops assignment right ∈ independent)
    (success : multiplyAffine limit ops dependent independent = some output) :
    AffineSound ctx ops cell (.mul left right) output := by
  obtain ⟨coefficients, coefficientResult, remainder⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨remainders, remainderResult, recorded⟩ := Option.bind_eq_some_iff.mp remainder
  have same : { coefficients, remainders : AffineCover Value } = output := Option.some.inj recorded
  subst output
  intro assignment valid
  obtain ⟨a, hasA, b, hasB, equation⟩ := sound assignment valid
  have rightMember := rightCover assignment valid
  refine ⟨ops.mul a (evaluate ops assignment right),
    bounded_combine_preserves_pair coefficientResult hasA rightMember,
    ops.mul b (evaluate ops assignment right),
    bounded_combine_preserves_pair remainderResult hasB rightMember, ?_⟩
  change ops.mul (evaluate ops assignment left) (evaluate ops assignment right) = _
  rw [equation, laws.add_mul, laws.mul_assoc a (assignment cell),
    laws.mul_comm (assignment cell), <- laws.mul_assoc]

theorem affine_mul_comm_sound
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {left right : Expression Cell Value} {cover : AffineCover Value}
    (laws : CommutativeRingLaws ops)
    (sound : AffineSound ctx ops cell (.mul right left) cover) :
    AffineSound ctx ops cell (.mul left right) cover := by
  intro assignment valid
  obtain ⟨a, hasA, b, hasB, equation⟩ := sound assignment valid
  refine ⟨a, hasA, b, hasB, ?_⟩
  change ops.mul (evaluate ops assignment left) (evaluate ops assignment right) = _
  rw [laws.mul_comm]
  exact equation

theorem split_affine_sound [DecidableEq Cell] [DecidableEq Value]
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {facts : Cell -> Option (List Value)} {limit : Nat}
    (laws : CommutativeRingLaws ops) (factsSound : FactsCover ctx facts)
    (expr : Expression Cell Value) {output : AffineCover Value}
    (success : splitAffine limit ops facts cell expr = some output) :
    AffineSound ctx ops cell expr output := by
  induction expr generalizing output with
  | var sourceCell =>
      simp only [splitAffine] at success
      split at success
      · rename_i same
        cases success
        subst sourceCell
        intro assignment _
        refine ⟨ops.one, by simp, ops.zero, by simp, ?_⟩
        simp only [evaluate, laws.one_mul, laws.add_zero]
      · obtain ⟨values, factResult, same⟩ := Option.map_eq_some_iff.mp success
        cases same
        intro assignment valid
        refine ⟨ops.zero, by simp, assignment sourceCell,
          factsSound sourceCell values factResult assignment valid, ?_⟩
        simp only [evaluate, laws.zero_mul, laws.zero_add]
  | const value =>
      cases success
      intro assignment _
      refine ⟨ops.zero, by simp, value, by simp, ?_⟩
      simp only [evaluate, laws.zero_mul, laws.zero_add]
  | add left right leftSound rightSound =>
      obtain ⟨l, leftResult, rest⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨r, rightResult, combined⟩ := Option.bind_eq_some_iff.mp rest
      exact affine_add_sound laws (leftSound leftResult) (rightSound rightResult) combined
  | neg inner innerSound =>
      obtain ⟨cover, innerResult, negated⟩ := Option.bind_eq_some_iff.mp success
      exact affine_negate_sound laws (innerSound innerResult) negated
  | scale inner scalar innerSound =>
      simp only [splitAffine] at success
      split at success
      · rename_i zero
        cases success
        intro assignment _
        refine ⟨ops.zero, by simp, ops.zero, by simp, ?_⟩
        simp only [evaluate, zero, laws.mul_zero, laws.zero_mul, laws.add_zero]
      · obtain ⟨cover, innerResult, scaled⟩ := Option.bind_eq_some_iff.mp success
        exact affine_scale_sound laws (innerSound innerResult) scaled
  | mul left right leftSound rightSound =>
      obtain ⟨l, leftResult, rest⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨r, rightResult, multiplied⟩ := Option.bind_eq_some_iff.mp rest
      split at multiplied
      · rename_i zero
        exact affine_mul_comm_sound laws (affine_multiply_sound laws (rightSound rightResult)
          (zero_affine_remainder_covers laws (leftSound leftResult) zero) multiplied)
      · split at multiplied
        · rename_i _ zero
          exact affine_multiply_sound laws (leftSound leftResult)
            (zero_affine_remainder_covers laws (rightSound rightResult) zero) multiplied
        · cases multiplied

-- Az affin felbontas es a vetites egyutt mar nem ker kesz AffineSound-premisszat.
theorem split_then_project_sound [DecidableEq Cell] [DecidableEq Value]
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {facts : Cell -> Option (List Value)} {expr : Expression Cell Value}
    {cover : AffineCover Value} {rhs output : List Value}
    {inverse : Value -> Option Value} {limit : Nat}
    (laws : CommutativeRingLaws ops) (factsSound : FactsCover ctx facts)
    (inverseSound : forall a inverted, inverse a = some inverted -> ops.mul inverted a = ops.one)
    (rhsCover : forall assignment, ctx assignment -> evaluate ops assignment expr ∈ rhs)
    (splitResult : splitAffine limit ops facts cell expr = some cover)
    (projectResult : projectAffine limit ops inverse cover rhs = some output) :
    Covers ctx cell (ListDomain output) := by
  exact affine_projection_sound laws inverseSound (split_affine_sound laws factsSound expr splitResult)
    rhsCover projectResult

theorem split_then_project_merge_sound [DecidableEq Cell] [DecidableEq Value]
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {facts : Cell -> Option (List Value)} {expr : Expression Cell Value}
    {cover : AffineCover Value} {rhs output : List Value} {knowledge : Knowledge Value}
    {inverse : Value -> Option Value} {limit : Nat}
    (laws : CommutativeRingLaws ops) (factsSound : FactsCover ctx facts)
    (inverseSound : forall a inverted, inverse a = some inverted -> ops.mul inverted a = ops.one)
    (sound : Sound ctx cell knowledge)
    (rhsCover : forall assignment, ctx assignment -> evaluate ops assignment expr ∈ rhs)
    (splitResult : splitAffine limit ops facts cell expr = some cover)
    (projectResult : projectAffine limit ops inverse cover rhs = some output) :
    Sound ctx cell (mergeDomain knowledge (ListDomain output)) := by
  exact merge_domain_sound sound
    (split_then_project_sound laws factsSound inverseSound rhsCover splitResult projectResult)

-- A Rust null-egyenlet alapu kovetkeztetesenek kozvetlen szemantikai esete.
theorem zero_equation_projection_sound [DecidableEq Cell] [DecidableEq Value]
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {facts : Cell -> Option (List Value)} {expr : Expression Cell Value}
    {cover : AffineCover Value} {output : List Value}
    {inverse : Value -> Option Value} {limit : Nat}
    (laws : CommutativeRingLaws ops) (factsSound : FactsCover ctx facts)
    (inverseSound : forall a inverted, inverse a = some inverted -> ops.mul inverted a = ops.one)
    (equation : forall assignment, ctx assignment -> evaluate ops assignment expr = ops.zero)
    (splitResult : splitAffine limit ops facts cell expr = some cover)
    (projectResult : projectAffine limit ops inverse cover [ops.zero] = some output) :
    Covers ctx cell (ListDomain output) := by
  exact split_then_project_sound laws factsSound inverseSound
    (fun assignment valid => List.mem_singleton.mpr (equation assignment valid)) splitResult projectResult

end Recovery
