import Recovery.Algebra
import Recovery.Knowledge

/-!
Az affin egyutthato- es maradekdomainekbol kepzett vetitest modellezi.
A split altal eloallitott ket halmaz kozott nem kovetel fuggetlenseget.
Ha barmely egyutthato inverze hianyzik, az egesz vetites None eredmenyu.
-/

namespace Recovery

variable {Cell Value : Type}

structure AffineCover (Value : Type) where
  coefficients : List Value
  remainders : List Value
  deriving DecidableEq

def AffineSound (ctx : Context Cell Value) (ops : Arithmetic Value)
    (cell : Cell) (expr : Expression Cell Value) (cover : AffineCover Value) : Prop :=
  forall assignment, ctx assignment ->
    exists a, a ∈ cover.coefficients /\ exists b, b ∈ cover.remainders /\
      evaluate ops assignment expr = ops.add (ops.mul a (assignment cell)) b

-- A teljes listat inverzalja; egy hianyzo inverz nem maradhat ki az eredmenybol.
def invertAll (inverse : Value -> Option Value) : List Value -> Option (List (Value × Value))
  | [] => some []
  | coefficient :: rest => do
      let inverted <- inverse coefficient
      let tail <- invertAll inverse rest
      pure ((coefficient, inverted) :: tail)

def projectedValues (ops : Arithmetic Value) (inverses : List (Value × Value))
    (numerators : List Value) : List Value :=
  inverses.flatMap (fun pair => numerators.map (fun numerator => ops.mul numerator pair.2))

def projectAffine (limit : Nat) (ops : Arithmetic Value) (inverse : Value -> Option Value)
    (cover : AffineCover Value) (rhs : List Value) : Option (List Value) := do
  let numerators <- boundedCombine limit (fun r b => ops.add r (ops.neg b)) rhs cover.remainders
  let inverses <- invertAll inverse cover.coefficients
  if cover.coefficients.length * numerators.length <= limit then
    boundedList limit (projectedValues ops inverses numerators)
  else none

theorem invert_all_preserves_member {inverse : Value -> Option Value}
    {coefficients : List Value} {inverses : List (Value × Value)} {coefficient : Value}
    (success : invertAll inverse coefficients = some inverses)
    (member : coefficient ∈ coefficients) :
    exists inverted, inverse coefficient = some inverted /\ (coefficient, inverted) ∈ inverses := by
  induction coefficients generalizing inverses with
  | nil => cases member
  | cons first rest tailSound =>
      obtain ⟨inverted, firstInverse, remainder⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨tail, tailResult, recorded⟩ := Option.bind_eq_some_iff.mp remainder
      have same : (first, inverted) :: tail = inverses := Option.some.inj recorded
      subst inverses
      rcases List.mem_cons.mp member with same | inRest
      · subst coefficient
        exact ⟨inverted, firstInverse, by simp⟩
      · obtain ⟨value, inverseResult, pairMember⟩ := tailSound tailResult inRest
        exact ⟨value, inverseResult, List.mem_cons_of_mem _ pairMember⟩

theorem missing_inverse_aborts {inverse : Value -> Option Value}
    {coefficients : List Value} {coefficient : Value}
    (member : coefficient ∈ coefficients) (missing : inverse coefficient = none) :
    invertAll inverse coefficients = none := by
  cases result : invertAll inverse coefficients with
  | none => rfl
  | some inverses =>
      obtain ⟨_, found, _⟩ := invert_all_preserves_member result member
      rw [missing] at found
      cases found

theorem projected_values_contain_pair {ops : Arithmetic Value}
    {inverses : List (Value × Value)} {numerators : List Value}
    {coefficient inverted numerator : Value}
    (pairMember : (coefficient, inverted) ∈ inverses) (member : numerator ∈ numerators) :
    ops.mul numerator inverted ∈ projectedValues ops inverses numerators := by
  exact List.mem_flatMap.mpr
    ⟨(coefficient, inverted), pairMember, List.mem_map.mpr ⟨numerator, member, rfl⟩⟩

theorem projection_missing_inverse_aborts
    {ops : Arithmetic Value} {inverse : Value -> Option Value} {cover : AffineCover Value}
    {rhs : List Value} {limit : Nat} {coefficient : Value}
    (member : coefficient ∈ cover.coefficients) (missing : inverse coefficient = none) :
    projectAffine limit ops inverse cover rhs = none := by
  have noInverses := missing_inverse_aborts member missing
  cases numeratorResult : boundedCombine limit
      (fun r b => ops.add r (ops.neg b)) rhs cover.remainders with
  | none => simp [projectAffine, numeratorResult]
  | some values => simp [projectAffine, numeratorResult, noInverses]

-- A valodi kozos ertekadasbol szarmazo a,b,r harmas a Descartes-szorzatban is benne marad.
theorem affine_projection_sound
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {expr : Expression Cell Value} {cover : AffineCover Value} {rhs output : List Value}
    {inverse : Value -> Option Value} {limit : Nat}
    (laws : CommutativeRingLaws ops)
    (inverseSound : forall a inverted, inverse a = some inverted -> ops.mul inverted a = ops.one)
    (affine : AffineSound ctx ops cell expr cover)
    (rhsCover : forall assignment, ctx assignment -> evaluate ops assignment expr ∈ rhs)
    (success : projectAffine limit ops inverse cover rhs = some output) :
    Covers ctx cell (ListDomain output) := by
  obtain ⟨numerators, numeratorResult, remainder⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨inverses, inverseResult, bounded⟩ := Option.bind_eq_some_iff.mp remainder
  split at bounded
  · intro assignment valid
    obtain ⟨a, hasA, b, hasB, equation⟩ := affine assignment valid
    have numeratorMember := bounded_combine_preserves_pair numeratorResult (rhsCover assignment valid) hasB
    obtain ⟨inverted, invertedResult, pairMember⟩ := invert_all_preserves_member inverseResult hasA
    have member := projected_values_contain_pair (ops := ops) pairMember numeratorMember
    have solved := laws.solve_affine equation.symm (inverseSound a inverted invertedResult)
    rw [solved] at member
    exact bounded_list_preserves_member bounded member
  · cases bounded

theorem affine_projection_merge_sound
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell}
    {expr : Expression Cell Value} {cover : AffineCover Value} {rhs output : List Value}
    {inverse : Value -> Option Value} {limit : Nat} {knowledge : Knowledge Value}
    (laws : CommutativeRingLaws ops)
    (inverseSound : forall a inverted, inverse a = some inverted -> ops.mul inverted a = ops.one)
    (sound : Sound ctx cell knowledge) (affine : AffineSound ctx ops cell expr cover)
    (rhsCover : forall assignment, ctx assignment -> evaluate ops assignment expr ∈ rhs)
    (success : projectAffine limit ops inverse cover rhs = some output) :
    Sound ctx cell (mergeDomain knowledge (ListDomain output)) := by
  exact merge_domain_sound sound (affine_projection_sound laws inverseSound affine rhsCover success)

end Recovery
