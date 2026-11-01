import Recovery.Uniqueness
import Recovery.AffineSplit

/-!
A mar faktorizalt Root-szabaly szemantikai modelljet bizonyitja.
A ket tenyezoalak parameter-root es root-parameter; a kozos affin
parameter kinyereset vegzo Rust-linearizalo parser meg nem resze a bizonyitasnak.
-/

namespace Recovery

inductive RootPolynomial (Value : Type) where
  | factor (root : Value) (reversed : Bool)
  | mul (left right : RootPolynomial Value)
  | neg (inner : RootPolynomial Value)
  | scale (inner : RootPolynomial Value) (scalar : Value)

variable {Cell Value : Type}

def rootValue (ops : Arithmetic Value) (parameter : Value) : RootPolynomial Value -> Value
  | .factor root reversed =>
      if reversed then ops.add root (ops.neg parameter) else ops.add parameter (ops.neg root)
  | .mul left right => ops.mul (rootValue ops parameter left) (rootValue ops parameter right)
  | .neg inner => ops.neg (rootValue ops parameter inner)
  | .scale inner scalar => ops.mul (rootValue ops parameter inner) scalar

def rootCandidates [DecidableEq Value] (limit : Nat) (ops : Arithmetic Value) :
    RootPolynomial Value -> Option (List Value)
  | .factor root _ => boundedList limit [root]
  | .mul left right => do
      let l <- rootCandidates limit ops left
      let r <- rootCandidates limit ops right
      boundedList limit (l ++ r)
  | .neg inner => rootCandidates limit ops inner
  | .scale inner scalar =>
      if scalar = ops.zero then none else rootCandidates limit ops inner

theorem root_candidates_sound [DecidableEq Value]
    {ops : Arithmetic Value} {limit : Nat}
    (laws : CommutativeRingLaws ops) (domain : NoZeroDivisors ops)
    (polynomial : RootPolynomial Value) {output : List Value} {parameter : Value}
    (success : rootCandidates limit ops polynomial = some output)
    (zero : rootValue ops parameter polynomial = ops.zero) : parameter ∈ output := by
  induction polynomial generalizing output with
  | factor root reversed =>
      have same : parameter = root := by
        cases reversed with
        | false => exact (laws.difference_eq_zero_iff parameter root).mp zero
        | true => exact ((laws.difference_eq_zero_iff root parameter).mp zero).symm
      subst parameter
      exact bounded_list_preserves_member success (by simp)
  | mul left right leftSound rightSound =>
      obtain ⟨l, leftResult, rest⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨r, rightResult, combined⟩ := Option.bind_eq_some_iff.mp rest
      have factors : ops.mul (rootValue ops parameter left) (rootValue ops parameter right) = ops.zero := zero
      rcases domain.mul_eq_zero _ _ factors with leftZero | rightZero
      · exact bounded_list_preserves_member combined
          (List.mem_append_left _ (leftSound leftResult leftZero))
      · exact bounded_list_preserves_member combined
          (List.mem_append_right _ (rightSound rightResult rightZero))
  | neg inner innerSound =>
      exact innerSound success ((laws.neg_eq_zero_iff _).mp zero)
  | scale inner scalar innerSound =>
      by_cases scalarZero : scalar = ops.zero
      · simp only [rootCandidates, ite_eq_left scalarZero] at success
        cases success
      · have innerResult : rootCandidates limit ops inner = some output := by
          simpa only [rootCandidates, ite_eq_right scalarZero] using success
        have product : ops.mul (rootValue ops parameter inner) scalar = ops.zero := zero
        rcases domain.mul_eq_zero _ _ product with innerZero | impossible
        · exact innerSound innerResult innerZero
        · exact False.elim (scalarZero impossible)

theorem root_expression_domain_sound [DecidableEq Value]
    {ctx : Context Cell Value} {ops : Arithmetic Value} {limit : Nat}
    {expr : Expression Cell Value} {polynomial : RootPolynomial Value} {output : List Value}
    (laws : CommutativeRingLaws ops) (domain : NoZeroDivisors ops)
    (success : rootCandidates limit ops polynomial = some output)
    (equation : forall assignment, ctx assignment ->
      rootValue ops (evaluate ops assignment expr) polynomial = ops.zero) :
    forall assignment, ctx assignment -> evaluate ops assignment expr ∈ output := by
  intro assignment valid
  exact root_candidates_sound laws domain polynomial success (equation assignment valid)

theorem root_cell_domain_sound [DecidableEq Value]
    {ctx : Context Cell Value} {ops : Arithmetic Value} {limit : Nat} {cell : Cell}
    {polynomial : RootPolynomial Value} {output : List Value}
    (laws : CommutativeRingLaws ops) (domain : NoZeroDivisors ops)
    (success : rootCandidates limit ops polynomial = some output)
    (equation : forall assignment, ctx assignment ->
      rootValue ops (assignment cell) polynomial = ops.zero) : Covers ctx cell (ListDomain output) := by
  intro assignment valid
  exact root_candidates_sound laws domain polynomial success (equation assignment valid)

-- A Root-bol kapott kifejezesdomainnel tovabbvezeti a mar bizonyitott affin vetitest.
theorem root_then_affine_projection_sound [DecidableEq Cell] [DecidableEq Value]
    {ctx : Context Cell Value} {ops : Arithmetic Value} {cell : Cell} {limit : Nat}
    {facts : Cell -> Option (List Value)} {expr : Expression Cell Value}
    {polynomial : RootPolynomial Value} {roots output : List Value} {cover : AffineCover Value}
    {inverse : Value -> Option Value}
    (laws : CommutativeRingLaws ops) (domain : NoZeroDivisors ops)
    (factsSound : FactsCover ctx facts)
    (inverseSound : forall a inverted, inverse a = some inverted -> ops.mul inverted a = ops.one)
    (equation : forall assignment, ctx assignment ->
      rootValue ops (evaluate ops assignment expr) polynomial = ops.zero)
    (rootResult : rootCandidates limit ops polynomial = some roots)
    (splitResult : splitAffine limit ops facts cell expr = some cover)
    (projectResult : projectAffine limit ops inverse cover roots = some output) :
    Covers ctx cell (ListDomain output) := by
  exact split_then_project_sound laws factsSound inverseSound
    (root_expression_domain_sound laws domain rootResult equation) splitResult projectResult

end Recovery
