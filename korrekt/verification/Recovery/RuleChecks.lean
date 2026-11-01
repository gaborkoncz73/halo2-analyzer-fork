import Recovery.Root
import Recovery.AllButOne
import Recovery.BaseConversion
import Recovery.PropagationChecks

/-!
A szabalyok pozitiv alkalmazasait es a lenyeges feltetelek elhagyasanak
ellenpeldait a kernel ellenorzi. A konkret peldak nem helyettesitik az
altalanos tetelek bizonyitasat, es nem a Rust parser tesztjei.
-/

namespace Recovery.Checks

theorem boolean_no_zero_divisors : NoZeroDivisors booleanArithmetic := by
  constructor
  intro a b zero
  cases a <;> cases b <;> simp_all [booleanArithmetic]

example : uniqueExpression booleanArithmetic (fun (_ : Unit) => false)
    (.mul (.const false) (.var ())) = true := by decide

-- A nulla egyutthato melletti egyenlet nem hatarozza meg az ismeretlent.
example :
    (forall assignment : Assignment Unit Bool,
      booleanArithmetic.mul false (assignment ()) = false) /\
    NonUnique (fun (_ : Assignment Unit Bool) => True) () := by
  constructor
  · intro assignment
    simp [booleanArithmetic]
  · exact ⟨false, true, ⟨fun _ => false, True.intro, rfl⟩,
      ⟨fun _ => true, True.intro, rfl⟩, by decide⟩

example : rootCandidates 4 booleanArithmetic
    (.scale (.mul (.factor false false) (.factor true true)) false) = none := by decide

example : rootCandidates 1 booleanArithmetic
    (.mul (.factor false false) (.factor true true)) = none := by decide

-- Osszetett modulusnal a nulla szorzatbol nem kovetkezik nullatenyezo.
example : ((3 * (3 - 1) : Int) % 6 = 0) /\
    Not ((3 : Int) % 6 = 0) /\ Not ((3 : Int) % 6 = 1) := by decide

def repeatedRoot : RootPolynomial Bool := .mul (.factor true false) (.factor true true)

theorem root_affine_example_recovers_zero :
    Covers (fun assignment => rootValue booleanArithmetic
      (evaluate booleanArithmetic assignment affineExample) repeatedRoot = false)
      () (Singleton false) := by
  have factsSound : FactsCover
      (fun assignment => rootValue booleanArithmetic
        (evaluate booleanArithmetic assignment affineExample) repeatedRoot = false)
      (fun (_ : Unit) => none) := by
    intro _ _ impossible
    cases impossible
  have recovered := root_then_affine_projection_sound
    (cell := ()) (facts := fun (_ : Unit) => none) (expr := affineExample)
    (polynomial := repeatedRoot) (roots := [true, true]) (output := [false, false])
    (cover := { coefficients := [true], remainders := [true] })
    (inverse := booleanInverse) (limit := 16)
    boolean_ring_laws boolean_no_zero_divisors factsSound boolean_inverse_sound
    (fun _ valid => valid) (by decide) (by decide) (by decide)
  intro assignment valid
  have member := recovered assignment valid
  simpa [ListDomain, Singleton] using member

example : Satisfiable (fun assignment : Assignment Unit Bool => rootValue booleanArithmetic
    (evaluate booleanArithmetic assignment affineExample) repeatedRoot = false) := by
  exact ⟨fun _ => false, by decide⟩

def twoBranches : List (Nat × Bool) := [(1, false), (2, true)]

abbrev branchContext (assignment : Assignment Nat Bool) : Prop :=
  assignment 0 = true /\ Bool.xor (assignment 1) (assignment 2) = true /\
    booleanArithmetic.mul (assignment 1)
      (booleanArithmetic.add (assignment 0) (booleanArithmetic.neg false)) = false /\
    booleanArithmetic.mul (assignment 2)
      (booleanArithmetic.add (assignment 0) (booleanArithmetic.neg true)) = false

theorem boolean_branch_products : BranchProducts branchContext booleanArithmetic 0 twoBranches := by
  intro assignment valid branch member
  simp only [twoBranches, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · subst branch
    exact valid.2.2.1
  · subst branch
    exact valid.2.2.2

theorem boolean_branch_sum (assignment : Assignment Nat Bool) (valid : branchContext assignment) :
    branchSum booleanArithmetic assignment twoBranches = true := by
  simpa [branchSum, twoBranches, booleanArithmetic] using valid.2.1

theorem boolean_all_but_one_first_exact : Covers branchContext 1 (Singleton false) := by
  exact all_but_one_exact (branches := twoBranches) (selected := (1, false))
    (selectorValue := true) (totalValue := true)
    boolean_ring_laws boolean_no_zero_divisors (by decide) (by decide)
    (fun _ valid => valid.1) boolean_branch_sum boolean_branch_products

theorem boolean_all_but_one_second_exact : Covers branchContext 2 (Singleton true) := by
  exact all_but_one_exact (branches := twoBranches) (selected := (2, true))
    (selectorValue := true) (totalValue := true)
    boolean_ring_laws boolean_no_zero_divisors (by decide) (by decide)
    (fun _ valid => valid.1) boolean_branch_sum boolean_branch_products

example : Satisfiable branchContext := by
  exact ⟨fun cell => decide (cell = 0 \/ cell = 2), by decide⟩

def duplicateBranches : List (Nat × Bool) := [(1, false), (2, false)]

abbrev duplicateContext (assignment : Assignment Nat Bool) : Prop :=
  assignment 0 = false /\ Bool.xor (assignment 1) (assignment 2) = true

theorem duplicate_branch_products : BranchProducts duplicateContext booleanArithmetic 0 duplicateBranches := by
  intro assignment valid branch member
  simp only [duplicateBranches, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same <;> subst branch <;> simp [booleanArithmetic, valid.1]

theorem duplicate_branch_sum (assignment : Assignment Nat Bool) (valid : duplicateContext assignment) :
    branchSum booleanArithmetic assignment duplicateBranches = true := by
  simpa [branchSum, duplicateBranches, booleanArithmetic] using valid.2

-- Ismetlodo gyokok mellett x es az osszeg is egyertelmu, a ket y megsem az.
theorem duplicate_roots_allow_non_unique :
    Unique duplicateContext 0 /\
    Stable duplicateContext (fun _ => true) /\
    (forall assignment, duplicateContext assignment -> branchSum booleanArithmetic assignment duplicateBranches = true) /\
    BranchProducts duplicateContext booleanArithmetic 0 duplicateBranches /\
    NonUnique duplicateContext 1 := by
  refine ⟨?_, ?_, duplicate_branch_sum, duplicate_branch_products, ?_⟩
  · intro left right leftValid rightValid
    exact leftValid.1.trans rightValid.1.symm
  · intro _ _ _ _
    rfl
  · exact ⟨false, true, ⟨fun cell => decide (cell = 2), by decide, by decide⟩,
      ⟨fun cell => decide (cell = 1), by decide, by decide⟩, by decide⟩

example : Not ((duplicateBranches.map Prod.snd).Nodup) := by decide

-- Az azonos hosszusag, a szamjegykorlat es a no-wrap feltetel kulon is szukseges.
example : packDigits 2 [1] = packDigits 2 [1, 0] /\ Not (([1] : List Nat) = [1, 0]) := by decide
example : packDigits 2 [2, 0] = packDigits 2 [0, 1] /\ Not (([2, 0] : List Nat) = [0, 1]) := by decide
example : packDigits 2 [0, 0] % 3 = packDigits 2 [1, 1] % 3 /\
    Not (([0, 0] : List Nat) = [1, 1]) := by decide
example : unpackDigits 10 2 123 = none := by decide
example : projectDigitValues 10 2 0 [37, 42] = [7, 2] := by decide
example : projectDigitValues 10 2 1 [37, 42] = [3, 4] := by decide
example : projectDigitValues 10 2 0 [37, 123] = [7] := by decide

abbrev decimalContext (assignment : Assignment Nat Nat) : Prop :=
  assignment 1 < 10 /\ assignment 2 <= 3 /\ assignment 0 = 37 /\
    packDigits 10 [assignment 1, assignment 2] % 101 = assignment 0 % 101

theorem decimal_example_exact (assignment : Assignment Nat Nat) (valid : decimalContext assignment) :
    assignment 1 = 7 /\ assignment 2 = 3 := by
  have decoded := base_conversion_exact_digits
    (ctx := decimalContext) (packed := 0) (digits := [1, 2]) (base := 10) (modulus := 101) (value := 37)
    (by decide)
    (by
      intro a h digit member
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same
      · subst digit; exact h.1
      · subst digit; omega)
    (by
      intro a h
      apply highest_digit_bound_prevents_wrap (lower := [a 1]) (highest := a 2) (maximum := 3)
      · intro digit member
        have same := List.mem_singleton.mp member
        exact same ▸ h.1
      · exact h.2.1
      · change 10 ^ 1 * (3 + 1) < 101
        decide)
    (fun _ h => h.2.2.2) (fun _ h => h.2.2.1) (by decide) assignment valid
  have expected : unpackDigits 10 2 37 = some [7, 3] := by decide
  simpa only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, expected,
    Option.some.injEq, List.cons.injEq, and_true] using decoded.symm

example : Satisfiable decimalContext := by
  exact ⟨fun cell => if cell = 0 then 37 else if cell = 1 then 7 else if cell = 2 then 3 else 0,
    by decide⟩

end Recovery.Checks
