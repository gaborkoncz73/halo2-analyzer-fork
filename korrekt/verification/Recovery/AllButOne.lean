import Recovery.Uniqueness
import Recovery.Normalization

/-!
A sum(y_i)=e es y_i*(x-root_i)=0 rendszer All-But-One szabalyat bizonyitja.
A gyokoknak a tenyleges ertektipusban kell kulonbozniuk, nem csak egeszkent.
A Rustban megkovetelt 0..n gyokhalmaz helyett az algebrai tetel altalanosabb,
de kulon tetel igazolja az indexgyokok modulo-kulonbozosegenek meretfeltetelet.
-/

namespace Recovery

variable {Cell Value : Type}

def branchSum (ops : Arithmetic Value) (assignment : Assignment Cell Value) :
    List (Cell × Value) -> Value
  | [] => ops.zero
  | branch :: rest => ops.add (assignment branch.1) (branchSum ops assignment rest)

def BranchProducts (ctx : Context Cell Value) (ops : Arithmetic Value)
    (selector : Cell) (branches : List (Cell × Value)) : Prop :=
  forall assignment, ctx assignment -> forall branch, branch ∈ branches ->
    ops.mul (assignment branch.1) (ops.add (assignment selector) (ops.neg branch.2)) = ops.zero

theorem inactive_branch_zero {ops : Arithmetic Value} {value selector root : Value}
    (laws : CommutativeRingLaws ops) (domain : NoZeroDivisors ops)
    (product : ops.mul value (ops.add selector (ops.neg root)) = ops.zero)
    (inactive : Not (selector = root)) : value = ops.zero := by
  rcases domain.mul_eq_zero _ _ product with zero | factorZero
  · exact zero
  · exact False.elim (inactive ((laws.difference_eq_zero_iff selector root).mp factorZero))

theorem branch_sum_zero {ops : Arithmetic Value} (laws : CommutativeRingLaws ops)
    (assignment : Assignment Cell Value) (branches : List (Cell × Value))
    (zeros : forall branch, branch ∈ branches -> assignment branch.1 = ops.zero) :
    branchSum ops assignment branches = ops.zero := by
  induction branches with
  | nil => rfl
  | cons first rest tailZero =>
      have firstZero := zeros first (by simp)
      have remainder := tailZero (fun branch member => zeros branch (List.mem_cons_of_mem first member))
      simp only [branchSum, firstZero, remainder, laws.add_zero]

theorem selected_branch_sum {ops : Arithmetic Value} (laws : CommutativeRingLaws ops)
    (assignment : Assignment Cell Value) {branches : List (Cell × Value)} {selected : Cell × Value}
    (distinct : (branches.map Prod.snd).Nodup) (member : selected ∈ branches)
    (inactive : forall branch, branch ∈ branches -> Not (branch.2 = selected.2) ->
      assignment branch.1 = ops.zero) :
    branchSum ops assignment branches = assignment selected.1 := by
  induction branches with
  | nil => cases member
  | cons first rest tailSelected =>
      obtain ⟨absent, restDistinct⟩ := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp member with same | inRest
      · subst selected
        have tailZero : forall branch, branch ∈ rest -> assignment branch.1 = ops.zero := by
          intro branch included
          have different : Not (branch.2 = first.2) := by
            intro sameRoot
            have rootMember : branch.2 ∈ rest.map Prod.snd := List.mem_map.mpr ⟨branch, included, rfl⟩
            exact absent (sameRoot ▸ rootMember)
          exact inactive branch (List.mem_cons_of_mem first included) different
        simp only [branchSum, branch_sum_zero laws assignment rest tailZero, laws.add_zero]
      · have firstDifferent : Not (first.2 = selected.2) := by
          intro sameRoot
          have rootMember : selected.2 ∈ rest.map Prod.snd := List.mem_map.mpr ⟨selected, inRest, rfl⟩
          exact absent (sameRoot.symm ▸ rootMember)
        have firstZero := inactive first (by simp) firstDifferent
        have tailValue := tailSelected restDistinct inRest
          (fun branch included => inactive branch (List.mem_cons_of_mem first included))
        simp only [branchSum, firstZero, tailValue, laws.zero_add]

theorem selected_value_eq_sum
    {ctx : Context Cell Value} {ops : Arithmetic Value} {selector : Cell}
    {branches : List (Cell × Value)} {selected : Cell × Value}
    (laws : CommutativeRingLaws ops) (domain : NoZeroDivisors ops)
    (distinct : (branches.map Prod.snd).Nodup) (member : selected ∈ branches)
    (products : BranchProducts ctx ops selector branches)
    (assignment : Assignment Cell Value) (valid : ctx assignment)
    (active : assignment selector = selected.2) :
    assignment selected.1 = branchSum ops assignment branches := by
  apply Eq.symm
  apply selected_branch_sum laws assignment distinct member
  intro branch included different
  apply inactive_branch_zero laws domain (products assignment valid branch included)
  intro sameRoot
  exact different (sameRoot.symm.trans active)

theorem all_but_one_unique
    {ctx : Context Cell Value} {ops : Arithmetic Value} {selector : Cell}
    {branches : List (Cell × Value)} {selected : Cell × Value}
    {total : Assignment Cell Value -> Value}
    (laws : CommutativeRingLaws ops) (domain : NoZeroDivisors ops)
    (distinct : (branches.map Prod.snd).Nodup) (member : selected ∈ branches)
    (selectorUnique : Unique ctx selector) (totalStable : Stable ctx total)
    (sumEquation : forall assignment, ctx assignment -> branchSum ops assignment branches = total assignment)
    (products : BranchProducts ctx ops selector branches) : Unique ctx selected.1 := by
  intro left right leftValid rightValid
  have sameSelector := selectorUnique left right leftValid rightValid
  by_cases active : left selector = selected.2
  · have rightActive := sameSelector.symm.trans active
    calc
      left selected.1 = branchSum ops left branches :=
        selected_value_eq_sum laws domain distinct member products left leftValid active
      _ = total left := sumEquation left leftValid
      _ = total right := totalStable left right leftValid rightValid
      _ = branchSum ops right branches := (sumEquation right rightValid).symm
      _ = right selected.1 :=
        (selected_value_eq_sum laws domain distinct member products right rightValid rightActive).symm
  · have leftZero := inactive_branch_zero laws domain (products left leftValid selected member) active
    have rightInactive : Not (right selector = selected.2) := fun same => active (sameSelector.trans same)
    have rightZero := inactive_branch_zero laws domain (products right rightValid selected member) rightInactive
    exact leftZero.trans rightZero.symm

theorem all_but_one_exact [DecidableEq Value]
    {ctx : Context Cell Value} {ops : Arithmetic Value} {selector : Cell}
    {branches : List (Cell × Value)} {selected : Cell × Value} {selectorValue totalValue : Value}
    (laws : CommutativeRingLaws ops) (domain : NoZeroDivisors ops)
    (distinct : (branches.map Prod.snd).Nodup) (member : selected ∈ branches)
    (selectorKnown : forall assignment, ctx assignment -> assignment selector = selectorValue)
    (sumEquation : forall assignment, ctx assignment -> branchSum ops assignment branches = totalValue)
    (products : BranchProducts ctx ops selector branches) :
    Covers ctx selected.1 (Singleton (if selectorValue = selected.2 then totalValue else ops.zero)) := by
  intro assignment valid
  change assignment selected.1 = if selectorValue = selected.2 then totalValue else ops.zero
  split
  · rename_i active
    exact (selected_value_eq_sum laws domain distinct member products assignment valid
      ((selectorKnown assignment valid).trans active)).trans (sumEquation assignment valid)
  · rename_i inactive
    apply inactive_branch_zero laws domain (products assignment valid selected member)
    intro same
    exact inactive ((selectorKnown assignment valid).symm.trans same)

theorem index_roots_distinct_modulo {count modulus left right : Nat}
    (withinModulus : count <= modulus) (leftBound : left < count) (rightBound : right < count) :
    ((left : Int) % (modulus : Int) = (right : Int) % (modulus : Int)) <-> left = right := by
  rw [Int.emod_eq_of_lt (by omega : 0 <= (left : Int)) (by omega : (left : Int) < (modulus : Int)),
    Int.emod_eq_of_lt (by omega : 0 <= (right : Int)) (by omega : (right : Int) < (modulus : Int))]
  omega

end Recovery
