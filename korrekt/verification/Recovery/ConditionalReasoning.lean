import Recovery.ContextReasoning

/-!
A lefedo selector-domain osszes agara vegzett kovetkeztetest igazolja.
Egy bizonytalan ag nem hagyhato el: ilyenkor a regi lefedo domain a biztonsagos fallback.
-/

namespace Recovery

variable {Cell Value : Type}

def branchContext (ctx : Context Cell Value) (selector : Cell) (value : Value) : Context Cell Value :=
  fun assignment => ctx assignment /\ assignment selector = value

def branchUnion (selectors : ValueSet Value) (domains : Value -> ValueSet Value) : ValueSet Value :=
  fun value => exists selected, selectors selected /\ domains selected value

theorem conditional_domain_union_sound
    {ctx : Context Cell Value} {selector target : Cell} {selectors : ValueSet Value}
    {domains : Value -> ValueSet Value}
    (selectorCover : Covers ctx selector selectors)
    (branches : forall value, selectors value -> Covers (branchContext ctx selector value) target (domains value)) :
    Covers ctx target (branchUnion selectors domains) := by
  intro assignment valid
  have selected := selectorCover assignment valid
  exact ⟨assignment selector, selected, branches (assignment selector) selected assignment ⟨valid, rfl⟩⟩

theorem infeasible_branch_has_empty_cover {ctx : Context Cell Value} {selector target : Cell} {value : Value}
    (unsat : Not (Satisfiable (branchContext ctx selector value))) :
    Covers (branchContext ctx selector value) target (fun _ => False) := by
  intro assignment valid
  exact unsat ⟨assignment, valid⟩

theorem unresolved_branch_keeps_original_cover
    {ctx : Context Cell Value} {selector target : Cell} {value : Value} {domain : ValueSet Value}
    (cover : Covers ctx target domain) : Covers (branchContext ctx selector value) target domain := by
  intro assignment valid
  exact cover assignment valid.1

theorem conditional_common_value_exact
    {ctx : Context Cell Value} {selector target : Cell} {selectors : ValueSet Value} {value : Value}
    (sat : Satisfiable ctx) (selectorCover : Covers ctx selector selectors)
    (branches : forall selected, selectors selected ->
      Covers (branchContext ctx selector selected) target (Singleton value)) :
    Unique ctx target /\ Complete ctx target (Singleton value) := by
  have cover : Covers ctx target (Singleton value) := by
    intro assignment valid
    exact branches (assignment selector) (selectorCover assignment valid) assignment ⟨valid, rfl⟩
  exact ⟨singleton_cover_is_unique cover, singleton_cover_is_complete sat cover⟩

end Recovery
