import Std

/-!
A rendszer szemantikajat tetszoleges cella- es ertektipus felett adja meg.
A Gamma mar tartalmazza a rogzitett publikus megfigyeleseket; nem olvas privat witnesst.
Az ertektipus a kesobbi algebrai bizonyitasokban a kapcsolas testet jelenti.
-/

namespace Recovery

abbrev Assignment (Cell Value : Type) := Cell -> Value
abbrev Context (Cell Value : Type) := Assignment Cell Value -> Prop
abbrev ValueSet (Value : Type) := Value -> Prop

variable {Cell Value : Type}

def Included (left right : ValueSet Value) : Prop :=
  forall value, left value -> right value

def SameValues (left right : ValueSet Value) : Prop :=
  forall value, left value <-> right value

def Singleton (value : Value) : ValueSet Value := fun other => other = value

def Intersection (left right : ValueSet Value) : ValueSet Value :=
  fun value => left value /\ right value

def Union (left right : ValueSet Value) : ValueSet Value :=
  fun value => left value \/ right value

def Satisfiable (ctx : Context Cell Value) : Prop := exists assignment, ctx assignment

def Feasible (ctx : Context Cell Value) (cell : Cell) : ValueSet Value :=
  fun value => exists assignment, ctx assignment /\ assignment cell = value

def Covers (ctx : Context Cell Value) (cell : Cell) (domain : ValueSet Value) : Prop :=
  forall assignment, ctx assignment -> domain (assignment cell)

def SamplesSound (ctx : Context Cell Value) (cell : Cell) (samples : ValueSet Value) : Prop :=
  Included samples (Feasible ctx cell)

def Complete (ctx : Context Cell Value) (cell : Cell) (domain : ValueSet Value) : Prop :=
  SameValues domain (Feasible ctx cell)

def Unique (ctx : Context Cell Value) (cell : Cell) : Prop :=
  forall left right, ctx left -> ctx right -> left cell = right cell

def NonUnique (ctx : Context Cell Value) (cell : Cell) : Prop :=
  exists a b, Feasible ctx cell a /\ Feasible ctx cell b /\ Not (a = b)

theorem coverage_iff_feasible_included
    {ctx : Context Cell Value} {cell : Cell} {domain : ValueSet Value} :
    Covers ctx cell domain <-> Included (Feasible ctx cell) domain := by
  constructor
  · intro cover value feasible
    obtain ⟨assignment, valid, same⟩ := feasible
    rw [<- same]
    exact cover assignment valid
  · intro included assignment valid
    exact included (assignment cell) ⟨assignment, valid, rfl⟩

theorem complete_implies_coverage
    {ctx : Context Cell Value} {cell : Cell} {domain : ValueSet Value}
    (complete : Complete ctx cell domain) : Covers ctx cell domain := by
  intro assignment valid
  exact (complete (assignment cell)).mpr ⟨assignment, valid, rfl⟩

theorem non_unique_excludes_unique
    {ctx : Context Cell Value} {cell : Cell}
    (ambiguous : NonUnique ctx cell) : Not (Unique ctx cell) := by
  obtain ⟨a, b, ⟨left, leftValid, leftValue⟩, ⟨right, rightValid, rightValue⟩, distinct⟩ := ambiguous
  intro unique
  apply distinct
  calc
    a = left cell := leftValue.symm
    _ = right cell := unique left right leftValid rightValid
    _ = b := rightValue

end Recovery
