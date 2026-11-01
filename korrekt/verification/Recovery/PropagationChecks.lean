import Recovery.AffineSplit

/-!
A ket elemu testen ellenorzi az algebrai feltetelek egy konkret megvalositasat.
Az altalanos tetelek nem ettol a veges teszttol fuggnek; a peldak a modell
hatarait es a veszelyes agakat ellenorzik, nativ bizonyitasi gyorsitas nelkul.
-/

namespace Recovery.Checks

def booleanArithmetic : Arithmetic Bool where
  zero := false
  one := true
  add := Bool.xor
  mul := Bool.and
  neg := id

theorem boolean_ring_laws : CommutativeRingLaws booleanArithmetic := by
  constructor
  · intro a b c; cases a <;> cases b <;> cases c <;> decide
  · intro a b; cases a <;> cases b <;> decide
  · intro a; cases a <;> decide
  · intro a; cases a <;> decide
  · intro a b c; cases a <;> cases b <;> cases c <;> decide
  · intro a b; cases a <;> cases b <;> decide
  · intro a; cases a <;> decide
  · intro a; cases a <;> decide
  · intro a b c; cases a <;> cases b <;> cases c <;> decide

def booleanInverse : Bool -> Option Bool
  | false => none
  | true => some true

theorem boolean_inverse_sound (a inverted : Bool)
    (success : booleanInverse a = some inverted) :
    booleanArithmetic.mul inverted a = booleanArithmetic.one := by
  cases a with
  | false => cases success
  | true => cases success; rfl

-- A tul nagy eredmenyt nem egy kisebb jelolthalmazzal helyettesiti.
example : boundedList 1 ([0, 1] : List Nat) = none := by decide

-- Egyetlen nem invertalhato lehetoseg is megakadalyozza a vetitest.
example : projectAffine 16 booleanArithmetic booleanInverse
    { coefficients := [false, true], remainders := [false] } [false] = none := by decide

-- A ketszer fuggo szorzatot nem tekinti affin kifejezesnek.
example : splitAffine 16 booleanArithmetic (fun (_ : Unit) => none) ()
    (.mul (.var ()) (.var ())) = none := by decide

-- A nullaval skalazas a belso domain ismerete nelkul is helyes affin felbontas.
example : splitAffine 16 booleanArithmetic (fun (_ : Unit) => none) ()
    (.scale (.var ()) false) =
      some { coefficients := [false], remainders := [false] } := by decide

-- A kozos valtozo ket elofordulasanak korrelaciojat elhagyva csak bovebb domain keletkezik.
example : expressionDomain 4 booleanArithmetic (fun (_ : Unit) => some [false, true])
    (.add (.var ()) (.var ())) = some [false, true, true, false] := by decide

example (assignment : Assignment Unit Bool) :
    evaluate booleanArithmetic assignment (.add (.var ()) (.var ())) = false := by
  cases value : assignment () <;> simp [evaluate, booleanArithmetic, value]

def affineExample : Expression Unit Bool := .add (.scale (.var ()) true) (.const true)

-- A teljes felbontas-vetites lancot alkalmazza: x+1=1 a ket elemu testen x=0-t ad.
theorem boolean_affine_example_recovers_zero :
    Covers (fun assignment => evaluate booleanArithmetic assignment affineExample = true)
      () (Singleton false) := by
  let cover : AffineCover Bool := { coefficients := [true], remainders := [true] }
  have factsSound : FactsCover
      (fun assignment => evaluate booleanArithmetic assignment affineExample = true)
      (fun (_ : Unit) => none) := by
    intro _ _ impossible
    cases impossible
  have recovered := split_then_project_sound
    (ctx := fun assignment => evaluate booleanArithmetic assignment affineExample = true)
    (cell := ()) (facts := fun (_ : Unit) => none) (expr := affineExample)
    (cover := cover) (rhs := [true]) (output := [false])
    (inverse := booleanInverse) (limit := 16)
    boolean_ring_laws factsSound boolean_inverse_sound
    (by intro assignment valid; simp [valid]) (by decide) (by decide)
  intro assignment valid
  have member := recovered assignment valid
  simpa only [ListDomain, List.mem_singleton] using member

theorem boolean_affine_example_satisfiable :
    Satisfiable (fun assignment => evaluate booleanArithmetic assignment affineExample = true) := by
  exact ⟨fun _ => false, by decide⟩

theorem boolean_affine_example_exact :
    Unique (fun assignment => evaluate booleanArithmetic assignment affineExample = true) () /\
    Complete (fun assignment => evaluate booleanArithmetic assignment affineExample = true)
      () (Singleton false) := by
  exact ⟨singleton_cover_is_unique boolean_affine_example_recovers_zero,
    singleton_cover_is_complete boolean_affine_example_satisfiable boolean_affine_example_recovers_zero⟩

end Recovery.Checks
