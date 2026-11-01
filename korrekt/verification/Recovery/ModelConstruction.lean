import Recovery.Domains

/-!
A megoldo nelkuli modellepites matematikai modellje. A feltetelezett ertek szukiti a kontextust.
Ebben a kontextusban a kielegito ertekadas valodi mintat ad, az ellentmondas pedig kizarja a jeloltet.
A `model_construction.rs` kodja nincs kinyerve, a mintak SAT-valasza a solver-feltevesre epul.
-/

namespace Recovery

variable {Cell Value : Type}

/-- Az eredeti kontextus megszoritasa egy feltetelezett cellaertekre. -/
def Assuming (ctx : Context Cell Value) (cell : Cell) (value : Value) : Context Cell Value :=
  fun assignment => ctx assignment /\ assignment cell = value

/-- A szigoritott kerdes SAT-valasza az eredeti kontextusban is megvalosithato erteket ad. -/
theorem strengthened_model_is_feasible {ctx : Context Cell Value} {cell : Cell} {value : Value}
    {hints : Assignment Cell Value -> Prop}
    (model : exists assignment, Assuming ctx cell value assignment /\ hints assignment) :
    Feasible ctx cell value := by
  obtain ⟨assignment, ⟨valid, same⟩, _⟩ := model
  exact ⟨assignment, valid, same⟩

/-- Ket diszjunkt lefedo domain a feltetelezes mellett kizarja a jeloltet. -/
theorem hypothesis_conflict_refutes {ctx : Context Cell Value} {cell other : Cell} {value : Value}
    {left right : ValueSet Value}
    (coversLeft : Covers (Assuming ctx cell value) other left)
    (coversRight : Covers (Assuming ctx cell value) other right)
    (disjoint : forall entry, left entry -> right entry -> False) :
    Not (Feasible ctx cell value) := by
  rintro ⟨assignment, valid, same⟩
  have assumed : Assuming ctx cell value assignment := ⟨valid, same⟩
  exact disjoint _ (coversLeft assignment assumed) (coversRight assignment assumed)

/-- Ha egy lefedo domain minden esete lehetetlen, maga a jelolt is lehetetlen. -/
theorem case_split_refutes {ctx : Context Cell Value} {cell other : Cell} {value : Value}
    {domain : ValueSet Value}
    (covers : Covers (Assuming ctx cell value) other domain)
    (branches : forall entry, domain entry ->
      Not (Feasible (Assuming ctx cell value) other entry)) :
    Not (Feasible ctx cell value) := by
  rintro ⟨assignment, valid, same⟩
  have assumed : Assuming ctx cell value assignment := ⟨valid, same⟩
  exact branches _ (covers assignment assumed) ⟨assignment, assumed, rfl⟩

/-- A kizart jelolt eltavolitasa megorzi a lefedest. -/
theorem refutation_preserves_coverage {ctx : Context Cell Value} {cell : Cell} {value : Value}
    {domain : ValueSet Value} (covers : Covers ctx cell domain)
    (refuted : Not (Feasible ctx cell value)) :
    Covers ctx cell (fun entry => domain entry /\ Not (entry = value)) := by
  intro assignment valid
  refine ⟨covers assignment valid, ?_⟩
  intro same
  exact refuted ⟨assignment, valid, same⟩

/-- Lefedo domain, amelynek minden eleme megvalosithato, teljes. -/
theorem constructed_samples_complete {ctx : Context Cell Value} {cell : Cell}
    {domain : ValueSet Value} (covers : Covers ctx cell domain)
    (feasible : forall entry, domain entry -> Feasible ctx cell entry) :
    Complete ctx cell domain := by
  intro entry
  constructor
  · exact feasible entry
  · rintro ⟨assignment, valid, same⟩
    exact same ▸ covers assignment valid

end Recovery
