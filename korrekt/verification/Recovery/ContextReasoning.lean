import Recovery.GlobalKnowledge
import Recovery.SolverSteps

/-!
A keresesi hint-ek, a gyengitett SMT-reszhalmaz es az uj hipotetikus
premisszak hatasat kulon kezeli. Reszhalmazos SAT nem teljes modellbizonyitek.
-/

namespace Recovery

variable {Cell Value : Type}

def searchContext (ctx : Context Cell Value) (state : AnalysisState Cell Value) : Context Cell Value :=
  fun assignment => ctx assignment /\ state.searchFacts assignment

theorem search_context_equivalent {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) (assignment : Assignment Cell Value) :
    searchContext ctx state assignment <-> ctx assignment := by
  exact ⟨fun valid => valid.1, fun valid => ⟨valid, sound.search assignment valid⟩⟩

theorem search_feasible_iff_original {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) (cell : Cell) (value : Value) :
    Feasible (searchContext ctx state) cell value <-> Feasible ctx cell value := by
  constructor
  · intro feasible
    obtain ⟨assignment, valid, same⟩ := feasible
    exact ⟨assignment, valid.1, same⟩
  · intro feasible
    obtain ⟨assignment, valid, same⟩ := feasible
    exact ⟨assignment, ⟨valid, sound.search assignment valid⟩, same⟩

theorem hinted_exclusion_proves_original_coverage
    {ctx : Context Cell Value} {state : AnalysisState Cell Value} {cell : Cell} {domain : ValueSet Value}
    (sound : AnalysisSound ctx state)
    (unsat : Not (Satisfiable (fun assignment =>
      searchContext ctx state assignment /\ Not (domain (assignment cell))))) : Covers ctx cell domain := by
  have cover := exclusion_unsat_proves_coverage unsat
  intro assignment valid
  exact cover assignment ⟨valid, sound.search assignment valid⟩

theorem hinted_candidate_unsat_allows_original_removal
    {ctx : Context Cell Value} {state : AnalysisState Cell Value} {cell : Cell}
    {domain : ValueSet Value} {value : Value}
    (sound : AnalysisSound ctx state) (cover : Covers ctx cell domain)
    (unsat : Not (Feasible (searchContext ctx state) cell value)) :
    Covers ctx cell (fun candidate => domain candidate /\ Not (candidate = value)) := by
  apply candidate_unsat_allows_removal cover
  intro feasible
  exact unsat ((search_feasible_iff_original sound cell value).mpr feasible)

theorem hinted_fast_probe_proves_original_exact
    {ctx : Context Cell Value} {state : AnalysisState Cell Value} {cell : Cell} {value : Value}
    (sound : AnalysisSound ctx state) (feasible : Feasible ctx cell value)
    (unsat : Not (Satisfiable (fun assignment =>
      searchContext ctx state assignment /\ Not (assignment cell = value)))) :
    Unique ctx cell /\ Complete ctx cell (Singleton value) := by
  have cover : Covers ctx cell (Singleton value) := hinted_exclusion_proves_original_coverage sound unsat
  obtain ⟨assignment, valid, _⟩ := feasible
  exact ⟨singleton_cover_is_unique cover, singleton_cover_is_complete ⟨assignment, valid⟩ cover⟩

theorem subset_unsat_proves_original_coverage
    {ctx subset : Context Cell Value} {cell : Cell} {domain : ValueSet Value}
    (weaker : forall assignment, ctx assignment -> subset assignment)
    (unsat : Not (Satisfiable (fun assignment => subset assignment /\ Not (domain (assignment cell))))) :
    Covers ctx cell domain := by
  have cover := exclusion_unsat_proves_coverage unsat
  intro assignment valid
  exact cover assignment (weaker assignment valid)

def underHypothesis (state : AnalysisState Cell Value) : AnalysisState Cell Value :=
  { state with
    knowledge := fun cell =>
      { domain := (state.knowledge cell).domain, samples := fun _ => False, complete := false }
    nonUnique := fun _ => false }

-- Egy szukebb, kielegitheto kontextusban a regi lefedes es egyertelmuseg megmarad,
-- de a regi megvalosithatosagi es teljessegi bizonyitekokat nem viszi at.
theorem hypothesis_analysis_sound {ctx hypothesis : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state)
    (sat : Satisfiable (fun assignment => ctx assignment /\ hypothesis assignment)) :
    AnalysisSound (fun assignment => ctx assignment /\ hypothesis assignment) (underHypothesis state) := by
  constructor
  · exact sat
  · intro cell
    constructor
    · intro domain recorded assignment valid
      exact (sound.values cell).coverage domain recorded assignment valid.1
    · intro _ impossible; exact False.elim impossible
    · intro impossible; cases impossible
  · intro cell marked left right leftValid rightValid
    exact sound.uniqueness cell marked left right leftValid.1 rightValid.1
  · intro _ impossible; cases impossible
  · intro assignment valid
    exact sound.search assignment valid.1

end Recovery
