import Recovery.GlobalKnowledge

/-!
A teljes tobbcellas allapot modelljere bizonyit reszleges helyesseget.
A konkret szabalyok es solvervalaszok EvidenceSound szerzodeset a hivo igazolja.
A tetel nem allitja a Rust-kinyeres huseget, a terminalast vagy az utemezo optimalitasat.
-/

namespace Recovery

variable {Cell Value : Type}

inductive AnalysisStep [DecidableEq Cell] (ctx : Context Cell Value) :
    AnalysisState Cell Value -> AnalysisState Cell Value -> Prop where
  | merge (state : AnalysisState Cell Value) (result : RecoveryEvidence Cell Value)
      (evidence : EvidenceSound ctx result) : AnalysisStep ctx state (mergeEvidence state result)
  | certify (state : AnalysisState Cell Value) (cell : Cell) (domain : ValueSet Value)
      (recorded : (state.knowledge cell).domain = some domain)
      (witnessed : Included domain (state.knowledge cell).samples) :
      AnalysisStep ctx state (certifyGlobalComplete state cell)
  | singleton (state : AnalysisState Cell Value) (cell : Cell) (value : Value)
      (recorded : (state.knowledge cell).domain = some (Singleton value)) :
      AnalysisStep ctx state (certifyGlobalComplete state cell)
  | refresh (state : AnalysisState Cell Value) (selected : Cell -> Bool) :
      AnalysisStep ctx state (refreshSearchFacts state selected)
  | samples (state : AnalysisState Cell Value) (selected : Cell -> Bool)
      (witnessed : forall cell, selected cell = true -> exists a b,
        (state.knowledge cell).samples a /\ (state.knowledge cell).samples b /\ Not (a = b)) :
      AnalysisStep ctx state (classifySamples state selected)
  | exact (state : AnalysisState Cell Value) (values : Cell -> Option Value)
      (recorded : forall cell value, values cell = some value ->
        (state.knowledge cell).domain = some (Singleton value)) :
      AnalysisStep ctx state (promoteExactValues state values)
  | spend (state : AnalysisState Cell Value) (used : Nat) :
      AnalysisStep ctx state (spendSolverCalls state used)
  | progress (state : AnalysisState Cell Value) : AnalysisStep ctx state (advanceEpoch state)
  | unchanged (state : AnalysisState Cell Value) : AnalysisStep ctx state state

theorem analysis_step_preserves_soundness [DecidableEq Cell]
    {ctx : Context Cell Value} {before after : AnalysisState Cell Value}
    (sound : AnalysisSound ctx before) (step : AnalysisStep ctx before after) : AnalysisSound ctx after := by
  cases step with
  | merge _ evidence => exact merge_evidence_sound sound evidence
  | certify _ _ recorded witnessed => exact certify_global_complete_sound sound recorded witnessed
  | singleton _ _ recorded => exact certify_global_singleton_sound sound recorded
  | refresh selected => exact refresh_search_facts_sound sound selected
  | samples selected witnessed => exact classify_samples_sound sound selected witnessed
  | exact values recorded => exact promote_exact_values_sound sound values recorded
  | spend used => exact spend_solver_calls_sound sound used
  | progress => exact advance_epoch_sound sound
  | unchanged => exact sound

inductive AnalysisExecution [DecidableEq Cell] (ctx : Context Cell Value) :
    AnalysisState Cell Value -> AnalysisState Cell Value -> Prop where
  | refl (state : AnalysisState Cell Value) : AnalysisExecution ctx state state
  | next {first middle last : AnalysisState Cell Value}
      (earlier : AnalysisExecution ctx first middle) (step : AnalysisStep ctx middle last) :
      AnalysisExecution ctx first last

theorem analysis_execution_preserves_soundness [DecidableEq Cell]
    {ctx : Context Cell Value} {before after : AnalysisState Cell Value}
    (sound : AnalysisSound ctx before) (execution : AnalysisExecution ctx before after) :
    AnalysisSound ctx after := by
  induction execution with
  | refl => exact sound
  | next _ step prefixSound => exact analysis_step_preserves_soundness prefixSound step

theorem global_recovery_sound [DecidableEq Cell]
    {ctx : Context Cell Value} {finalState : AnalysisState Cell Value}
    (sat : Satisfiable ctx) (execution : AnalysisExecution ctx initialAnalysis finalState) :
    AnalysisSound ctx finalState := by
  exact analysis_execution_preserves_soundness (initial_analysis_sound sat) execution

-- A strategia tetszoleges megengedett lepessorozatot valaszthat; ettol a reszleges helyesseg nem valtozik.
theorem global_recovery_reports_sound [DecidableEq Cell]
    {ctx : Context Cell Value} {finalState : AnalysisState Cell Value}
    (sat : Satisfiable ctx) (execution : AnalysisExecution ctx initialAnalysis finalState) :
    (forall cell, finalState.unique cell = true -> Unique ctx cell) /\
    (forall cell, finalState.nonUnique cell = true -> NonUnique ctx cell) /\
    (forall cell domain, (finalState.knowledge cell).domain = some domain -> Covers ctx cell domain) /\
    (forall cell, (finalState.knowledge cell).complete = true ->
      exists domain, (finalState.knowledge cell).domain = some domain /\ Complete ctx cell domain) /\
    (forall cell value, (finalState.knowledge cell).domain = some (Singleton value) ->
      Unique ctx cell /\ Complete ctx cell (Singleton value)) /\
    (forall assignment, ctx assignment -> finalState.searchFacts assignment) := by
  have sound := global_recovery_sound sat execution
  exact ⟨sound.uniqueness, sound.ambiguity, fun cell => (sound.values cell).coverage,
    fun cell => (sound.values cell).completeness,
    fun _ _ recorded => reported_exact_sound sound recorded, sound.search⟩

theorem analysis_step_calls_monotone [DecidableEq Cell]
    {ctx : Context Cell Value} {before after : AnalysisState Cell Value}
    (step : AnalysisStep ctx before after) : before.solverCalls <= after.solverCalls := by
  cases step <;> simp [mergeEvidence, certifyGlobalComplete, replaceKnowledge, refreshSearchFacts,
    classifySamples, promoteExactValues, spendSolverCalls, advanceEpoch]

theorem execution_calls_monotone [DecidableEq Cell]
    {ctx : Context Cell Value} {before after : AnalysisState Cell Value}
    (execution : AnalysisExecution ctx before after) : before.solverCalls <= after.solverCalls := by
  induction execution with
  | refl => exact Nat.le_refl _
  | next _ step accumulated => exact Nat.le_trans accumulated (analysis_step_calls_monotone step)

theorem progress_preserves_spent_calls (state : AnalysisState Cell Value) :
    (advanceEpoch state).solverCalls = state.solverCalls := rfl

end Recovery
