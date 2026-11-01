import Recovery.Execution
import Recovery.Uniqueness

/-!
A tobbcellas recovery-allapotot es az eredmenyek beolvasztasat modellezi.
Az eredeti kontextus nem valtozik; a keresesi premisszaknak kovetkezniuk kell belole.
A fuggvenyalapu tarolok nem a Rust HashMap/HashSet implementaciojanak forditasai.
-/

namespace Recovery

variable {Cell Value : Type}

structure AnalysisState (Cell Value : Type) where
  knowledge : Cell -> Knowledge Value
  unique : Cell -> Bool
  nonUnique : Cell -> Bool
  searchFacts : Assignment Cell Value -> Prop
  solverCalls : Nat
  epoch : Nat

structure AnalysisSound (ctx : Context Cell Value) (state : AnalysisState Cell Value) : Prop where
  satisfiable : Satisfiable ctx
  values : forall cell, Sound ctx cell (state.knowledge cell)
  uniqueness : forall cell, state.unique cell = true -> Unique ctx cell
  ambiguity : forall cell, state.nonUnique cell = true -> NonUnique ctx cell
  search : forall assignment, ctx assignment -> state.searchFacts assignment

def initialAnalysis : AnalysisState Cell Value :=
  { knowledge := fun _ => initialKnowledge
    unique := fun _ => false
    nonUnique := fun _ => false
    searchFacts := fun _ => True
    solverCalls := 0
    epoch := 0 }

structure RecoveryEvidence (Cell Value : Type) where
  domains : Cell -> Option (ValueSet Value)
  samples : Cell -> ValueSet Value
  unique : Cell -> Bool
  nonUnique : Cell -> Bool

structure EvidenceSound (ctx : Context Cell Value) (result : RecoveryEvidence Cell Value) : Prop where
  coverage : forall cell domain, result.domains cell = some domain -> Covers ctx cell domain
  samples : forall cell, SamplesSound ctx cell (result.samples cell)
  uniqueness : forall cell, result.unique cell = true -> Unique ctx cell
  ambiguity : forall cell, result.nonUnique cell = true -> NonUnique ctx cell

def mergeEvidence (state : AnalysisState Cell Value) (result : RecoveryEvidence Cell Value) :
    AnalysisState Cell Value :=
  { state with
    knowledge := fun cell =>
      let sampled := rememberSamples (state.knowledge cell) (result.samples cell)
      match result.domains cell with
      | none => sampled
      | some domain => mergeDomain sampled domain
    unique := fun cell => state.unique cell || result.unique cell
    nonUnique := fun cell => state.nonUnique cell || result.nonUnique cell }

def modelEvidence (assignment : Assignment Cell Value) (selected : Cell -> Bool) : RecoveryEvidence Cell Value :=
  { domains := fun _ => none
    samples := fun cell => if selected cell then Singleton (assignment cell) else fun _ => False
    unique := fun _ => false
    nonUnique := fun _ => false }

def domainEvidence [DecidableEq Cell] (cell : Cell) (domain : ValueSet Value) : RecoveryEvidence Cell Value :=
  { domains := fun other => if other = cell then some domain else none
    samples := fun _ _ => False
    unique := fun _ => false
    nonUnique := fun _ => false }

def uniquenessEvidence [DecidableEq Cell] (cell : Cell) : RecoveryEvidence Cell Value :=
  { domains := fun _ => none
    samples := fun _ _ => False
    unique := fun other => decide (other = cell)
    nonUnique := fun _ => false }

def exactSearchFacts (state : AnalysisState Cell Value) (assignment : Assignment Cell Value) : Prop :=
  forall cell value, (state.knowledge cell).domain = some (Singleton value) -> assignment cell = value

def coveringSearchFacts (state : AnalysisState Cell Value) (selected : Cell -> Bool)
    (assignment : Assignment Cell Value) : Prop :=
  forall cell domain, selected cell = true -> (state.knowledge cell).domain = some domain -> domain (assignment cell)

def refreshSearchFacts (state : AnalysisState Cell Value) (selected : Cell -> Bool) : AnalysisState Cell Value :=
  { state with searchFacts := fun assignment =>
      exactSearchFacts state assignment /\ coveringSearchFacts state selected assignment }

def replaceKnowledge [DecidableEq Cell] (state : AnalysisState Cell Value) (cell : Cell)
    (knowledge : Knowledge Value) : AnalysisState Cell Value :=
  { state with knowledge := fun other => if other = cell then knowledge else state.knowledge other }

def certifyGlobalComplete [DecidableEq Cell] (state : AnalysisState Cell Value) (cell : Cell) :
    AnalysisState Cell Value := replaceKnowledge state cell (certifyComplete (state.knowledge cell))

def spendSolverCalls (state : AnalysisState Cell Value) (used : Nat) : AnalysisState Cell Value :=
  { state with solverCalls := state.solverCalls + used }

def advanceEpoch (state : AnalysisState Cell Value) : AnalysisState Cell Value :=
  { state with epoch := state.epoch + 1 }

def classifySamples (state : AnalysisState Cell Value) (selected : Cell -> Bool) : AnalysisState Cell Value :=
  { state with nonUnique := fun cell => state.nonUnique cell || selected cell }

def promoteExactValues (state : AnalysisState Cell Value) (exact : Cell -> Option Value) : AnalysisState Cell Value :=
  { state with unique := fun cell => state.unique cell || (exact cell).isSome }

theorem initial_analysis_sound {ctx : Context Cell Value} (sat : Satisfiable ctx) :
    AnalysisSound ctx (initialAnalysis : AnalysisState Cell Value) := by
  refine ⟨sat, fun cell => initial_knowledge_sound ctx cell, ?_, ?_, ?_⟩
  · intro _ impossible; cases impossible
  · intro _ impossible; cases impossible
  · intro _ _; trivial

theorem merge_evidence_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    {result : RecoveryEvidence Cell Value} (sound : AnalysisSound ctx state)
    (evidence : EvidenceSound ctx result) : AnalysisSound ctx (mergeEvidence state result) := by
  constructor
  · exact sound.satisfiable
  · intro cell
    have sampled := remember_samples_sound (sound.values cell) (evidence.samples cell)
    cases recorded : result.domains cell with
    | none => simpa only [mergeEvidence, recorded] using sampled
    | some domain =>
        have merged := merge_domain_sound sampled (evidence.coverage cell domain recorded)
        simpa only [mergeEvidence, recorded] using merged
  · intro cell marked
    rcases Bool.or_eq_true_iff.mp marked with old | fresh
    · exact sound.uniqueness cell old
    · exact evidence.uniqueness cell fresh
  · intro cell marked
    rcases Bool.or_eq_true_iff.mp marked with old | fresh
    · exact sound.ambiguity cell old
    · exact evidence.ambiguity cell fresh
  · exact sound.search

-- Egy teljes modell minden kivalasztott cellahoz szolgaltathat mintat, nem csak a kerdezetthez.
theorem model_evidence_sound {ctx : Context Cell Value} (assignment : Assignment Cell Value)
    (valid : ctx assignment) (selected : Cell -> Bool) :
    EvidenceSound ctx (modelEvidence assignment selected) := by
  constructor
  · intro _ _ impossible; cases impossible
  · intro cell value member
    simp only [modelEvidence] at member
    split at member
    · exact ⟨assignment, valid, member.symm⟩
    · exact False.elim member
  · intro _ impossible; cases impossible
  · intro _ impossible; cases impossible

theorem domain_evidence_sound [DecidableEq Cell] {ctx : Context Cell Value}
    {cell : Cell} {domain : ValueSet Value} (cover : Covers ctx cell domain) :
    EvidenceSound ctx (domainEvidence cell domain) := by
  constructor
  · intro other recordedDomain recorded
    simp only [domainEvidence] at recorded
    split at recorded
    · rename_i sameCell
      subst other
      cases recorded
      exact cover
    · cases recorded
  · intro _ _ impossible; exact False.elim impossible
  · intro _ impossible; cases impossible
  · intro _ impossible; cases impossible

theorem uniqueness_evidence_sound [DecidableEq Cell] {ctx : Context Cell Value}
    {cell : Cell} (unique : Unique ctx cell) : EvidenceSound ctx (uniquenessEvidence cell) := by
  constructor
  · intro _ _ impossible; cases impossible
  · intro _ _ impossible; exact False.elim impossible
  · intro other marked
    have same : other = cell := of_decide_eq_true marked
    subst other
    exact unique
  · intro _ impossible; cases impossible

theorem refresh_search_facts_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) (selected : Cell -> Bool) :
    AnalysisSound ctx (refreshSearchFacts state selected) := by
  refine ⟨sound.satisfiable, sound.values, sound.uniqueness, sound.ambiguity, ?_⟩
  intro assignment valid
  constructor
  · intro cell value recorded
    exact (sound.values cell).coverage (Singleton value) recorded assignment valid
  · intro cell domain _ recorded
    exact (sound.values cell).coverage domain recorded assignment valid

theorem replace_knowledge_sound [DecidableEq Cell] {ctx : Context Cell Value}
    {state : AnalysisState Cell Value} {cell : Cell} {knowledge : Knowledge Value}
    (sound : AnalysisSound ctx state) (cellSound : Sound ctx cell knowledge) :
    AnalysisSound ctx (replaceKnowledge state cell knowledge) := by
  refine ⟨sound.satisfiable, ?_, sound.uniqueness, sound.ambiguity, sound.search⟩
  intro other
  simp only [replaceKnowledge]
  split
  · rename_i same
    subst other
    exact cellSound
  · exact sound.values other

theorem certify_global_complete_sound [DecidableEq Cell] {ctx : Context Cell Value}
    {state : AnalysisState Cell Value} {cell : Cell} {domain : ValueSet Value}
    (sound : AnalysisSound ctx state) (recorded : (state.knowledge cell).domain = some domain)
    (witnessed : Included domain (state.knowledge cell).samples) :
    AnalysisSound ctx (certifyGlobalComplete state cell) := by
  exact replace_knowledge_sound sound
    (certify_complete_from_samples_sound (sound.values cell) recorded witnessed)

theorem certify_global_singleton_sound [DecidableEq Cell] {ctx : Context Cell Value}
    {state : AnalysisState Cell Value} {cell : Cell} {value : Value}
    (sound : AnalysisSound ctx state)
    (recorded : (state.knowledge cell).domain = some (Singleton value)) :
    AnalysisSound ctx (certifyGlobalComplete state cell) := by
  exact replace_knowledge_sound sound
    (certify_singleton_sound sound.satisfiable (sound.values cell) recorded)

theorem spend_solver_calls_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) (used : Nat) : AnalysisSound ctx (spendSolverCalls state used) := by
  exact ⟨sound.satisfiable, sound.values, sound.uniqueness, sound.ambiguity, sound.search⟩

theorem advance_epoch_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) : AnalysisSound ctx (advanceEpoch state) := by
  exact ⟨sound.satisfiable, sound.values, sound.uniqueness, sound.ambiguity, sound.search⟩

theorem classify_samples_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) (selected : Cell -> Bool)
    (witnessed : forall cell, selected cell = true -> exists a b,
      (state.knowledge cell).samples a /\ (state.knowledge cell).samples b /\ Not (a = b)) :
    AnalysisSound ctx (classifySamples state selected) := by
  refine ⟨sound.satisfiable, sound.values, sound.uniqueness, ?_, sound.search⟩
  intro cell marked
  rcases Bool.or_eq_true_iff.mp marked with old | fresh
  · exact sound.ambiguity cell old
  · obtain ⟨a, b, hasA, hasB, different⟩ := witnessed cell fresh
    exact two_samples_prove_non_unique (sound.values cell).samples hasA hasB different

theorem promote_exact_values_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) (exact : Cell -> Option Value)
    (recorded : forall cell value, exact cell = some value ->
      (state.knowledge cell).domain = some (Singleton value)) :
    AnalysisSound ctx (promoteExactValues state exact) := by
  refine ⟨sound.satisfiable, sound.values, ?_, sound.ambiguity, sound.search⟩
  intro cell marked
  rcases Bool.or_eq_true_iff.mp marked with old | fresh
  · exact sound.uniqueness cell old
  · cases result : exact cell with
    | none => simp only [result, Option.isSome_none] at fresh; cases fresh
    | some value =>
        exact singleton_cover_is_unique ((sound.values cell).coverage _ (recorded cell value result))

theorem reported_unique_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) {cell : Cell} (reported : state.unique cell = true) :
    Unique ctx cell := sound.uniqueness cell reported

theorem reported_non_unique_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) {cell : Cell} (reported : state.nonUnique cell = true) :
    NonUnique ctx cell := sound.ambiguity cell reported

theorem reported_domain_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) {cell : Cell} {domain : ValueSet Value}
    (recorded : (state.knowledge cell).domain = some domain) : Covers ctx cell domain :=
  (sound.values cell).coverage domain recorded

theorem reported_complete_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) {cell : Cell} (marked : (state.knowledge cell).complete = true) :
    exists domain, (state.knowledge cell).domain = some domain /\ Complete ctx cell domain :=
  (sound.values cell).completeness marked

theorem reported_exact_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) {cell : Cell} {value : Value}
    (recorded : (state.knowledge cell).domain = some (Singleton value)) :
    Unique ctx cell /\ Complete ctx cell (Singleton value) := by
  have cover := reported_domain_sound sound recorded
  exact ⟨singleton_cover_is_unique cover, singleton_cover_is_complete sound.satisfiable cover⟩

-- A Rust domain_is_complete singleton-agat az explicit flag nelkul is igazolja.
theorem effective_complete_sound {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) {cell : Cell}
    (marked : (state.knowledge cell).complete = true \/
      exists value, (state.knowledge cell).domain = some (Singleton value)) :
    exists domain, (state.knowledge cell).domain = some domain /\ Complete ctx cell domain := by
  rcases marked with explicit | singleton
  · exact reported_complete_sound sound explicit
  · obtain ⟨value, recorded⟩ := singleton
    exact ⟨Singleton value, recorded, (reported_exact_sound sound recorded).2⟩

theorem complete_domain_two_values_non_unique {ctx : Context Cell Value} {cell : Cell}
    {domain : ValueSet Value} {a b : Value} (complete : Complete ctx cell domain)
    (hasA : domain a) (hasB : domain b) (different : Not (a = b)) : NonUnique ctx cell := by
  exact ⟨a, b, (complete a).mp hasA, (complete b).mp hasB, different⟩

theorem reports_never_contradict {ctx : Context Cell Value} {state : AnalysisState Cell Value}
    (sound : AnalysisSound ctx state) (cell : Cell) :
    Not (state.unique cell = true /\ state.nonUnique cell = true) := by
  intro both
  exact non_unique_excludes_unique (sound.ambiguity cell both.2) (sound.uniqueness cell both.1)

end Recovery
