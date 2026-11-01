import Recovery.GlobalExecution
import Recovery.ConditionalReasoning
import Recovery.PropagationView
import Recovery.Cache
import Recovery.PropagationChecks

/-!
A tobbcellas vegrehajtas pozitiv peldait es a context/cache hatarait ellenorzi.
A teljes modellek mintai megvalosithatosagi bizonyitekok, nem fuggetlen cellaertekek.
-/

namespace Recovery.Checks

abbrev oppositeContext (assignment : Assignment Bool Bool) : Prop :=
  Bool.xor (assignment false) (assignment true) = true

def firstModel : Assignment Bool Bool := id
def secondModel : Assignment Bool Bool := Bool.not

def sharedModelState : AnalysisState Bool Bool :=
  mergeEvidence (mergeEvidence initialAnalysis (modelEvidence firstModel (fun _ => true)))
    (modelEvidence secondModel (fun _ => true))

def classifiedModelState : AnalysisState Bool Bool :=
  classifySamples sharedModelState (fun _ => true)

theorem shared_models_execution :
    AnalysisExecution oppositeContext initialAnalysis sharedModelState := by
  exact .next (.next (.refl _) (.merge _ _ (model_evidence_sound firstModel (by decide) _)))
    (.merge _ _ (model_evidence_sound secondModel (by decide) _))

theorem both_model_samples_recorded (cell : Bool) :
    (sharedModelState.knowledge cell).samples (firstModel cell) /\
    (sharedModelState.knowledge cell).samples (secondModel cell) /\
    Not (firstModel cell = secondModel cell) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sharedModelState, mergeEvidence, modelEvidence, rememberSamples, initialAnalysis,
      initialKnowledge, Union, Singleton]
  · simp [sharedModelState, mergeEvidence, modelEvidence, rememberSamples, initialAnalysis,
      initialKnowledge, Union, Singleton]
  · cases cell <;> decide

theorem classified_models_execution :
    AnalysisExecution oppositeContext initialAnalysis classifiedModelState := by
  apply AnalysisExecution.next shared_models_execution
  apply AnalysisStep.samples
  intro cell _
  have samples := both_model_samples_recorded cell
  exact ⟨firstModel cell, secondModel cell, samples⟩

theorem shared_model_recovery_reports_non_unique (cell : Bool) : NonUnique oppositeContext cell := by
  have sound := global_recovery_sound ⟨firstModel, by decide⟩ classified_models_execution
  apply reported_non_unique_sound sound
  simp [classifiedModelState, classifySamples]

example (cell : Bool) : (classifiedModelState.knowledge cell).domain = none := by
  rfl

example : (spendSolverCalls classifiedModelState 2).solverCalls = 2 := by rfl

-- Ket cella egy-egy megvalosithato erteke nem jelent egy kozos megvalosithato ertekparost.
example : Feasible oppositeContext false false /\ Feasible oppositeContext true false /\
    Not (exists assignment, oppositeContext assignment /\
      assignment false = false /\ assignment true = false) := by
  refine ⟨⟨firstModel, by decide, rfl⟩, ⟨secondModel, by decide, rfl⟩, ?_⟩
  intro joint
  obtain ⟨assignment, valid, first, second⟩ := joint
  rw [oppositeContext, first, second] at valid
  cases valid

-- Uj publikus premissza mellett a regi ketminta-bizonyitek mar nem viheto at.
example : AnalysisSound (fun assignment => oppositeContext assignment /\ assignment false = false)
    (underHypothesis classifiedModelState) := by
  apply hypothesis_analysis_sound
  · exact global_recovery_sound ⟨firstModel, by decide⟩ classified_models_execution
  · exact ⟨firstModel, by decide⟩

example (cell : Bool) : (underHypothesis classifiedModelState).nonUnique cell = false := rfl

abbrev sevenContext (assignment : Assignment Unit Nat) : Prop := assignment () = 7

def uniqueOnlyState : AnalysisState Unit Nat :=
  mergeEvidence initialAnalysis (uniquenessEvidence ())

theorem unique_only_state_sound : AnalysisSound sevenContext uniqueOnlyState := by
  apply merge_evidence_sound (initial_analysis_sound (ctx := sevenContext) ⟨fun _ => 7, rfl⟩)
  apply uniqueness_evidence_sound
  intro left right leftValid rightValid
  exact leftValid.trans rightValid.symm

-- Puszta K-tagsagbol nem general E-be egy onkenyes konkret erteket.
example : exactSearchFacts uniqueOnlyState (fun _ => 99) := by
  intro cell value impossible
  cases impossible

-- Gyengitett subsetben talalt modell nem teljes Γ-modell, akkor sem, ha Γ kielegitheto.
example : Satisfiable (fun assignment : Assignment Unit Nat => assignment () = 0) /\
    Satisfiable (fun assignment : Assignment Unit Nat => True /\ assignment () = 1) /\
    Not (Feasible (fun assignment : Assignment Unit Nat => assignment () = 0) () 1) := by
  refine ⟨⟨fun _ => 0, rfl⟩, ⟨fun _ => 1, True.intro, rfl⟩, ?_⟩
  intro feasible
  obtain ⟨assignment, zero, one⟩ := feasible
  have impossible : (0 : Nat) = 1 := zero.symm.trans one
  cases impossible

-- Egy onkenyes extra hint onigazolo UNSAT-ot okozhatna; ezert szukseges a hint entailmentje.
example : Not (Satisfiable (fun assignment : Assignment Unit Nat =>
      (True /\ assignment () = 0) /\ Not (assignment () = 0))) /\
    Not (Covers (fun (_ : Assignment Unit Nat) => True) () (Singleton 0)) := by
  constructor
  · intro satisfiable
    obtain ⟨assignment, constraints⟩ := satisfiable
    exact constraints.2 constraints.1.2
  · intro cover
    have impossible : (1 : Nat) = 0 := cover (fun _ => 1) True.intro
    cases impossible

-- Minden ag egyertelmusege onmagaban nem eleg: az agak kulonbozo erteket adhatnak.
example :
    (forall value, Unique (Recovery.branchContext (fun (_ : Assignment Unit Bool) => True) () value) ()) /\
    NonUnique (fun (_ : Assignment Unit Bool) => True) () := by
  constructor
  · intro value left right leftValid rightValid
    exact leftValid.2.trans rightValid.2.symm
  · exact ⟨false, true, ⟨fun _ => false, True.intro, rfl⟩,
      ⟨fun _ => true, True.intro, rfl⟩, by decide⟩

def cacheFixture : DomainCacheEntry Unit Bool :=
  { signature := domainSignature (.var ()) (fun _ => some [false, true]) (fun _ => false)
    result := some [false, true] }

example : reuseDomainCache (.var ()) (fun _ => some [false, true]) (fun _ => false) cacheFixture =
    some (some [false, true]) := by decide

example : reuseDomainCache (.var ()) (fun _ => some [false]) (fun _ => false) cacheFixture = none := by decide

-- A cache a complete flag valtozasat is eszreveszi, nem csak a domainet.
example : reuseDomainCache (.var ()) (fun _ => some [false, true]) (fun _ => true) cacheFixture = none := by decide

example : reuseDomainCache (.var ()) (fun _ => (none : Option (List Bool))) (fun _ => false)
    { signature := domainSignature (.var ()) (fun _ => none) (fun _ => false), result := none } =
      some none := by decide

-- A kifejezestol fuggetlen cella megvaltozasa nem okoz hamis cache-eredmenyt.
example : reuseDomainCache (.var false)
    (fun cell => if cell then some [true] else some [false]) (fun _ => false)
    { signature := domainSignature (.var false) (fun _ => some [false]) (fun _ => false),
      result := some [false] } = some (some [false]) := by decide

end Recovery.Checks
