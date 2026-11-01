import Proofs.EngineFixpoint
import Proofs.RecoveryKnowledge

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
A generalt `run_recovery` konkret gepe. A szemantikai beolvasztas a generalt `recovery_core`-bol jon.
A solver, az utemezo es a szabalymotor orakulum: minden bizonyithatatlan feltetele itt, nevvel szerepel.
Az orakulum tetszoleges lehet, amig a szerzodeset teljesiti, igy a tetel minden solverre ervenyes.
-/

abbrev MarkSet := std.collections.hash.set.HashSet cells.CellId std.hash.random.RandomState alloc.alloc.Global

structure CoreState (Aux : Type) where
  facts : knowledge.UcpFacts
  values : domains.UcpValueFacts
  evidence : recovery_core.RecoveryEvidence
  marks : MarkSet
  aux : Aux

structure RecoveryOracle (Aux Action Stop Error : Type) where
  engine : CoreState Aux -> Result (core.result.Result (knowledge.UcpFacts × domains.UcpValueFacts × Aux) Error)
  refresh : CoreState Aux -> Result (core.result.Result Aux Error)
  select : CoreState Aux -> Result (core.result.Result (Aux × recovery_loop.Selection Action Stop) Error)
  query : CoreState Aux -> Action -> Result (core.result.Result (Aux × recovery_core.EstablishedEvidence) Error)
  admin : CoreState Aux -> recovery_core.EstablishedEvidence -> Result (core.result.Result Aux Error)
  sampleError : recovery_core.UnsupportedSample -> Error
  certificationError : recovery_core.CertificationError -> Error

variable {Aux Action Stop Error : Type}

/-- Az eles `RecoveryDriver` szemantikai magja, a Rust-adapter sorrendjeben. -/
noncomputable def coreMachine (p : Nat) (oracle : RecoveryOracle Aux Action Stop Error) :
    recovery_loop.RecoveryMachine (CoreState Aux) Action recovery_core.EstablishedEvidence Stop Error where
  propagate := fun state => do
    let answer ← oracle.engine state
    match answer with
    | .Err error => .ok (.Err error)
    | .Ok (facts, values, aux) =>
        let (certified, nextValues) ←
          recovery_core.RecoveryEvidence.impl.try_certify_complete_domains state.evidence facts values (p : Int)
        match certified with
        | .Err error => .ok (.Err (oracle.certificationError error))
        | .Ok again => .ok (.Ok ({ state with facts := facts, values := nextValues, aux := aux }, again))
  refresh := fun state => do
    let answer ← oracle.refresh state
    match answer with
    | .Err error => .ok (.Err error)
    | .Ok aux => .ok (.Ok { state with aux := aux })
  select := fun state => do
    let answer ← oracle.select state
    match answer with
    | .Err error => .ok (.Err error)
    | .Ok (aux, selection) => .ok (.Ok ({ state with aux := aux }, selection))
  query := fun state action => do
    let answer ← oracle.query state action
    match answer with
    | .Err error => .ok (.Err error)
    | .Ok (aux, established) => .ok (.Ok ({ state with aux := aux }, established))
  merge := fun state established => do
    let (merged, evidence, facts, values, marks) ←
      recovery_core.merge_established_evidence state.evidence state.facts state.values state.marks
        established (p : Int)
    match merged with
    | .Err error => .ok (.Err (oracle.sampleError error))
    | .Ok changed =>
        let middle : CoreState Aux := ⟨facts, values, evidence, marks, state.aux⟩
        let administered ← oracle.admin middle established
        match administered with
        | .Err error => .ok (.Err error)
        | .Ok aux =>
            let (finished, nextValues, nextMarks) ←
              recovery_core.finish_merge evidence facts values marks (p : Int)
            match finished with
            | .Err error => .ok (.Err (oracle.certificationError error))
            | .Ok added =>
                .ok (.Ok (⟨facts, nextValues, evidence, nextMarks, aux⟩, changed || added))

section Contracts

variable {F : Type} [Field F] (p : Nat) [CharP F p]
  (surjective : Function.Surjective (fun value : Int => (value : F)))

def StateSound (context : OriginalContext cells.CellId F) (state : CoreState Aux) : Prop :=
  CoreSound p context state.facts state.values state.evidence state.marks

/-- Az orakulum kotelezettsegei. Ezek a tetel explicit bizalmi hatarat alkotjak. -/
structure OracleContracts (oracle : RecoveryOracle Aux Action Stop Error) (constants : Constants F)
    (context : OriginalContext cells.CellId F) (ready : Aux -> Prop) (stopped : Stop -> Aux -> Prop) : Prop where
  engine : ∀ state, StateSound p context state ->
    WP.dspec (oracle.engine state) (RustOutcome fun (facts, values, _) =>
      EngineExecution p constants context (state.facts, state.values) (facts, values))
  refresh : ∀ state, StateSound p context state ->
    WP.dspec (oracle.refresh state) (RustOutcome fun aux => ready aux)
  select : ∀ state, StateSound p context state -> ready state.aux ->
    WP.dspec (oracle.select state) (RustOutcome fun (aux, selection) => ready aux ∧ match selection with
      | .Run _ => True
      | .Stop status => stopped status aux)
  query : ∀ state action, StateSound p context state -> ready state.aux ->
    WP.dspec (oracle.query state action) (RustOutcome fun (aux, established) =>
      ready aux ∧ EvidenceClaim p context state.evidence.feasible established)
  admin : ∀ state established, ready state.aux ->
    WP.dspec (oracle.admin state established) (RustOutcome fun aux => ready aux)

@[simp] theorem state_sound_aux (context : OriginalContext cells.CellId F) (state : CoreState Aux) (aux : Aux) :
    StateSound p context { state with aux := aux } = StateSound p context state := rfl

include surjective in
-- A szerzodesek a konkret gepre teljesulnek: ez korabban nyitott kotelezettseg volt.
theorem core_machine_contracts (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (oracle : RecoveryOracle Aux Action Stop Error) (constants : Constants F)
    (context : OriginalContext cells.CellId F) (ready : Aux -> Prop) (stopped : Stop -> Aux -> Prop)
    (contracts : OracleContracts p oracle constants context ready stopped) :
    RecoveryContracts (coreMachine p oracle) (StateSound p context) (fun _ => True)
      (fun state : CoreState Aux => ready state.aux)
      (fun state established => EvidenceClaim p context state.evidence.feasible established)
      (fun status state => stopped status state.aux) where
  propagate := by
    intro state sound
    apply WP.dspec_bind (contracts.engine state sound)
    intro answer valid
    cases answer with
    | Err error => simp [RustOutcome]
    | Ok result =>
        obtain ⟨facts, values, aux⟩ := result
        have knowledgeSound : KnowledgeSound p context facts values :=
          engine_execution_sound p surjective positive constants context sound.satisfiable sound.knowledge valid
        apply WP.dspec_bind (rust_certify_domains_sound p positive bits context facts values state.evidence
          knowledgeSound sound.samples sound.capacity)
        rintro ⟨certified, nextValues⟩ post
        cases certified with
        | Err error => simp [RustOutcome]
        | Ok again =>
            have nextSound : KnowledgeSound p context facts nextValues := by simpa [CertifyPost] using post
            exact (WP.dspec_ok _).mpr (And.intro
              (⟨sound.satisfiable, nextSound, sound.samples, sound.capacity, sound.nonUnique⟩ :
                CoreSound p context facts nextValues state.evidence state.marks) (fun _ => trivial))
  refresh := by
    intro state sound _
    apply WP.dspec_bind (contracts.refresh state sound)
    intro answer valid
    cases answer with
    | Err error => simp [RustOutcome]
    | Ok aux => simpa [RustOutcome] using And.intro sound valid
  select := by
    intro state sound prepared
    apply WP.dspec_bind (contracts.select state sound prepared)
    intro answer valid
    cases answer with
    | Err error => simp [RustOutcome]
    | Ok result =>
        obtain ⟨aux, selection⟩ := result
        obtain ⟨nextReady, stoppedValid⟩ := valid
        cases selection with
        | Run action => simpa [RustOutcome] using And.intro sound nextReady
        | Stop status => simpa [RustOutcome] using And.intro sound (And.intro nextReady stoppedValid)
  query := by
    intro state action sound prepared
    apply WP.dspec_bind (contracts.query state action sound prepared)
    intro answer valid
    cases answer with
    | Err error => simp [RustOutcome]
    | Ok result =>
        obtain ⟨aux, established⟩ := result
        simpa [RustOutcome] using And.intro sound valid
  merge := by
    intro state established sound prepared claim
    apply WP.dspec_bind (rust_merge_evidence_sound p surjective positive bits context state.facts state.values
      state.evidence state.marks sound established claim)
    rintro ⟨merged, evidence, facts, values, marks⟩ post
    cases merged with
    | Err error => simp [RustOutcome]
    | Ok changed =>
        have middleSound : CoreSound p context facts values evidence marks := by simpa [MergePost] using post
        apply WP.dspec_bind (contracts.admin ⟨facts, values, evidence, marks, state.aux⟩ established prepared)
        intro administered valid
        cases administered with
        | Err error => simp [RustOutcome]
        | Ok aux =>
            apply WP.dspec_bind (rust_finish_merge_sound p positive bits context facts values evidence marks middleSound)
            rintro ⟨finished, nextValues, nextMarks⟩ finishPost
            cases finished with
            | Err error => simp [RustOutcome]
            | Ok added =>
                have finalSound : CoreSound p context facts nextValues evidence nextMarks := by
                  simpa [FinishPost] using finishPost
                exact (WP.dspec_ok _).mpr (And.intro finalSound (fun _ => valid))

/-- A konkret allapot projekcioja a szemantikai riportnezetre. -/
def coreView (searchFacts : Aux -> Assignment cells.CellId F -> Prop) (state : CoreState Aux) :
    RecoveryView cells.CellId F where
  unique := fun cell => state.facts.unique_cells cell = true
  nonUnique := fun cell => state.marks cell = true
  domain := fun cell => (state.values.domains cell).map (fun domain value => DomainContains fieldValue domain value)
  samples := fun cell value => ∃ entry ∈ state.evidence.feasible, entry.1 = cell ∧
    ∃ sample ∈ entry.2, fieldValue sample = value
  complete := fun cell => completeDomainTag state.values cell = true
  searchFacts := searchFacts state.aux

-- A projekcio helyessege: a konkret invariansbol a riport szemantikai allitasai kovetkeznek.
theorem core_view_sound (context : OriginalContext cells.CellId F)
    (searchFacts : Aux -> Assignment cells.CellId F -> Prop) (state : CoreState Aux)
    (sound : StateSound p context state)
    (hints : ∀ assignment, context assignment -> searchFacts state.aux assignment) :
    SoundRecovery context (coreView searchFacts state) where
  satisfiable := sound.satisfiable
  unique := fun cell marked => sound.knowledge.known cell marked
  nonUnique := fun cell marked => sound.nonUnique cell marked
  covers := by
    intro cell domain recorded assignment valid
    simp only [coreView, Option.map_eq_some_iff] at recorded
    obtain ⟨stored, entry, rfl⟩ := recorded
    exact sound.knowledge.covers cell stored entry assignment valid
  samples := by
    rintro cell value ⟨entry, member, rfl, sample, inside, rfl⟩
    exact (sound.samples entry member sample inside).1
  complete := by
    intro cell complete
    obtain ⟨domain, recorded, exact⟩ := rust_complete_domain_is_exact context fieldValue state.values cell
      sound.satisfiable sound.knowledge.covers sound.knowledge.flags
      ((rust_complete_domain_matches state.values cell).trans (congrArg Result.ok complete))
    refine ⟨fun value => DomainContains fieldValue domain value, ?_, exact⟩
    simp [coreView, recorded]
  searchFacts := hints

include surjective in
/-- **A visszaallitasi eljaras fo tetele.** A generalt fociklus es a generalt beolvasztasi mag
sikeres lefutasa utan a teljes riportnezet helyes az eredeti, publikus adatokkal rogzitett kontextusban. -/
theorem rust_private_recovery_sound (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (oracle : RecoveryOracle Aux Action Stop Error) (constants : Constants F)
    (context : OriginalContext cells.CellId F) (searchFacts : Aux -> Assignment cells.CellId F -> Prop)
    (stopped : Stop -> Aux -> Prop)
    (contracts : OracleContracts p oracle constants context
      (fun aux => ∀ assignment, context assignment -> searchFacts aux assignment) stopped)
    (initial final : CoreState Aux) (status : Stop) (start : StateSound p context initial)
    (returned : recovery_loop.run_recovery (coreMachine p oracle) initial = .ok (.Ok (status, final))) :
    StateSound p context final ∧ SoundRecovery context (coreView searchFacts final) ∧ stopped status final.aux := by
  have checked := rust_recovery_success_is_sound (coreMachine p oracle) (StateSound p context) (fun _ => True)
    (fun state : CoreState Aux => ∀ assignment, context assignment -> searchFacts state.aux assignment)
    (fun state established => EvidenceClaim p context state.evidence.feasible established)
    (fun status state => stopped status state.aux)
    (core_machine_contracts p surjective positive bits oracle constants context _ stopped contracts)
    initial final status start returned
  exact ⟨checked.1, core_view_sound p context searchFacts final checked.1 checked.2.1, checked.2.2⟩

include surjective in
/-- A riportban `Recovered` statuszt ado pontos ertek minden, a publikus adatokkal osszeegyeztetheto tanuban a titkos ertek. -/
theorem rust_recovered_value_is_forced (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (oracle : RecoveryOracle Aux Action Stop Error) (constants : Constants F)
    (context : OriginalContext cells.CellId F) (searchFacts : Aux -> Assignment cells.CellId F -> Prop)
    (stopped : Stop -> Aux -> Prop)
    (contracts : OracleContracts p oracle constants context
      (fun aux => ∀ assignment, context assignment -> searchFacts aux assignment) stopped)
    (initial final : CoreState Aux) (status : Stop) (start : StateSound p context initial)
    (returned : recovery_loop.run_recovery (coreMachine p oracle) initial = .ok (.Ok (status, final)))
    (cell : cells.CellId) (value : Int)
    (known : domains.UcpValueFacts.impl.known_value final.values cell = .ok (some value)) :
    Feasible context cell (fieldValue value) ∧
      ∀ assignment, context assignment -> assignment cell = fieldValue value := by
  obtain ⟨sound, _, _⟩ := rust_private_recovery_sound p surjective positive bits oracle constants context
    searchFacts stopped contracts initial final status start returned
  exact rust_known_value_is_forced context fieldValue final.values cell value sound.satisfiable
    sound.knowledge.covers known

/-- A kezdeti ures allapot minden kielegitheto kontextusban helyes. -/
theorem empty_state_sound (context : OriginalContext cells.CellId F)
    (satisfiable : ∃ assignment, context assignment) (aux : Aux) :
    StateSound p context
      (⟨⟨fun _ => false⟩, ⟨fun _ => none, fun _ => false⟩, ⟨[]⟩, fun _ => false, aux⟩ : CoreState Aux) := by
  refine ⟨satisfiable, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro _ impossible; cases impossible
  · intro _ _ impossible; cases impossible
  · intro _ _ impossible; cases impossible
  · intro _ _ impossible; cases impossible
  · intro _ _ impossible; cases impossible
  · intro _ impossible; cases impossible
  · intro _ _ impossible; cases impossible
  · intro _ impossible; cases impossible
  · simp [Usize.max]
  · intro _ impossible; cases impossible
  · intro _ impossible; cases impossible

end Contracts

end SourceProof
