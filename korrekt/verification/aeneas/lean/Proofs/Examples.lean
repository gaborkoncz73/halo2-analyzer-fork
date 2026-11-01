import Proofs.PrivateRecovery
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
Nem-uressegi peldak: a fo tetelek premisszai kielegithetok, a generalt kod tenylegesen lefut.
A halozat: x + r = 1, ahol r publikus es 0; a keresesi orakulum egy fast probe eredmenyet adja vissza.
A test `ZMod 5`, a privat cella `x`, a publikus cella `r`.
-/

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev secretCell : cells.CellId := firstCell
abbrev publicCell : cells.CellId := secondCell

def exampleCircuit : PublicCircuit (ZMod 5) :=
  { constraints := fun assignment => assignment secretCell + assignment publicCell = 1
    isPublic := fun cell => cell = publicCell }

def exampleObserved : cells.CellId -> ZMod 5 := fun _ => 0

abbrev exampleContext := Consistent exampleCircuit exampleObserved

theorem example_forced (assignment : Assignment cells.CellId (ZMod 5)) (valid : exampleContext assignment) :
    assignment secretCell = fieldValue 1 := by
  obtain ⟨constraint, observedValue⟩ := valid
  have publicZero := observedValue publicCell rfl
  simp only [exampleCircuit, exampleObserved] at constraint publicZero
  simp only [publicZero, add_zero] at constraint
  simpa [fieldValue] using constraint

noncomputable def exampleWitness : Assignment cells.CellId (ZMod 5) := by
  classical
  exact fun cell => if cell = secretCell then 1 else 0

theorem cells_differ : secondCell ≠ firstCell := by
  simp [firstCell, secondCell]

theorem example_witness_valid : exampleContext exampleWitness := by
  classical
  have atSecret : exampleWitness secretCell = 1 := by simp [exampleWitness]
  have atPublic : exampleWitness publicCell = 0 := by
    simp [exampleWitness, secretCell, publicCell, cells_differ]
  refine ⟨?_, ?_⟩
  · simp [exampleCircuit, atSecret, atPublic]
  · intro cell same
    change cell = publicCell at same
    subst cell
    simpa [exampleObserved] using atPublic

noncomputable def exampleEvidence : recovery_core.EstablishedEvidence :=
  { cell := secretCell, samples := alloc.vec.Vec.new Int, model_samples := [],
    domain := some (.Exact 1), unique := true, non_unique := false }

noncomputable def exampleOracle : RecoveryOracle Bool Unit Unit Unit where
  engine := fun state => .ok (.Ok (state.facts, state.values, state.aux))
  refresh := fun state => .ok (.Ok state.aux)
  select := fun state => .ok (.Ok (state.aux, if state.aux then .Stop () else .Run ()))
  query := fun _ _ => .ok (.Ok (true, exampleEvidence))
  admin := fun state _ => .ok (.Ok state.aux)
  sampleError := fun _ => ()
  certificationError := fun _ => ()

def exampleConstants : Constants (ZMod 5) := ⟨fun _ => 1, fun _ => 0, fun _ => one_ne_zero⟩

theorem example_surjective : Function.Surjective (fun value : Int => (value : ZMod 5)) :=
  ZMod.intCast_surjective

theorem example_positive : 1 < ((5 : Nat) : Int) := by norm_num

theorem example_bits : ((5 : Nat) : Int).natAbs.size ≤ 4096 := by
  have : ((5 : Nat) : Int).natAbs.size = 3 := by decide
  omega

theorem example_canonical_one : centeredRepresentative 1 ((5 : Nat) : Int) = 1 := by decide

theorem example_claim (entries : EvidenceMap) (room : Headroom entries 0) :
    EvidenceClaim 5 exampleContext entries exampleEvidence := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sample member
    simp [exampleEvidence, alloc.vec.Vec.from_val] at member
  · intro entry impossible
    cases impossible
  · intro domain same
    simp only [exampleEvidence, Option.some.injEq] at same
    subst domain
    exact ⟨fun assignment valid => example_forced assignment valid,
      by intro value member; simp only [DomainMembers, Finset.mem_singleton] at member; subst member; exact example_canonical_one,
      by simp [DomainMembers],
      by intro value member; simp only [DomainMembers, Finset.mem_singleton] at member; subst member; decide⟩
  · intro _ left right leftValid rightValid
    exact (example_forced left leftValid).trans (example_forced right rightValid).symm
  · intro impossible
    cases impossible
  · simpa [exampleEvidence, alloc.vec.Vec.from_val, modelLoad] using room

/-- Az orakulum-szerzodesek kielegithetok: a fo tetel premisszaja nem ures. -/
theorem example_contracts :
    OracleContracts 5 exampleOracle exampleConstants exampleContext
      (fun _ => ∀ assignment, exampleContext assignment -> True) (fun _ _ => True) where
  engine := by
    intro state _
    simp only [exampleOracle, WP.dspec_ok, RustOutcome]
    exact EngineExecution.refl _
  refresh := by
    intro state _
    simp [exampleOracle, RustOutcome]
  select := by
    intro state _ _
    simp only [exampleOracle, WP.dspec_ok, RustOutcome]
    cases state.aux <;> simp
  query := by
    intro state _ sound _
    simp only [exampleOracle, WP.dspec_ok, RustOutcome]
    exact ⟨fun _ _ => trivial, example_claim _ sound.capacity⟩
  admin := by
    intro state _ _
    simp [exampleOracle, RustOutcome]

noncomputable def exampleInitial : CoreState Bool :=
  ⟨⟨fun _ => false⟩, ⟨fun _ => none, fun _ => false⟩, ⟨[]⟩, fun _ => false, false⟩

theorem example_initial_sound : StateSound 5 exampleContext exampleInitial :=
  empty_state_sound 5 exampleContext ⟨exampleWitness, example_witness_valid⟩ false

theorem empty_vec_next (iter : alloc.vec.into_iter.IntoIter Int) (empty : iter.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next iter = .ok (none, iter) := by
  simp only [alloc.vec.into_iter.IteratorIntoIter.next]
  split
  · rfl
  · simp_all

theorem remember_loop_empty (iter : alloc.vec.into_iter.IntoIter Int) (empty : iter.val = [])
    (evidence : recovery_core.RecoveryEvidence) (cell : cells.CellId) (modulus : Int) :
    recovery_core.RecoveryEvidence.impl.try_remember_list_loop iter evidence cell modulus =
      .ok (.Ok (), evidence) := by
  unfold recovery_core.RecoveryEvidence.impl.try_remember_list_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [uncurry_apply_pair]
  unfold recovery_core.RecoveryEvidence.impl.try_remember_list_loop.body
  rw [empty_vec_next iter empty]
  simp

theorem example_remember_empty (evidence : recovery_core.RecoveryEvidence) (modulus : Int) :
    recovery_core.RecoveryEvidence.impl.try_remember_list evidence secretCell (alloc.vec.Vec.new Int) modulus =
      .ok (.Ok (), evidence) := by
  unfold recovery_core.RecoveryEvidence.impl.try_remember_list
  have started : alloc.vec.IntoIteratorVec.into_iter (alloc.vec.Vec.new Int) =
      Result.ok (show alloc.vec.into_iter.IntoIter Int from alloc.vec.Vec.new Int) := rfl
  rw [started, bind_ok]
  exact remember_loop_empty _ (alloc.vec.Vec.from_val _ _) evidence secretCell modulus

theorem example_remember_model (evidence : recovery_core.RecoveryEvidence) (modulus : Int) :
    recovery_core.RecoveryEvidence.impl.try_remember_model evidence [] modulus = .ok (.Ok (), evidence) := by
  unfold recovery_core.RecoveryEvidence.impl.try_remember_model
    SharedABTreeMap.Insts.CoreIterTraitsCollectIntoIteratorPairSharedAKSharedAVIter.into_iter
    recovery_core.RecoveryEvidence.impl.try_remember_model_loop
  simp only [bind_ok]
  rw [Aeneas.Std.loop.eq_def]
  simp [recovery_core.RecoveryEvidence.impl.try_remember_model_loop.body,
    alloc.collections.btree.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next]

theorem example_certify_empty (facts : knowledge.UcpFacts) (values : domains.UcpValueFacts) (modulus : Int) :
    recovery_core.RecoveryEvidence.impl.try_certify_complete_domains ⟨[]⟩ facts values modulus =
      .ok (.Ok false, values) := by
  unfold recovery_core.RecoveryEvidence.impl.try_certify_complete_domains
    SharedABTreeMap.Insts.CoreIterTraitsCollectIntoIteratorPairSharedAKSharedAVIter.into_iter
    recovery_core.RecoveryEvidence.impl.try_certify_complete_domains_loop
  simp only [bind_ok]
  rw [Aeneas.Std.loop.eq_def]
  simp [recovery_core.RecoveryEvidence.impl.try_certify_complete_domains_loop.body,
    alloc.collections.btree.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next]

theorem example_record_empty (marks : MarkSet) :
    recovery_core.RecoveryEvidence.impl.record_non_unique_cells ⟨[]⟩ marks = .ok marks := by
  unfold recovery_core.RecoveryEvidence.impl.record_non_unique_cells
    SharedABTreeMap.Insts.CoreIterTraitsCollectIntoIteratorPairSharedAKSharedAVIter.into_iter
    recovery_core.RecoveryEvidence.impl.record_non_unique_cells_loop
  simp only [bind_ok]
  rw [Aeneas.Std.loop.eq_def]
  simp [recovery_core.RecoveryEvidence.impl.record_non_unique_cells_loop.body,
    alloc.collections.btree.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next]

noncomputable def exampleLearned : domains.UcpValueFacts := by
  classical
  exact ⟨Function.update (fun _ => none) secretCell (some (.Exact 1)), fun _ => false⟩

theorem example_mark_domain :
    domains.UcpValueFacts.impl.mark_domain ⟨fun _ => none, fun _ => false⟩ secretCell (.Exact 1) =
      .ok (true, exampleLearned) := by
  classical
  unfold domains.UcpValueFacts.impl.mark_domain
  rw [rust_complete_domain_matches]
  have bounded : domains.bounded_value 1 = .ok (some 1) :=
    rust_bounded_value_accepts_supported 1 (by decide)
  have lookup := rust_domain_lookup ⟨fun _ => none, fun _ => false⟩ secretCell
  simp only at lookup
  simp [completeDomainTag, bounded, lookup, std.collections.hash.map.HashMap.impl.insert, exampleLearned]

noncomputable def exampleFinal : CoreState Bool :=
  ⟨insertedFacts ⟨fun _ => false⟩ secretCell, exampleLearned, ⟨[]⟩, fun _ => false, true⟩

theorem example_known_final :
    domains.UcpValueFacts.impl.known_value exampleFinal.values secretCell = .ok (some 1) := by
  classical
  rw [rust_known_value_matches]
  simp [exampleFinal, exampleLearned, domainExactValue]

theorem example_merge :
    (coreMachine 5 exampleOracle).merge { exampleInitial with aux := true } exampleEvidence =
      .ok (.Ok (exampleFinal, true)) := by
  classical
  simp only [coreMachine, recovery_core.merge_established_evidence, exampleEvidence, exampleInitial,
    example_remember_empty, example_remember_model, bind_ok, uncurry_apply_pair,
    core.result.Result.Insts.CoreOpsTry.branch, cell_clone_correct, rust_mark_unique_matches_insert,
    reduceIte, example_mark_domain]
  simp [exampleOracle, recovery_core.finish_merge, example_certify_empty, example_record_empty,
    core.result.Result.Insts.CoreOpsTry.branch, exampleFinal]

theorem example_stable (state : CoreState Bool) (empty : state.evidence = ⟨[]⟩) :
    recovery_loop.propagate_until_stable (coreMachine 5 exampleOracle) state = .ok (.Ok state) := by
  obtain ⟨facts, values, evidence, marks, aux⟩ := state
  cases empty
  unfold recovery_loop.propagate_until_stable recovery_loop.propagate_until_stable_loop
  rw [Aeneas.Std.loop.eq_def]
  simp [recovery_loop.propagate_until_stable_loop.body, coreMachine, exampleOracle, example_certify_empty,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem example_first_round :
    recovery_loop.run_recovery_loop.body (coreMachine 5 exampleOracle) exampleInitial true =
      .ok (.cont (exampleFinal, true)) := by
  rw [recovery_body_split, example_stable exampleInitial rfl, bind_ok]
  unfold recovery_loop.run_recovery_loop.body
  simp only [Bool.false_eq_true, ite_false]
  have selected : (coreMachine 5 exampleOracle).select exampleInitial =
      .ok (.Ok ({ exampleInitial with aux := false }, .Run ())) := by
    simp [coreMachine, exampleOracle, exampleInitial]
  have queried : (coreMachine 5 exampleOracle).query { exampleInitial with aux := false } () =
      .ok (.Ok ({ exampleInitial with aux := true }, exampleEvidence)) := by
    simp [coreMachine, exampleOracle, exampleInitial]
  simp only [selected, queried, example_merge, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    uncurry_apply_pair]

theorem example_second_round :
    recovery_loop.run_recovery_loop.body (coreMachine 5 exampleOracle) exampleFinal true =
      .ok (.done (.Ok ((), exampleFinal))) := by
  rw [recovery_body_split, example_stable exampleFinal rfl, bind_ok]
  unfold recovery_loop.run_recovery_loop.body
  simp only [Bool.false_eq_true, ite_false]
  have selected : (coreMachine 5 exampleOracle).select exampleFinal =
      .ok (.Ok (exampleFinal, .Stop ())) := by
    simp [coreMachine, exampleOracle, exampleFinal]
  simp only [selected, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]

/-- A generalt fociklus es a generalt beolvasztas tenyleges lefutasa a pelda halozaton. -/
theorem example_run :
    recovery_loop.run_recovery (coreMachine 5 exampleOracle) exampleInitial = .ok (.Ok ((), exampleFinal)) := by
  unfold recovery_loop.run_recovery recovery_loop.run_recovery_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [uncurry_apply_pair, example_first_round, bind_ok]
  rw [Aeneas.Std.loop.eq_def]
  simp only [uncurry_apply_pair, example_second_round, bind_ok]

/-- Vegpontok kozotti pelda: a fo tetel a tenyleges futasra alkalmazva a valodi titkot adja vissza. -/
theorem example_recovers_secret :
    exampleWitness secretCell = fieldValue 1 ∧ Determined exampleCircuit exampleObserved secretCell :=
  rust_recovery_reveals_secret 5 example_surjective example_positive example_bits exampleCircuit exampleObserved
    exampleOracle exampleConstants (fun _ _ => True) (fun _ _ => True)
    (by simpa using example_contracts) exampleInitial exampleFinal () example_initial_sound example_run
    secretCell 1 example_known_final exampleWitness example_witness_valid

noncomputable def exampleAlternative : Assignment cells.CellId (ZMod 5) := by
  classical
  exact fun cell => if cell = secretCell then 0 else 1

theorem example_alternative_valid : exampleCircuit.constraints exampleAlternative := by
  classical
  simp [exampleCircuit, exampleAlternative, secretCell, publicCell, cells_differ]

/-- A pelda valoban szivarog: a publikus adat kizar egy, a halozat szerint lehetseges erteket. -/
theorem example_is_overconstrained : Overconstrained exampleCircuit exampleObserved secretCell := by
  classical
  apply rust_recovery_proves_overconstrained 5 example_surjective example_positive example_bits exampleCircuit
    exampleObserved exampleOracle exampleConstants (fun _ _ => True) (fun _ _ => True)
    (by simpa using example_contracts) exampleInitial exampleFinal () example_initial_sound example_run
    secretCell 1 example_known_final exampleAlternative example_alternative_valid
  simp [exampleAlternative, fieldValue]

end SourceProof
