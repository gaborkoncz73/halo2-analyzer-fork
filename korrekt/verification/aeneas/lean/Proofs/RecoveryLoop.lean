import Proofs.Semantics

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000

-- A Rust Err megengedett leallas; nem jelenti sem a recovery sikeret, sem a titkossagot.
def RustOutcome {T E : Type} (post : T -> Prop) : core.result.Result T E -> Prop
  | .Ok value => post value
  | .Err _ => True

def LoopOutcome {State Output : Type} (invariant : State -> Prop) (post : Output -> Prop) :
    ControlFlow State Output -> Prop
  | .cont next => invariant next
  | .done output => post output

@[dspec_admissible] theorem guarded_dspec_admissible {State Output : Type}
    (guard : Prop) (state : State) (post : Output -> Prop) :
    Lean.Order.admissible (fun f : State -> Result Output => guard -> WP.dspec (f state) post) := by
  apply Lean.Order.admissible_pi
  intro _
  exact WP.dspec_func_admissible state post

-- Az Aeneas reszleges specifikacioja a divergalast megengedi, a panikot nem.
theorem generated_loop_preserves {State Output : Type}
    (body : State -> Result (ControlFlow State Output))
    (invariant : State -> Prop) (post : Output -> Prop)
    (stepSound : forall state, invariant state ->
      WP.dspec (body state) (LoopOutcome invariant post))
    (state : State) (initial : invariant state) :
    WP.dspec (loop body state) post := by
  revert state
  dspec_induction loop
  intro nextLoop ih state initial
  apply WP.dspec_bind (stepSound state initial)
  intro control valid
  cases control with
  | cont next => exact ih next valid
  | done output => simpa [LoopOutcome] using valid

variable {M Action Pending Stop Error : Type}

-- Ezek a konkret adapterre meg bizonyitando muveleti szerzodesek, nem axiomak.
structure RecoveryContracts (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (invariant stable ready : M -> Prop) (evidence : M -> Pending -> Prop)
    (stopped : Stop -> M -> Prop) : Prop where
  propagate : forall state, invariant state ->
    WP.dspec (driver.propagate state) (RustOutcome fun (next, again) =>
      invariant next /\ (again = false -> stable next))
  refresh : forall state, invariant state -> stable state ->
    WP.dspec (driver.refresh state) (RustOutcome fun next => invariant next /\ ready next)
  select : forall state, invariant state -> ready state ->
    WP.dspec (driver.select state) (RustOutcome fun (next, selection) =>
      invariant next /\ ready next /\ match selection with
        | .Run _ => True
        | .Stop status => stopped status next)
  query : forall state action, invariant state -> ready state ->
    WP.dspec (driver.query state action) (RustOutcome fun (next, pending) =>
      invariant next /\ ready next /\ evidence next pending)
  merge : forall state pending, invariant state -> ready state -> evidence state pending ->
    WP.dspec (driver.merge state pending) (RustOutcome fun (next, changed) =>
      invariant next /\ (changed = false -> ready next))

theorem propagation_body_preserves
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (invariant stable ready : M -> Prop) (evidence : M -> Pending -> Prop)
    (stopped : Stop -> M -> Prop)
    (contracts : RecoveryContracts driver invariant stable ready evidence stopped)
    (state : M) (initial : invariant state) :
    WP.dspec (recovery_loop.propagate_until_stable_loop.body driver state)
      (LoopOutcome invariant (RustOutcome fun next => invariant next /\ ready next)) := by
  unfold recovery_loop.propagate_until_stable_loop.body
  apply WP.dspec_bind (contracts.propagate state initial)
  intro answer valid
  cases answer with
  | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        LoopOutcome, RustOutcome, core.convert.FromSame.from]
  | Ok pair =>
      obtain ⟨next, again⟩ := pair
      obtain ⟨nextValid, nextStable⟩ := valid
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      cases again with
      | true => simpa [LoopOutcome] using nextValid
      | false =>
          apply WP.dspec_bind (contracts.refresh next nextValid (nextStable rfl))
          intro refreshed refreshedValid
          simpa [LoopOutcome] using refreshedValid

theorem rust_propagation_returns_ready
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (invariant stable ready : M -> Prop) (evidence : M -> Pending -> Prop)
    (stopped : Stop -> M -> Prop)
    (contracts : RecoveryContracts driver invariant stable ready evidence stopped)
    (state : M) (initial : invariant state) :
    WP.dspec (recovery_loop.propagate_until_stable driver state)
      (RustOutcome fun next => invariant next /\ ready next) := by
  unfold recovery_loop.propagate_until_stable recovery_loop.propagate_until_stable_loop
  exact generated_loop_preserves _ invariant _
    (propagation_body_preserves driver invariant stable ready evidence stopped contracts) state initial

def RecoveryLoopInvariant (invariant ready : M -> Prop) (state : M × Bool) : Prop :=
  invariant state.1 /\ (state.2 = false -> ready state.1)

def RecoveryOutput (invariant ready : M -> Prop) (stopped : Stop -> M -> Prop) :
    core.result.Result (Stop × M) Error -> Prop :=
  RustOutcome fun (status, state) => invariant state /\ ready state /\ stopped status state

theorem selection_body_preserves
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (invariant stable ready : M -> Prop) (evidence : M -> Pending -> Prop)
    (stopped : Stop -> M -> Prop)
    (contracts : RecoveryContracts driver invariant stable ready evidence stopped)
    (state : M) (initial : invariant state) (prepared : ready state) :
    WP.dspec (recovery_loop.run_recovery_loop.body driver state false)
      (LoopOutcome (RecoveryLoopInvariant invariant ready) (RecoveryOutput invariant ready stopped)) := by
  unfold recovery_loop.run_recovery_loop.body
  simp only [Bool.false_eq_true, ite_false]
  apply WP.dspec_bind (contracts.select state initial prepared)
  intro selected selectedValid
  cases selected with
  | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        LoopOutcome, RecoveryOutput, RustOutcome, core.convert.FromSame.from]
  | Ok pair =>
      obtain ⟨next, selection⟩ := pair
      obtain ⟨nextValid, nextReady, selectionValid⟩ := selectedValid
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      cases selection with
      | Stop status =>
          simpa [LoopOutcome, RecoveryOutput, RustOutcome] using
            (And.intro nextValid (And.intro nextReady selectionValid))
      | Run action =>
          apply WP.dspec_bind (contracts.query next action nextValid nextReady)
          intro queried queryValid
          cases queried with
          | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                LoopOutcome, RecoveryOutput, RustOutcome, core.convert.FromSame.from]
          | Ok pair =>
              obtain ⟨queriedState, pending⟩ := pair
              obtain ⟨queriedValid, queriedReady, pendingSound⟩ := queryValid
              simp only [bind_ok]
              apply WP.dspec_bind (contracts.merge queriedState pending queriedValid queriedReady pendingSound)
              intro merged mergedValid
              cases merged with
              | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    LoopOutcome, RecoveryOutput, RustOutcome, core.convert.FromSame.from]
              | Ok pair =>
                  obtain ⟨mergedState, changed⟩ := pair
                  simpa [core.result.Result.Insts.CoreOpsTry.branch, LoopOutcome, RecoveryLoopInvariant, RustOutcome]
                    using mergedValid

theorem recovery_body_split
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error) (state : M) :
    recovery_loop.run_recovery_loop.body driver state true = (do
      let answer <- recovery_loop.propagate_until_stable driver state
      match answer with
      | .Ok next => recovery_loop.run_recovery_loop.body driver next false
      | .Err error => .ok (.done (.Err error))) := by
  unfold recovery_loop.run_recovery_loop.body
  simp only [ite_true, Bool.false_eq_true, ite_false]
  congr 1
  funext answer
  cases answer <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]

-- A fo tetel a tenyleges Rust-fociklusbol generalt fuggvenyre vonatkozik.
theorem rust_recovery_loop_preserves
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (invariant stable ready : M -> Prop) (evidence : M -> Pending -> Prop)
    (stopped : Stop -> M -> Prop)
    (contracts : RecoveryContracts driver invariant stable ready evidence stopped)
    (state : M) (initial : invariant state) :
    WP.dspec (recovery_loop.run_recovery driver state) (RecoveryOutput invariant ready stopped) := by
  unfold recovery_loop.run_recovery recovery_loop.run_recovery_loop
  apply generated_loop_preserves _ (RecoveryLoopInvariant invariant ready)
  · intro current currentValid
    obtain ⟨currentState, needed⟩ := current
    obtain ⟨currentSound, currentReady⟩ := currentValid
    cases needed with
    | false =>
        exact selection_body_preserves driver invariant stable ready evidence stopped
          contracts currentState currentSound (currentReady rfl)
    | true =>
        dsimp only
        rw [recovery_body_split]
        apply WP.dspec_bind (rust_propagation_returns_ready driver invariant stable ready evidence stopped
          contracts currentState currentSound)
        intro propagated propagatedValid
        cases propagated with
        | Err error => simp [LoopOutcome, RecoveryOutput, RustOutcome]
        | Ok next =>
            exact selection_body_preserves driver invariant stable ready evidence stopped
              contracts next propagatedValid.1 propagatedValid.2
  · exact ⟨initial, by simp⟩

theorem rust_recovery_success_is_sound
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (invariant stable ready : M -> Prop) (evidence : M -> Pending -> Prop)
    (stopped : Stop -> M -> Prop)
    (contracts : RecoveryContracts driver invariant stable ready evidence stopped)
    (state finalState : M) (status : Stop) (initial : invariant state)
    (returned : recovery_loop.run_recovery driver state = .ok (.Ok (status, finalState))) :
    invariant finalState /\ ready finalState /\ stopped status finalState := by
  have sound := rust_recovery_loop_preserves driver invariant stable ready evidence stopped contracts state initial
  rw [returned] at sound
  simpa [RecoveryOutput, RustOutcome] using sound

end SourceProof
