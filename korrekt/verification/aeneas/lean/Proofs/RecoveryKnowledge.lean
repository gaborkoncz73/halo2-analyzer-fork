import Proofs.RecoveryLoop

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

variable {Cell Value : Type}

abbrev Assignment (Cell Value : Type) := Cell -> Value
abbrev OriginalContext (Cell Value : Type) := Assignment Cell Value -> Prop

def Feasible (context : OriginalContext Cell Value) (cell : Cell) (value : Value) : Prop :=
  Exists fun assignment => context assignment /\ assignment cell = value

-- A konkret Rust-adapter projekciojanak helyessege kulon, meg nyitott bizonyitasi kotelezettseg.
structure RecoveryView (Cell Value : Type) where
  unique : Cell -> Prop
  nonUnique : Cell -> Prop
  domain : Cell -> Option (Value -> Prop)
  samples : Cell -> Value -> Prop
  complete : Cell -> Prop
  searchFacts : Assignment Cell Value -> Prop

structure SoundRecovery (context : OriginalContext Cell Value) (view : RecoveryView Cell Value) : Prop where
  satisfiable : Exists fun assignment => context assignment
  unique : forall cell, view.unique cell -> forall left right,
    context left -> context right -> left cell = right cell
  nonUnique : forall cell, view.nonUnique cell -> Exists fun left => Exists fun right =>
    context left /\ context right /\ left cell ≠ right cell
  covers : forall cell domain, view.domain cell = Option.some domain ->
    forall assignment, context assignment -> domain (assignment cell)
  samples : forall cell value, view.samples cell value -> Feasible context cell value
  complete : forall cell, view.complete cell -> Exists fun domain =>
    view.domain cell = Option.some domain /\ forall value, domain value <-> Feasible context cell value
  searchFacts : forall assignment, context assignment -> view.searchFacts assignment

variable {M Action Pending Stop Error : Type}

-- A forrasbol generalt fociklus a teljes K/Delta/W/E invarianssal is instancialhato.
theorem rust_recovery_preserves_knowledge
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (context : OriginalContext Cell Value) (view : M -> RecoveryView Cell Value)
    (stable ready : M -> Prop) (evidence : M -> Pending -> Prop) (stopped : Stop -> M -> Prop)
    (contracts : RecoveryContracts driver (fun state => SoundRecovery context (view state))
      stable ready evidence stopped)
    (state finalState : M) (status : Stop) (initial : SoundRecovery context (view state))
    (returned : recovery_loop.run_recovery driver state = .ok (.Ok (status, finalState))) :
    SoundRecovery context (view finalState) :=
  (rust_recovery_success_is_sound driver _ stable ready evidence stopped contracts
    state finalState status initial returned).1

-- Az exact domain nem puszta SAT-minta: minden eredeti megoldasban ugyanaz az ertek.
theorem sound_recovery_exact (context : OriginalContext Cell Value) (view : RecoveryView Cell Value)
    (sound : SoundRecovery context view) (cell : Cell) (value : Value)
    (exactDomain : view.domain cell = Option.some (fun candidate => candidate = value)) :
    Feasible context cell value /\ forall assignment, context assignment -> assignment cell = value := by
  have fixed : forall assignment, context assignment -> assignment cell = value :=
    sound.covers cell _ exactDomain
  obtain ⟨witness, valid⟩ := sound.satisfiable
  exact ⟨⟨witness, valid, fixed witness valid⟩, fixed⟩

-- A generalt fociklus vegallapotaban szereplo singleton minden eredeti megoldasban kotelezo.
theorem rust_recovery_exact_value_is_forced
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (context : OriginalContext Cell Value) (view : M -> RecoveryView Cell Value)
    (stable ready : M -> Prop) (evidence : M -> Pending -> Prop) (stopped : Stop -> M -> Prop)
    (contracts : RecoveryContracts driver (fun state => SoundRecovery context (view state))
      stable ready evidence stopped)
    (state finalState : M) (status : Stop) (initial : SoundRecovery context (view state))
    (returned : recovery_loop.run_recovery driver state = .ok (.Ok (status, finalState)))
    (cell : Cell) (value : Value)
    (exactDomain : (view finalState).domain cell = Option.some (fun candidate => candidate = value)) :
    Feasible context cell value /\ forall assignment, context assignment -> assignment cell = value := by
  exact sound_recovery_exact context (view finalState)
    (rust_recovery_preserves_knowledge driver context view stable ready evidence stopped
      contracts state finalState status initial returned) cell value exactDomain

theorem sound_recovery_never_both_unique_and_nonunique
    (context : OriginalContext Cell Value) (view : RecoveryView Cell Value)
    (sound : SoundRecovery context view) (cell : Cell) :
    Not (view.unique cell /\ view.nonUnique cell) := by
  rintro ⟨unique, nonUnique⟩
  obtain ⟨left, right, leftValid, rightValid, different⟩ := sound.nonUnique cell nonUnique
  exact different (sound.unique cell unique left right leftValid rightValid)

-- A valtozatlan eredeti Gamma kovetkezmenyei nem hoznak be onigazolo keresesi premisszakat.
theorem sound_recovery_hints_preserve_feasibility
    (context : OriginalContext Cell Value) (view : RecoveryView Cell Value)
    (sound : SoundRecovery context view) (assignment : Assignment Cell Value) :
    (context assignment /\ view.searchFacts assignment) <-> context assignment := by
  exact ⟨And.left, fun valid => ⟨valid, sound.searchFacts assignment valid⟩⟩

end SourceProof
