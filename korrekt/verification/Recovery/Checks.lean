import Recovery.Execution
import Recovery.SolverSteps

/-!
Kis ellenpeldakkal ellenorzi a bizonyitasi feltetelek szuksegesseget.
Ezek a peldak nem helyettesitik az altalanos tetelek bizonyitasat.
-/

namespace Recovery

-- Egy megvalosithato minta nem bizonyit lefedest egy szabad valtozora.
example :
    SamplesSound (fun (_ : Assignment Unit Nat) => True) () (Singleton 0) /\
    Not (Covers (fun (_ : Assignment Unit Nat) => True) () (Singleton 0)) := by
  constructor
  · exact model_sample_is_sound (fun _ => 0) True.intro
  · intro cover
    have impossible : (1 : Nat) = 0 := cover (fun _ => 1) True.intro
    cases impossible

-- Kielegithetetlen kontextusban az egyelemes lefedes sem ad teljes domaint.
example :
    Covers (fun (_ : Assignment Unit Nat) => False) () (Singleton 0) /\
    Not (Complete (fun (_ : Assignment Unit Nat) => False) () (Singleton 0)) := by
  constructor
  · intro _ impossible
    exact False.elim impossible
  · intro complete
    obtain ⟨_, impossible, _⟩ := (complete 0).mp rfl
    exact impossible

-- Az uj felteves melletti megoldashalmaz szukebb lehet; a regi teljesseg nem viheto at.
example :
    Complete (fun (_ : Assignment Unit Nat) => True) () (fun _ => True) /\
    Not (Complete (fun assignment : Assignment Unit Nat => assignment () = 0)
      () (fun _ => True)) := by
  constructor
  · intro value
    exact ⟨fun _ => ⟨fun _ => value, True.intro, rfl⟩, fun _ => True.intro⟩
  · intro complete
    obtain ⟨assignment, zero, one⟩ := (complete 1).mp True.intro
    have impossible : (0 : Nat) = 1 := zero.symm.trans one
    cases impossible

end Recovery
