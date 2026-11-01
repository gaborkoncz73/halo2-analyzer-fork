import Recovery.Domains

/-!
Egy cella Delta-, W- es explicit teljessegi allapotanak absztrakt muveleteit modellezi.
A None hianyzo domaint jelent; a mintak onmagukban nem hoznak letre lefedest.
Az explicit complete jeloles nem azonos a Rust singleton-felismeresenek implementaciojaval.
-/

namespace Recovery

variable {Cell Value : Type}

structure Knowledge (Value : Type) where
  domain : Option (ValueSet Value)
  samples : ValueSet Value
  complete : Bool

def initialKnowledge : Knowledge Value :=
  { domain := none, samples := fun _ => False, complete := false }

structure Sound (ctx : Context Cell Value) (cell : Cell) (knowledge : Knowledge Value) : Prop where
  coverage : forall domain, knowledge.domain = some domain -> Covers ctx cell domain
  samples : SamplesSound ctx cell knowledge.samples
  completeness : knowledge.complete = true ->
    exists domain, knowledge.domain = some domain /\ Complete ctx cell domain

def rememberSamples (knowledge : Knowledge Value) (incoming : ValueSet Value) : Knowledge Value :=
  { knowledge with samples := Union knowledge.samples incoming }

-- A mar teljesnek jelolt domaint megorzi; egyebkent metszessel illeszti az uj lefedest.
def mergeDomain (knowledge : Knowledge Value) (incoming : ValueSet Value) : Knowledge Value :=
  if knowledge.complete then knowledge else
    { knowledge with domain := some (match knowledge.domain with
        | none => incoming
        | some existing => Intersection existing incoming) }

def certifyComplete (knowledge : Knowledge Value) : Knowledge Value :=
  { knowledge with complete := true }

theorem initial_knowledge_sound (ctx : Context Cell Value) (cell : Cell) :
    Sound ctx cell (initialKnowledge : Knowledge Value) := by
  constructor
  · intro domain recorded
    cases recorded
  · intro value impossible
    exact False.elim impossible
  · intro impossible
    cases impossible

theorem remember_samples_sound
    {ctx : Context Cell Value} {cell : Cell} {knowledge : Knowledge Value}
    {incoming : ValueSet Value} (sound : Sound ctx cell knowledge)
    (incomingSound : SamplesSound ctx cell incoming) :
    Sound ctx cell (rememberSamples knowledge incoming) := by
  exact ⟨sound.coverage, remember_samples_preserves_soundness sound.samples incomingSound,
    sound.completeness⟩

theorem merge_domain_sound
    {ctx : Context Cell Value} {cell : Cell} {knowledge : Knowledge Value}
    {incoming : ValueSet Value} (sound : Sound ctx cell knowledge)
    (incomingCover : Covers ctx cell incoming) :
    Sound ctx cell (mergeDomain knowledge incoming) := by
  unfold mergeDomain
  split
  · exact sound
  · rename_i notComplete
    constructor
    · intro domain recorded
      cases recorded
      cases original : knowledge.domain with
      | none => exact incomingCover
      | some existing =>
          exact intersect_preserves_coverage (sound.coverage existing original) incomingCover
    · exact sound.samples
    · intro impossible
      exact False.elim (notComplete impossible)

theorem certify_complete_from_samples_sound
    {ctx : Context Cell Value} {cell : Cell} {knowledge : Knowledge Value}
    {domain : ValueSet Value} (sound : Sound ctx cell knowledge)
    (recorded : knowledge.domain = some domain)
    (allWitnessed : Included domain knowledge.samples) :
    Sound ctx cell (certifyComplete knowledge) := by
  constructor
  · exact sound.coverage
  · exact sound.samples
  · intro _
    exact ⟨domain, recorded,
      complete_from_samples (sound.coverage domain recorded) sound.samples allWitnessed⟩

theorem certify_singleton_sound
    {ctx : Context Cell Value} {cell : Cell} {knowledge : Knowledge Value} {value : Value}
    (sat : Satisfiable ctx) (sound : Sound ctx cell knowledge)
    (recorded : knowledge.domain = some (Singleton value)) :
    Sound ctx cell (certifyComplete knowledge) := by
  constructor
  · exact sound.coverage
  · exact sound.samples
  · intro _
    exact ⟨Singleton value, recorded,
      singleton_cover_is_complete sat (sound.coverage (Singleton value) recorded)⟩

end Recovery
