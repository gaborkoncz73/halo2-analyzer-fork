import Recovery.Knowledge

/-!
A modellezett lepesek tetszoleges veges sorozatara bizonyit invariansmegorzest.
Az uj domainek lefedese es az uj mintak megvalosithatosaga bizonyitasi kotelezettseg,
nem a teljes Rust-pipeline vagy az osszes UCP-szabaly igazolasa.
-/

namespace Recovery

variable {Cell Value : Type}

inductive Step (ctx : Context Cell Value) (cell : Cell) :
    Knowledge Value -> Knowledge Value -> Prop where
  | remember (knowledge : Knowledge Value) (incoming : ValueSet Value)
      (evidence : SamplesSound ctx cell incoming) :
      Step ctx cell knowledge (rememberSamples knowledge incoming)
  | merge (knowledge : Knowledge Value) (incoming : ValueSet Value)
      (evidence : Covers ctx cell incoming) :
      Step ctx cell knowledge (mergeDomain knowledge incoming)
  | certify (knowledge : Knowledge Value) (domain : ValueSet Value)
      (recorded : knowledge.domain = some domain)
      (allWitnessed : Included domain knowledge.samples) :
      Step ctx cell knowledge (certifyComplete knowledge)
  | singleton (knowledge : Knowledge Value) (value : Value)
      (sat : Satisfiable ctx)
      (recorded : knowledge.domain = some (Singleton value)) :
      Step ctx cell knowledge (certifyComplete knowledge)
  | unchanged (knowledge : Knowledge Value) : Step ctx cell knowledge knowledge

theorem step_preserves_soundness
    {ctx : Context Cell Value} {cell : Cell} {before after : Knowledge Value}
    (sound : Sound ctx cell before) (step : Step ctx cell before after) :
    Sound ctx cell after := by
  cases step with
  | remember _ evidence => exact remember_samples_sound sound evidence
  | merge _ evidence => exact merge_domain_sound sound evidence
  | certify _ recorded allWitnessed =>
      exact certify_complete_from_samples_sound sound recorded allWitnessed
  | singleton _ sat recorded => exact certify_singleton_sound sat sound recorded
  | unchanged => exact sound

inductive Execution (ctx : Context Cell Value) (cell : Cell) :
    Knowledge Value -> Knowledge Value -> Prop where
  | refl (knowledge : Knowledge Value) : Execution ctx cell knowledge knowledge
  | next {first middle last : Knowledge Value}
      (earlier : Execution ctx cell first middle) (step : Step ctx cell middle last) :
      Execution ctx cell first last

theorem execution_preserves_soundness
    {ctx : Context Cell Value} {cell : Cell} {before after : Knowledge Value}
    (sound : Sound ctx cell before) (execution : Execution ctx cell before after) :
    Sound ctx cell after := by
  induction execution with
  | refl => exact sound
  | next _ step prefixSound => exact step_preserves_soundness prefixSound step

theorem recovery_from_empty_is_sound
    {ctx : Context Cell Value} {cell : Cell} {after : Knowledge Value}
    (execution : Execution ctx cell initialKnowledge after) : Sound ctx cell after := by
  exact execution_preserves_soundness (initial_knowledge_sound ctx cell) execution

end Recovery
