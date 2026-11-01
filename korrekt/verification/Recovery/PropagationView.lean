import Recovery.GlobalKnowledge

/-!
A globalis fixpont szemantikai bemenetet kuloniti el a mintaktol es metadataktol.
A fixpont-atviteli tetel csak a megadott K/Delta-nezeten keresztul mukodo
propagatorra vonatkozik; a tenyleges Rust engine ilyen finomitasat nem bizonyitja.
A cache ettol fuggetlenul a teljessegi flaget is ellenorzi a sajat szignaturajaban.
-/

namespace Recovery

variable {Cell Value : Type}

abbrev PropagationInput (Cell Value : Type) :=
  (Cell -> Bool) × (Cell -> Option (ValueSet Value))

def propagationInput (state : AnalysisState Cell Value) : PropagationInput Cell Value :=
  (state.unique, fun cell => (state.knowledge cell).domain)

def SamePropagationInput (left right : AnalysisState Cell Value) : Prop :=
  (forall cell, left.unique cell = right.unique cell) /\
  (forall cell, (left.knowledge cell).domain = (right.knowledge cell).domain)

theorem same_propagation_input_eq {left right : AnalysisState Cell Value}
    (same : SamePropagationInput left right) : propagationInput left = propagationInput right := by
  exact Prod.ext (funext same.1) (funext same.2)

theorem model_samples_preserve_propagation_input (state : AnalysisState Cell Value)
    (assignment : Assignment Cell Value) (selected : Cell -> Bool) :
    SamePropagationInput state (mergeEvidence state (modelEvidence assignment selected)) := by
  constructor <;> intro cell <;> simp [mergeEvidence, modelEvidence, rememberSamples]

theorem completeness_preserves_propagation_input [DecidableEq Cell]
    (state : AnalysisState Cell Value) (cell : Cell) :
    SamePropagationInput state (certifyGlobalComplete state cell) := by
  constructor
  · intro _; rfl
  · intro other
    simp only [certifyGlobalComplete, replaceKnowledge]
    split
    · rename_i same
      subst other
      rfl
    · rfl

theorem sample_classification_preserves_propagation_input (state : AnalysisState Cell Value)
    (selected : Cell -> Bool) : SamePropagationInput state (classifySamples state selected) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem refresh_preserves_propagation_input (state : AnalysisState Cell Value)
    (selected : Cell -> Bool) : SamePropagationInput state (refreshSearchFacts state selected) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem progress_preserves_propagation_input (state : AnalysisState Cell Value) :
    SamePropagationInput state (advanceEpoch state) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem unchanged_input_preserves_fixpoint {before after : AnalysisState Cell Value}
    (propagate : PropagationInput Cell Value -> PropagationInput Cell Value)
    (same : SamePropagationInput before after)
    (fixed : propagate (propagationInput before) = propagationInput before) :
    propagate (propagationInput after) = propagationInput after := by
  rw [<- same_propagation_input_eq same]
  exact fixed

end Recovery
