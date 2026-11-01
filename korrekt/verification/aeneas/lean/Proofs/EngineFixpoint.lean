import Proofs.RecoveryCore

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
A QED²-erveles adaptacioja a Halo2-elemzore. A fixpontszamitas minden lepese vagy kinyert kodbol
kovetkezik (Assign, singleton), vagy explicit bizonyitekot hoz (domain- es egyertelmusegi szabalyok).
Az erveles az ertekadasok tetszoleges kontextusara ervenyes, ezert ugyanaz a tetel adja a
bemenet->kimenet egyertelmuseget es a publikus adat->privat ertek visszaallitast is.
-/

section Engine

variable {F : Type} [Field F] (p : Nat) [CharP F p]

/-- A K/Delta-fixpont egy lepese. A `facts` es `values` a kinyert Rust-allapot. -/
inductive EngineStep (constants : Constants F) (context : OriginalContext cells.CellId F) :
    knowledge.UcpFacts × domains.UcpValueFacts -> knowledge.UcpFacts × domains.UcpValueFacts -> Prop where
  /-- A kinyert Assign-elemzes es a kinyert K-frissites. -/
  | assign (facts next : knowledge.UcpFacts) (values : domains.UcpValueFacts)
      (expression : expressions.UcpExpr) (cell : cells.CellId) (changed : Bool)
      (equation : ∀ assignment, context assignment -> evaluate constants assignment expression [] = 0)
      (inferred : rules.infer_assigned_cell_from_zero_equation_with_modulus expression facts (p : Int) =
        .ok (Option.some cell))
      (inserted : knowledge.UcpFacts.impl.mark_unique facts cell = .ok (changed, next)) :
      EngineStep constants context (facts, values) (next, values)
  /-- Lefedo domain beolvasztasa a kinyert mark_domain fuggvennyel. A bizonyitekot a szabaly adja. -/
  | learn (facts : knowledge.UcpFacts) (values next : domains.UcpValueFacts)
      (cell : cells.CellId) (domain : domains.UcpValueDomain) (changed : Bool)
      (claim : DomainClaim p context cell domain)
      (merged : domains.UcpValueFacts.impl.mark_domain values cell domain = .ok (changed, next)) :
      EngineStep constants context (facts, values) (facts, next)
  /-- Az egyelemu lefedo domainbol egyertelmuseg kovetkezik. -/
  | singleton (facts next : knowledge.UcpFacts) (values : domains.UcpValueFacts)
      (cell : cells.CellId) (value : Int) (changed : Bool)
      (known : domains.UcpValueFacts.impl.known_value values cell = .ok (some value))
      (inserted : knowledge.UcpFacts.impl.mark_unique facts cell = .ok (changed, next)) :
      EngineStep constants context (facts, values) (next, values)
  /-- Tovabbi egyertelmusegi szabaly: az All-But-One, Base-Conv es BigInt-Mul bizonyiteka. -/
  | rule (facts next : knowledge.UcpFacts) (values : domains.UcpValueFacts)
      (cell : cells.CellId) (changed : Bool)
      (established : ∀ left right, context left -> context right -> left cell = right cell)
      (inserted : knowledge.UcpFacts.impl.mark_unique facts cell = .ok (changed, next)) :
      EngineStep constants context (facts, values) (next, values)

inductive EngineExecution (constants : Constants F) (context : OriginalContext cells.CellId F) :
    knowledge.UcpFacts × domains.UcpValueFacts -> knowledge.UcpFacts × domains.UcpValueFacts -> Prop where
  | refl (state) : EngineExecution constants context state state
  | step {first middle last} (earlier : EngineExecution constants context first middle)
      (next : EngineStep p constants context middle last) :
      EngineExecution constants context first last

variable (surjective : Function.Surjective (fun value : Int => (value : F)))

include surjective in
theorem engine_step_sound (positive : 1 < (p : Int))
    (constants : Constants F) (context : OriginalContext cells.CellId F)
    (satisfiable : ∃ assignment, context assignment)
    {before after : knowledge.UcpFacts × domains.UcpValueFacts}
    (sound : KnowledgeSound p context before.1 before.2)
    (step : EngineStep p constants context before after) :
    KnowledgeSound p context after.1 after.2 := by
  cases step with
  | assign facts next values expression cell changed equation inferred inserted =>
      exact knowledge_with_facts p context facts next values sound
        (rust_assign_then_insert_is_sound p positive constants context facts next sound.known
          expression cell equation inferred changed inserted)
  | learn facts values next cell domain changed claim merged =>
      have checked := rust_mark_domain_preserves_knowledge p surjective positive context facts values
        sound cell domain claim
      rw [merged] at checked
      exact (WP.spec_ok _).mp checked |>.1
  | singleton facts next values cell value changed known inserted =>
      have forced := rust_known_value_is_forced context fieldValue values cell value satisfiable sound.covers known
      exact knowledge_with_facts p context facts next values sound
        (rust_mark_unique_preserves_soundness context facts next cell changed sound.known
          (fun left right leftValid rightValid =>
            (forced.2 left leftValid).trans (forced.2 right rightValid).symm) inserted)
  | rule facts next values cell changed established inserted =>
      exact knowledge_with_facts p context facts next values sound
        (rust_mark_unique_preserves_soundness context facts next cell changed sound.known established inserted)

include surjective in
/-- A K/Delta-fixpont helyessege: az invarians tetszoleges veges szabalyalkalmazas-sorozaton at megmarad. -/
theorem engine_execution_sound (positive : 1 < (p : Int))
    (constants : Constants F) (context : OriginalContext cells.CellId F)
    (satisfiable : ∃ assignment, context assignment)
    {before after : knowledge.UcpFacts × domains.UcpValueFacts}
    (sound : KnowledgeSound p context before.1 before.2)
    (execution : EngineExecution p constants context before after) :
    KnowledgeSound p context after.1 after.2 := by
  induction execution with
  | refl => exact sound
  | step _ next previous => exact engine_step_sound p surjective positive constants context satisfiable previous next

end Engine

end SourceProof
