import Proofs.RuleLink
import Proofs.Regression
import Mathlib.Data.ZMod.Basic

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
A dolgozat kozponti fogalmai es allitasai.

* Az aritmetikai halozat egy kenyszer es a publikus cellak kijelolese.
* A publikus megfigyeles a kontextust szukiti: ez a `Consistent` halmaz, a tetelek Γ-ja.
* Az `Overconstrained` a munka informacioszivargasi ertelmezese: a megfigyeles a privat cella
  egy, a halozat szerint egyebkent megvalosithato erteket kizar.
* A `Determined` a puszta egyertelmu meghatarozottsag; a visszaallitas ennel tobb: konkret
  erteket kell adnia egy olyan eljarasnak, amely csak publikus adatot kap.
-/

variable {F : Type} [Field F]

structure PublicCircuit (F : Type) where
  constraints : OriginalContext cells.CellId F
  isPublic : cells.CellId -> Prop

/-- A publikus cellakon a megfigyelt ertekeket ado tanuk halmaza. -/
def Consistent (circuit : PublicCircuit F) (observed : cells.CellId -> F) : OriginalContext cells.CellId F :=
  fun assignment => circuit.constraints assignment ∧ ∀ cell, circuit.isPublic cell -> assignment cell = observed cell

/-- A cella erteket a publikus megfigyeles egyertelmuen meghatarozza. -/
def Determined (circuit : PublicCircuit F) (observed : cells.CellId -> F) (cell : cells.CellId) : Prop :=
  (∃ assignment, Consistent circuit observed assignment) ∧
    ∀ left right, Consistent circuit observed left -> Consistent circuit observed right -> left cell = right cell

/-- Overconstrainedness: a megfigyeles kizar egy, a halozat szerint megvalosithato privat erteket. -/
def Overconstrained (circuit : PublicCircuit F) (observed : cells.CellId -> F) (cell : cells.CellId) : Prop :=
  (∃ assignment, Consistent circuit observed assignment) ∧
    ∃ value, Feasible circuit.constraints cell value ∧ ¬ Feasible (Consistent circuit observed) cell value

/-- A QED² tulajdonsaga: a bemenetek meghatarozzak a kimeneteket. -/
def ProperlyConstrained (constraints : OriginalContext cells.CellId F)
    (inputs outputs : cells.CellId -> Prop) : Prop :=
  ∀ left right, constraints left -> constraints right ->
    (∀ cell, inputs cell -> left cell = right cell) -> ∀ cell, outputs cell -> left cell = right cell

theorem overconstrained_of_cover (circuit : PublicCircuit F) (observed : cells.CellId -> F) (cell : cells.CellId)
    (satisfiable : ∃ assignment, Consistent circuit observed assignment) (allowed : F -> Prop)
    (covers : ∀ assignment, Consistent circuit observed assignment -> allowed (assignment cell))
    (structural : Assignment cells.CellId F) (structuralValid : circuit.constraints structural)
    (excluded : ¬ allowed (structural cell)) : Overconstrained circuit observed cell := by
  refine ⟨satisfiable, structural cell, ⟨structural, structuralValid, rfl⟩, ?_⟩
  rintro ⟨assignment, valid, same⟩
  exact excluded (same ▸ covers assignment valid)

section Qed

variable (p : Nat) [CharP F p]
  (surjective : Function.Surjective (fun value : Int => (value : F)))

include surjective in
/-- **A QED² helyessegi erveles adaptacioja**: ha a bemenetekbol indulo K/Delta-fixpont minden kimenetet
K-ba tesz, a halozat nem alulkenyszerezett. A szabalyok a fix bemeneti ertekek szerinti kontextusban ervenyesek. -/
theorem qed2_fixpoint_soundness (positive : 1 < (p : Int))
    (constants : Constants F) (constraints : OriginalContext cells.CellId F)
    (inputs outputs : cells.CellId -> Prop)
    (initialFacts finalFacts : knowledge.UcpFacts) (initialValues finalValues : domains.UcpValueFacts)
    (start : ∀ observed, (∃ assignment, Consistent ⟨constraints, inputs⟩ observed assignment) ->
      KnowledgeSound p (Consistent ⟨constraints, inputs⟩ observed) initialFacts initialValues)
    (execution : ∀ observed, (∃ assignment, Consistent ⟨constraints, inputs⟩ observed assignment) ->
      EngineExecution p constants (Consistent ⟨constraints, inputs⟩ observed)
        (initialFacts, initialValues) (finalFacts, finalValues))
    (covered : ∀ cell, outputs cell -> finalFacts.unique_cells cell = true) :
    ProperlyConstrained constraints inputs outputs := by
  intro left right leftValid rightValid sameInputs cell output
  have leftConsistent : Consistent ⟨constraints, inputs⟩ left left := ⟨leftValid, fun _ _ => rfl⟩
  have rightConsistent : Consistent ⟨constraints, inputs⟩ left right :=
    ⟨rightValid, fun key input => (sameInputs key input).symm⟩
  have satisfiable : ∃ assignment, Consistent ⟨constraints, inputs⟩ left assignment := ⟨left, leftConsistent⟩
  have sound := engine_execution_sound p surjective positive constants (Consistent ⟨constraints, inputs⟩ left)
    satisfiable (start left satisfiable) (execution left satisfiable)
  exact sound.known cell (covered cell output) left right leftConsistent rightConsistent

include surjective in
/-- Ugyanaz az erveles forditott szerepekkel: a publikus cellak bemenetek, a privat cellak kimenetek. -/
theorem private_cells_determined_by_public (positive : 1 < (p : Int))
    (constants : Constants F) (circuit : PublicCircuit F) (observed : cells.CellId -> F)
    (initialFacts finalFacts : knowledge.UcpFacts) (initialValues finalValues : domains.UcpValueFacts)
    (satisfiable : ∃ assignment, Consistent circuit observed assignment)
    (start : KnowledgeSound p (Consistent circuit observed) initialFacts initialValues)
    (execution : EngineExecution p constants (Consistent circuit observed)
      (initialFacts, initialValues) (finalFacts, finalValues))
    (cell : cells.CellId) (reached : finalFacts.unique_cells cell = true) :
    Determined circuit observed cell := by
  have sound := engine_execution_sound p surjective positive constants (Consistent circuit observed)
    satisfiable start execution
  exact ⟨satisfiable, sound.known cell reached⟩

end Qed

section Recovery

variable (p : Nat) [CharP F p]
  (surjective : Function.Surjective (fun value : Int => (value : F)))
variable {Aux Action Stop Error : Type}

include surjective in
/-- **A visszaallitas fo tetele a dolgozat fogalmaiban.** A kinyert eljaras altal pontosnak jelentett
ertek megegyezik minden, a publikus adatokkal osszeegyeztetheto tanu titkos ertekevel. -/
theorem rust_recovery_reveals_secret (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (circuit : PublicCircuit F) (observed : cells.CellId -> F)
    (oracle : RecoveryOracle Aux Action Stop Error) (constants : Constants F)
    (searchFacts : Aux -> Assignment cells.CellId F -> Prop) (stopped : Stop -> Aux -> Prop)
    (contracts : OracleContracts p oracle constants (Consistent circuit observed)
      (fun aux => ∀ assignment, Consistent circuit observed assignment -> searchFacts aux assignment) stopped)
    (initial final : CoreState Aux) (status : Stop) (start : StateSound p (Consistent circuit observed) initial)
    (returned : recovery_loop.run_recovery (coreMachine p oracle) initial = .ok (.Ok (status, final)))
    (cell : cells.CellId) (value : Int)
    (known : domains.UcpValueFacts.impl.known_value final.values cell = .ok (some value))
    (secret : Assignment cells.CellId F) (witness : Consistent circuit observed secret) :
    secret cell = fieldValue value ∧ Determined circuit observed cell := by
  have forced := rust_recovered_value_is_forced p surjective positive bits oracle constants
    (Consistent circuit observed) searchFacts stopped contracts initial final status start returned cell value known
  refine ⟨forced.2 secret witness, ⟨secret, witness⟩, ?_⟩
  intro left right leftValid rightValid
  exact (forced.2 left leftValid).trans (forced.2 right rightValid).symm

include surjective in
/-- Ha a halozat egy masik tanuja mas erteket ad, a visszaallitott ertek szivargast is jelent. -/
theorem rust_recovery_proves_overconstrained (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (circuit : PublicCircuit F) (observed : cells.CellId -> F)
    (oracle : RecoveryOracle Aux Action Stop Error) (constants : Constants F)
    (searchFacts : Aux -> Assignment cells.CellId F -> Prop) (stopped : Stop -> Aux -> Prop)
    (contracts : OracleContracts p oracle constants (Consistent circuit observed)
      (fun aux => ∀ assignment, Consistent circuit observed assignment -> searchFacts aux assignment) stopped)
    (initial final : CoreState Aux) (status : Stop) (start : StateSound p (Consistent circuit observed) initial)
    (returned : recovery_loop.run_recovery (coreMachine p oracle) initial = .ok (.Ok (status, final)))
    (cell : cells.CellId) (value : Int)
    (known : domains.UcpValueFacts.impl.known_value final.values cell = .ok (some value))
    (alternative : Assignment cells.CellId F) (alternativeValid : circuit.constraints alternative)
    (different : alternative cell ≠ fieldValue value) : Overconstrained circuit observed cell := by
  have forced := rust_recovered_value_is_forced p surjective positive bits oracle constants
    (Consistent circuit observed) searchFacts stopped contracts initial final status start returned cell value known
  obtain ⟨witness, witnessValid, _⟩ := forced.1
  exact overconstrained_of_cover circuit observed cell ⟨witness, witnessValid⟩ (· = fieldValue value)
    forced.2 alternative alternativeValid different

/-- Az eljaras bemenete kizarolag a publikus nezet. A tanu megvaltoztatasa azonos nezet mellett nem hat az eredmenyre. -/
theorem recovery_is_witness_independent {View : Type} (viewOf : Assignment cells.CellId F -> View)
    (initialOf : View -> CoreState Aux) (oracleOf : View -> RecoveryOracle Aux Action Stop Error)
    (left right : Assignment cells.CellId F) (sameView : viewOf left = viewOf right) :
    recovery_loop.run_recovery (coreMachine p (oracleOf (viewOf left))) (initialOf (viewOf left)) =
      recovery_loop.run_recovery (coreMachine p (oracleOf (viewOf right))) (initialOf (viewOf right)) := by
  rw [sameView]

end Recovery

/-! ## A puszta egyertelmuseg nem azonos a visszaallitassal -/

/-- A kinyert Assign a cella egyertelmuseget igazolja, de az ertek az ismeretlen konstanstol fugg:
K-tagsagbol onmagaban nem kovetkezik konkret ertek. -/
theorem rust_unique_cell_has_no_abstract_value (cell : cells.CellId) (target : F) :
    (∃ constants : Constants F, ∀ assignment : Assignment cells.CellId F,
      evaluate constants assignment (.Add (.Var cell) (.Const .Unknown)) [] = 0 -> assignment cell = target) := by
  refine ⟨⟨fun _ => 1, fun _ => -target, fun _ => one_ne_zero⟩, ?_⟩
  intro assignment zero
  simp only [evaluate, scalarValue] at zero
  exact add_neg_eq_zero.mp zero

theorem rust_assign_marks_unknown_offset_unique (cell : cells.CellId) (modulus : Int) :
    rules.analyze_assign_candidate (.Add (.Var cell) (.Const .Unknown)) emptyFacts (Option.some modulus) =
      .ok (withCandidate cell) := by
  rw [assign_matches_spec]
  simp [assignSpec, uniqueSpec, emptyFacts, mergeAnalysis, withCandidate, noCandidate]

abbrev cubeCell : cells.CellId := firstCell

def cubeEquation : expressions.UcpExpr :=
  .Add (.Mul (.Var cubeCell) (.Mul (.Var cubeCell) (.Var cubeCell))) (.Const (.Known (-3)))

theorem rust_rules_reject_cube_equation :
    rules.analyze_assign_candidate cubeEquation emptyFacts (Option.some 5) = .ok invalidAnalysis := by
  rw [assign_matches_spec]
  simp [cubeEquation, assignSpec, uniqueSpec, emptyFacts, zeroConstant, nonzeroConstant, mergeAnalysis,
    invalidAnalysis]

def cubeCircuit : PublicCircuit (ZMod 5) :=
  { constraints := fun assignment => assignment cubeCell ^ 3 = 3, isPublic := fun _ => False }

/-- x³=3 modulo 5 egyertelmu megoldasu, a szabalyok megis elutasitjak: egyertelmuseg szabaly nelkul. -/
theorem cube_is_determined_without_rule :
    Determined cubeCircuit (fun _ => 0) cubeCell := by
  refine ⟨⟨fun _ => 2, by simp [cubeCircuit], fun _ impossible => impossible.elim⟩, ?_⟩
  rintro left right ⟨leftValid, _⟩ ⟨rightValid, _⟩
  have unique : ∀ value : ZMod 5, value ^ 3 = 3 -> value = 2 := by decide
  exact (unique _ leftValid).trans (unique _ rightValid).symm

end SourceProof
