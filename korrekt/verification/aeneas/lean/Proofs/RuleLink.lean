import Proofs.RecoveryDriver
import Recovery.GlobalExecution
import Recovery.SolverSteps
import Recovery.Root
import Recovery.AllButOne
import Recovery.BaseConversion
import Recovery.Lookup
import Mathlib.LinearAlgebra.Matrix.Rank

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
A kezzel irt Recovery-modell es a kinyert kod kapcsolata.
1. A konkret allapot invariansa maga utan vonja a modell `AnalysisSound` invariansat.
2. A modellbeli szabalyok es a solvervalaszok a motor es a beolvasztas bizonyitekaiva alakulnak.
-/

section Link

variable {F : Type} [Field F]

def fieldArithmetic (F : Type) [Field F] : Recovery.Arithmetic F :=
  { zero := 0, one := 1, add := (· + ·), mul := (· * ·), neg := (- ·) }

theorem field_ring_laws : Recovery.CommutativeRingLaws (fieldArithmetic F) where
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  add_neg := add_neg_cancel
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  mul_zero := mul_zero
  mul_add := mul_add

theorem field_no_zero_divisors : Recovery.NoZeroDivisors (fieldArithmetic F) where
  mul_eq_zero := fun _ _ zero => mul_eq_zero.mp zero

variable (p : Nat) [CharP F p]
  (surjective : Function.Surjective (fun value : Int => (value : F)))
variable {Aux : Type}

/-- A konkret allapot modellbeli kepe. -/
noncomputable def modelState (searchFacts : Aux -> Assignment cells.CellId F -> Prop) (state : CoreState Aux) :
    Recovery.AnalysisState cells.CellId F where
  knowledge := fun cell =>
    { domain := (state.values.domains cell).map (fun domain value => DomainContains fieldValue domain value)
      samples := (coreView searchFacts state).samples cell
      complete := completeDomainTag state.values cell }
  unique := state.facts.unique_cells
  nonUnique := state.marks
  searchFacts := searchFacts state.aux
  solverCalls := 0
  epoch := 0

/-- **Modell-kod kapcsolat**: a kinyert allapot invariansa a modell invariansat adja. -/
theorem core_refines_model (context : OriginalContext cells.CellId F)
    (searchFacts : Aux -> Assignment cells.CellId F -> Prop) (state : CoreState Aux)
    (sound : StateSound p context state)
    (hints : ∀ assignment, context assignment -> searchFacts state.aux assignment) :
    Recovery.AnalysisSound context (modelState searchFacts state) := by
  have viewSound := core_view_sound p context searchFacts state sound hints
  refine ⟨sound.satisfiable, fun cell => ⟨?_, ?_, ?_⟩, ?_, ?_, hints⟩
  · intro domain recorded assignment valid
    exact viewSound.covers cell domain recorded assignment valid
  · intro value sampled
    exact viewSound.samples cell value sampled
  · intro complete
    obtain ⟨domain, recorded, exact⟩ := viewSound.complete cell complete
    exact ⟨domain, recorded, exact⟩
  · intro cell marked left right leftValid rightValid
    exact sound.knowledge.known cell marked left right leftValid rightValid
  · intro cell marked
    obtain ⟨left, right, leftValid, rightValid, different⟩ := sound.nonUnique cell marked
    exact ⟨left cell, right cell, ⟨left, leftValid, rfl⟩, ⟨right, rightValid, rfl⟩, different⟩

/-- A modell riporttetele a konkret futas vegallapotara is alkalmazhato. -/
theorem rust_report_exact_is_complete (context : OriginalContext cells.CellId F)
    (searchFacts : Aux -> Assignment cells.CellId F -> Prop) (state : CoreState Aux)
    (sound : StateSound p context state)
    (hints : ∀ assignment, context assignment -> searchFacts state.aux assignment)
    (cell : cells.CellId) (value : F)
    (recorded : ((modelState searchFacts state).knowledge cell).domain = some (Recovery.Singleton value)) :
    Recovery.Unique context cell ∧ Recovery.Complete context cell (Recovery.Singleton value) :=
  Recovery.reported_exact_sound (core_refines_model p context searchFacts state sound hints) recorded

end Link

/-! ## Szabalyok es solvervalaszok mint bizonyitek -/

section Rules

variable {F : Type} [Field F] (p : Nat) [CharP F p]

/-- Az All-But-One modelltetele egy motorlepes bizonyitekat adja. -/
theorem all_but_one_rule_evidence (context : OriginalContext cells.CellId F) (selector : cells.CellId)
    (branches : List (cells.CellId × F)) (selected : cells.CellId × F)
    (total : Assignment cells.CellId F -> F)
    (distinct : (branches.map Prod.snd).Nodup) (member : selected ∈ branches)
    (selectorUnique : ∀ left right, context left -> context right -> left selector = right selector)
    (totalStable : ∀ left right, context left -> context right -> total left = total right)
    (sumEquation : ∀ assignment, context assignment ->
      Recovery.branchSum (fieldArithmetic F) assignment branches = total assignment)
    (products : Recovery.BranchProducts context (fieldArithmetic F) selector branches) :
    ∀ left right, context left -> context right -> left selected.1 = right selected.1 :=
  Recovery.all_but_one_unique field_ring_laws field_no_zero_divisors distinct member selectorUnique totalStable
    sumEquation products

/-- A BigInt-Mul szabaly: teljes oszloprangu, konstans egyutthatos rendszer megoldasa egyertelmu. -/
theorem linear_system_rule_evidence {Equation Unknown : Type} [Fintype Equation] [Fintype Unknown]
    [DecidableEq Unknown] (context : OriginalContext cells.CellId F)
    (matrix : Matrix Equation Unknown F) (cellOf : Unknown -> cells.CellId)
    (remainder : Equation -> Assignment cells.CellId F -> F)
    (stable : ∀ equation left right, context left -> context right -> remainder equation left = remainder equation right)
    (equations : ∀ assignment, context assignment -> ∀ equation,
      Matrix.mulVec matrix (fun unknown => assignment (cellOf unknown)) equation + remainder equation assignment = 0)
    (fullRank : matrix.rank = Fintype.card Unknown) (unknown : Unknown) :
    ∀ left right, context left -> context right -> left (cellOf unknown) = right (cellOf unknown) := by
  intro left right leftValid rightValid
  have injective : Function.Injective matrix.mulVec := by
    have dimension := LinearMap.finrank_range_add_finrank_ker matrix.mulVecLin
    rw [Matrix.rank] at fullRank
    rw [fullRank, Module.finrank_fintype_fun_eq_card] at dimension
    have kernel : Module.finrank F (LinearMap.ker matrix.mulVecLin) = 0 := by omega
    have bottom := Submodule.finrank_eq_zero.mp kernel
    exact LinearMap.ker_eq_bot.mp bottom
  have same : Matrix.mulVec matrix (fun unknown => left (cellOf unknown)) =
      Matrix.mulVec matrix (fun unknown => right (cellOf unknown)) := by
    funext equation
    have leftEquation := equations left leftValid equation
    have rightEquation := equations right rightValid equation
    rw [stable equation left right leftValid rightValid] at leftEquation
    exact add_right_cancel (leftEquation.trans rightEquation.symm)
  exact congrFun (injective same) unknown

/-- A Base-Conv Nat-modelljet a testbeli kontextusra viszi at egy injektiv szamlekepezessel. -/
theorem base_conversion_rule_evidence (context : OriginalContext cells.CellId F) (toNat : F -> Nat)
    (injective : Function.Injective toNat) (packed : cells.CellId) (digits : List cells.CellId)
    (base modulus : Nat) (positive : 0 < base)
    (bounded : ∀ assignment, context assignment ->
      Recovery.DigitsBounded base (digits.map (fun cell => toNat (assignment cell))))
    (noWrap : ∀ assignment, context assignment ->
      Recovery.packDigits base (digits.map (fun cell => toNat (assignment cell))) < modulus)
    (equation : ∀ assignment, context assignment ->
      Recovery.packDigits base (digits.map (fun cell => toNat (assignment cell))) % modulus =
        toNat (assignment packed) % modulus)
    (packedUnique : ∀ left right, context left -> context right -> left packed = right packed)
    (cell : cells.CellId) (member : cell ∈ digits) :
    ∀ left right, context left -> context right -> left cell = right cell := by
  let natContext : Recovery.Context cells.CellId Nat := fun numbers =>
    ∃ assignment, context assignment ∧ ∀ key, numbers key = toNat (assignment key)
  have mapped : ∀ (numbers : cells.CellId -> Nat) (assignment : cells.CellId -> F),
      (∀ key, numbers key = toNat (assignment key)) ->
      digits.map numbers = digits.map (fun key => toNat (assignment key)) := by
    intro numbers assignment same
    exact List.map_congr_left (fun key _ => same key)
  have natUnique := Recovery.base_conversion_unique (ctx := natContext) (packed := packed) (digits := digits)
    (base := base) (modulus := modulus) positive
    (by rintro numbers ⟨assignment, valid, same⟩; rw [mapped numbers assignment same]; exact bounded assignment valid)
    (by rintro numbers ⟨assignment, valid, same⟩; rw [mapped numbers assignment same]; exact noWrap assignment valid)
    (by
      rintro numbers ⟨assignment, valid, same⟩
      rw [mapped numbers assignment same, same packed]
      exact equation assignment valid)
    (by
      rintro numbers others ⟨assignment, valid, same⟩ ⟨other, otherValid, otherSame⟩
      rw [same packed, otherSame packed, packedUnique assignment other valid otherValid])
    member
  intro left right leftValid rightValid
  exact injective (natUnique (fun key => toNat (left key)) (fun key => toNat (right key))
    ⟨left, leftValid, fun _ => rfl⟩ ⟨right, rightValid, fun _ => rfl⟩)

/-- Modellbeli lefedesbol a beolvasztas domain-bizonyiteka. -/
theorem domain_claim_of_list_cover (context : OriginalContext cells.CellId F) (cell : cells.CellId)
    (domain : domains.UcpValueDomain)
    (covers : ∀ assignment, context assignment -> ∃ representative ∈ DomainMembers domain,
      fieldValue representative = assignment cell)
    (canonical : CanonicalDomain (p : Int) domain) (small : (DomainMembers domain).card ≤ 256)
    (fits : DomainFits domain) : DomainClaim p context cell domain :=
  ⟨fun assignment valid => (domain_contains_iff domain _).mpr (covers assignment valid), canonical, small, fits⟩

/-- A publikus megfigyeles pontos erteke kiindulo domainkent bejegyezheto. -/
theorem public_value_claim (context : OriginalContext cells.CellId F) (cell : cells.CellId) (value : Int)
    (observed : ∀ assignment, context assignment -> assignment cell = fieldValue value)
    (canonical : centeredRepresentative value (p : Int) = value) (fits : value.natAbs.size < 2 ^ 64) :
    DomainClaim p context cell (.Exact value) := by
  refine ⟨observed, ?_, by simp [DomainMembers], ?_⟩
  · intro entry member
    simp only [DomainMembers, Finset.mem_singleton] at member
    subst member
    exact canonical
  · intro entry member
    simp only [DomainMembers, Finset.mem_singleton] at member
    subst member
    exact fits

/-- A fast probe: SAT-modell es kizarasi UNSAT egyutt pontos, egyertelmu eredmenyt igazol. -/
theorem fast_probe_evidence (context : OriginalContext cells.CellId F) (entries : EvidenceMap)
    (cell : cells.CellId) (value : Int) (samples : alloc.vec.Vec Int)
    (modelled : samples.val = [value]) (sat : Feasible context cell (fieldValue value))
    (unsat : ¬ ∃ assignment, context assignment ∧ assignment cell ≠ fieldValue value)
    (canonical : centeredRepresentative value (p : Int) = value)
    (fits : value.natAbs.size < 2 ^ 64) (capacity : Headroom entries 1) :
    EvidenceClaim p context entries
      { cell := cell, samples := samples, model_samples := [], domain := some (.Exact value),
        unique := true, non_unique := false } := by
  have forced : ∀ assignment, context assignment -> assignment cell = fieldValue value := by
    intro assignment valid
    by_contra different
    exact unsat ⟨assignment, valid, different⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sample member
    simp only [modelled, List.mem_singleton] at member
    subst member
    exact sat
  · intro entry impossible
    cases impossible
  · intro domain same
    cases same
    refine ⟨forced, ?_, by simp [DomainMembers], ?_⟩
    · intro entry member
      simp only [DomainMembers, Finset.mem_singleton] at member
      subst member
      exact canonical
    · intro entry member
      simp only [DomainMembers, Finset.mem_singleton] at member
      subst member
      exact fits
  · intro _ left right leftValid rightValid
    exact (forced left leftValid).trans (forced right rightValid).symm
  · intro impossible
    cases impossible
  · simpa [modelled, modelLoad] using capacity

/-- Refine: kizarasi UNSAT-bol lefedo domain; a mintak kulon, megvalosithato modellekbol jonnek. -/
theorem refinement_evidence (context : OriginalContext cells.CellId F) (entries : EvidenceMap)
    (cell : cells.CellId) (domain : domains.UcpValueDomain) (samples : alloc.vec.Vec Int)
    (sat : ∀ sample ∈ samples.val, Feasible context cell (fieldValue sample))
    (unsat : ¬ ∃ assignment, context assignment ∧
      ¬ ∃ representative ∈ DomainMembers domain, fieldValue representative = assignment cell)
    (canonical : CanonicalDomain (p : Int) domain) (small : (DomainMembers domain).card ≤ 256)
    (fits : DomainFits domain) (capacity : Headroom entries samples.val.length) :
    EvidenceClaim p context entries
      { cell := cell, samples := samples, model_samples := [], domain := some domain,
        unique := false, non_unique := false } := by
  refine ⟨sat, ?_, ?_, ?_, ?_, ?_⟩
  · intro entry impossible
    cases impossible
  · intro stored same
    cases same
    apply domain_claim_of_list_cover p context cell domain _ canonical small fits
    intro assignment valid
    by_contra missing
    exact unsat ⟨assignment, valid, missing⟩
  · intro impossible
    cases impossible
  · intro impossible
    cases impossible
  · simpa [modelLoad] using capacity

end Rules

end SourceProof
