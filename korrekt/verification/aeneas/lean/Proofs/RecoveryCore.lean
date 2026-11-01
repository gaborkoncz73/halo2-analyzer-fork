import Proofs.Certification

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
A `recovery_core.rs` kinyert allapotatmenetei.
Az invarians szerint minden minta az eredeti kontextusbol valo, es minden tarolt tudas helyes.
-/

section Core

variable {F : Type} [Field F] (p : Nat) [CharP F p]
  (surjective : Function.Surjective (fun value : Int => (value : F)))

abbrev EvidenceMap := alloc.collections.btree.map.BTreeMap cells.CellId
  (alloc.collections.btree.set.BTreeSet num_bigint.bigint.BigInt alloc.alloc.Global) alloc.alloc.Global

/-- A tarolt W-minta az eredeti kontextus egy megoldasabol szarmazik, es kanonikus. -/
def SamplesValid (context : OriginalContext cells.CellId F) (entries : EvidenceMap) : Prop :=
  ∀ entry ∈ entries, ∀ sample ∈ entry.2,
    Feasible context entry.1 (fieldValue sample) ∧ centeredRepresentative sample (p : Int) = sample

/-- A mintahalmazok mereten es a meg beszurando r mintan nem lep tul a platform usize tartomanyan. -/
def Headroom (entries : EvidenceMap) (remaining : Nat) : Prop :=
  remaining ≤ Usize.max ∧ ∀ entry ∈ entries, entry.2.card + remaining ≤ Usize.max

def NonUniqueSound (context : OriginalContext cells.CellId F)
    (marks : std.collections.hash.set.HashSet cells.CellId std.hash.random.RandomState alloc.alloc.Global) : Prop :=
  ∀ cell, marks cell = true -> ∃ left right, context left ∧ context right ∧ left cell ≠ right cell

/-- A recovery teljes kinyert szemantikai allapotanak invariansa. -/
structure CoreSound (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (values : domains.UcpValueFacts) (evidence : recovery_core.RecoveryEvidence)
    (marks : std.collections.hash.set.HashSet cells.CellId std.hash.random.RandomState alloc.alloc.Global) : Prop where
  satisfiable : ∃ assignment, context assignment
  knowledge : KnowledgeSound p context facts values
  samples : SamplesValid p context evidence.feasible
  capacity : Headroom evidence.feasible 0
  nonUnique : NonUniqueSound context marks

noncomputable def rememberedEntries (entries : EvidenceMap) (cell : cells.CellId) (value : Int) : EvidenceMap := by
  classical
  exact (cell, insert value (((entries.find? (fun pair => decide (pair.1 = cell))).map Prod.snd).getD
      (∅ : Finset Int))) :: entries.filter (fun pair => decide (pair.1 ≠ cell))

theorem rust_remember_sample_result (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (evidence : recovery_core.RecoveryEvidence) (cell : cells.CellId) (sample : Int) :
    recovery_core.RecoveryEvidence.impl.try_remember_sample evidence cell sample (p : Int) =
      .ok (.Ok (), ⟨rememberedEntries evidence.feasible cell (centeredRepresentative sample (p : Int))⟩) := by
  classical
  unfold recovery_core.RecoveryEvidence.impl.try_remember_sample
  rw [rust_normalization_succeeds sample (p : Int) positive bits]
  simp only [bind_ok, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
    cell_clone_correct, alloc.collections.btree.map.BTreeMap.impl.entry, uncurry_apply_pair]
  cases found : evidence.feasible.find? (fun pair => @decide (pair.1 = cell) (Classical.propDecidable _)) <;>
    simp [found, rememberedEntries, alloc.collections.btree.map.entry.Entry.impl.or_default,
      alloc.collections.btree.set.BTreeSetTGlobal.Insts.CoreDefaultDefault,
      alloc.collections.btree.set.BTreeSetTGlobal.Insts.CoreDefaultDefault.default,
      alloc.collections.btree.set.BTreeSet.impl.insert, mapEntryBack, Insert.insert]
  congr!

theorem remembered_preserves_samples (positive : 1 < (p : Int))
    (context : OriginalContext cells.CellId F) (entries : EvidenceMap) (cell : cells.CellId) (sample : Int)
    (valid : SamplesValid p context entries) (feasible : Feasible context cell (fieldValue sample)) :
    SamplesValid p context (rememberedEntries entries cell (centeredRepresentative sample (p : Int))) := by
  classical
  intro entry member value inEntry
  simp only [rememberedEntries, List.mem_cons, List.mem_filter] at member
  rcases member with rfl | ⟨original, _⟩
  · simp only [Finset.mem_insert] at inEntry
    rcases inEntry with rfl | previous
    · refine ⟨?_, centered_idempotent (by omega)⟩
      obtain ⟨assignment, ctx, assigned⟩ := feasible
      refine ⟨assignment, ctx, assigned.trans ?_⟩
      exact ((field_eq_iff_residue (F := F) p _ _).mpr (centered_preserves_residue (by omega))).symm
    · cases found : entries.find? (fun pair => decide (pair.1 = cell)) with
      | none => simp [found] at previous
      | some pair =>
          simp only [found, Option.map_some, Option.getD_some] at previous
          have present := List.mem_of_find?_eq_some found
          have key : pair.1 = cell := by simpa using List.find?_some found
          have := valid pair present value previous
          rwa [key] at this
  · exact valid entry original value inEntry

theorem remembered_preserves_headroom (entries : EvidenceMap) (cell : cells.CellId) (value : Int)
    (remaining : Nat) (room : Headroom entries (remaining + 1)) :
    Headroom (rememberedEntries entries cell value) remaining := by
  classical
  obtain ⟨bound, cards⟩ := room
  refine ⟨by omega, ?_⟩
  intro entry member
  simp only [rememberedEntries, List.mem_cons, List.mem_filter] at member
  rcases member with rfl | ⟨original, _⟩
  · have grown := Finset.card_insert_le value
      (((entries.find? (fun pair => decide (pair.1 = cell))).map Prod.snd).getD (∅ : Finset Int))
    cases found : entries.find? (fun pair => decide (pair.1 = cell)) with
    | none =>
        simp only [found, Option.map_none, Option.getD_none, Finset.card_empty] at grown ⊢
        omega
    | some pair =>
        simp only [found, Option.map_some, Option.getD_some] at grown ⊢
        have := cards pair (List.mem_of_find?_eq_some found)
        omega
  · have := cards entry original
    omega

def RememberPost (context : OriginalContext cells.CellId F) (remaining : Nat) :
    core.result.Result Unit recovery_core.UnsupportedSample × recovery_core.RecoveryEvidence -> Prop
  | (.Ok _, next) => SamplesValid p context next.feasible ∧ Headroom next.feasible remaining
  | (.Err _, _) => True

theorem rust_remember_list_sound (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (context : OriginalContext cells.CellId F) (cell : cells.CellId) (samples : alloc.vec.Vec Int)
    (evidence : recovery_core.RecoveryEvidence) (remaining : Nat)
    (valid : SamplesValid p context evidence.feasible)
    (room : Headroom evidence.feasible (samples.val.length + remaining))
    (feasible : ∀ sample ∈ samples.val, Feasible context cell (fieldValue sample)) :
    WP.dspec (recovery_core.RecoveryEvidence.impl.try_remember_list evidence cell samples (p : Int))
      (RememberPost p context remaining) := by
  classical
  unfold recovery_core.RecoveryEvidence.impl.try_remember_list
  have started : WP.dspec (alloc.vec.IntoIteratorVec.into_iter samples)
      (fun iter : alloc.vec.into_iter.IntoIter Int => iter.val = samples.val) := by
    simp [alloc.vec.IntoIteratorVec.into_iter, alloc.vec.into_iter.IntoIter]
  apply WP.dspec_bind started
  intro iter sameSamples
  unfold recovery_core.RecoveryEvidence.impl.try_remember_list_loop
  simp only [bind_ok]
  refine generated_loop_preserves _
    (fun state : alloc.vec.into_iter.IntoIter Int × recovery_core.RecoveryEvidence =>
      SamplesValid p context state.2.feasible ∧ Headroom state.2.feasible (state.1.val.length + remaining) ∧
      ∀ sample ∈ state.1.val, Feasible context cell (fieldValue sample))
    (RememberPost p context remaining) ?_ (iter, evidence) ⟨valid, by simpa [sameSamples] using room,
      by simpa [sameSamples] using feasible⟩
  rintro ⟨current, state⟩ ⟨nowValid, nowRoom, nowFeasible⟩
  dsimp only at nowValid nowRoom nowFeasible ⊢
  unfold recovery_core.RecoveryEvidence.impl.try_remember_list_loop.body
  cases list : current.val with
  | nil =>
      have read : alloc.vec.into_iter.IteratorIntoIter.next current = .ok (none, current) := by
        simp only [alloc.vec.into_iter.IteratorIntoIter.next]
        split
        · rfl
        · simp_all
      rw [read]
      simp only [bind_ok, uncurry_apply_pair]
      simp only [list, List.length_nil, Nat.zero_add] at nowRoom
      simpa [LoopOutcome, RememberPost] using And.intro nowValid nowRoom
  | cons head tail =>
      obtain ⟨next, read, advanced⟩ := iterator_step current head tail list
      rw [read]
      simp only [bind_ok, uncurry_apply_pair]
      rw [rust_remember_sample_result p positive bits]
      simp only [bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, LoopOutcome]
      simp only [list, List.length_cons, List.mem_cons, forall_eq_or_imp] at nowRoom nowFeasible
      have shifted : Headroom state.feasible (tail.length + remaining + 1) := by
        have := nowRoom
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      simpa [LoopOutcome, advanced] using And.intro
        (remembered_preserves_samples p positive context state.feasible cell head nowValid nowFeasible.1)
        (And.intro (remembered_preserves_headroom _ cell _ _ shifted) nowFeasible.2)

def modelLoad (entries : EvidenceMap) : Nat := (entries.map (fun entry => entry.2.card)).sum

def ModelFeasible (context : OriginalContext cells.CellId F) (entries : EvidenceMap) : Prop :=
  ∀ entry ∈ entries, ∀ sample ∈ entry.2, Feasible context entry.1 (fieldValue sample)

theorem clone_iter_to_list (values acc : List Int) :
    alloc.vec.FromIteratorVec.iterToList
      (core.iter.traits.collect.IntoIterator.Blanket
        (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
          (alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT
            num_bigint.bigint.BigInt)
          recovery_core.RecoveryEvidence.try_remember_model.closure.Insts.CoreOpsFunctionFnMutTupleShared0BigIntBigInt)).iteratorInst
      ⟨values, ()⟩ acc = .ok (acc.reverse ++ values) := by
  induction values generalizing acc with
  | nil =>
      rw [alloc.vec.FromIteratorVec.iterToList]
      simp [core.iter.traits.collect.IntoIterator.Blanket,
        core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator,
        core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next]
  | cons head tail ih =>
      rw [alloc.vec.FromIteratorVec.iterToList]
      simp only [core.iter.traits.collect.IntoIterator.Blanket,
        core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator,
        core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
        recovery_core.RecoveryEvidence.try_remember_model.closure.Insts.CoreOpsFunctionFnMutTupleShared0BigIntBigInt,
        recovery_core.RecoveryEvidence.try_remember_model.closure.Insts.CoreOpsFunctionFnMutTupleShared0BigIntBigInt.call_mut,
        num_bigint.bigint.BigInt.Insts.CoreCloneClone.clone,
        List.head?_cons, List.tail_cons, bind_ok, uncurry_apply_pair] at ih ⊢
      rw [ih]
      simp

theorem rust_remember_model_sound (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (context : OriginalContext cells.CellId F) (models : EvidenceMap)
    (evidence : recovery_core.RecoveryEvidence) (remaining : Nat)
    (valid : SamplesValid p context evidence.feasible)
    (room : Headroom evidence.feasible (modelLoad models + remaining))
    (feasible : ModelFeasible context models) :
    WP.dspec (recovery_core.RecoveryEvidence.impl.try_remember_model evidence models (p : Int))
      (RememberPost p context remaining) := by
  classical
  unfold recovery_core.RecoveryEvidence.impl.try_remember_model
    SharedABTreeMap.Insts.CoreIterTraitsCollectIntoIteratorPairSharedAKSharedAVIter.into_iter
    recovery_core.RecoveryEvidence.impl.try_remember_model_loop
  simp only [bind_ok]
  refine generated_loop_preserves _
    (fun state : alloc.collections.btree.map.Iter cells.CellId (Finset Int) × recovery_core.RecoveryEvidence =>
      SamplesValid p context state.2.feasible ∧
      Headroom state.2.feasible (modelLoad state.1 + remaining) ∧ ModelFeasible context state.1)
    (RememberPost p context remaining) ?_ (models, evidence) ⟨valid, room, feasible⟩
  rintro ⟨current, state⟩ ⟨nowValid, nowRoom, nowFeasible⟩
  dsimp only at nowValid nowRoom nowFeasible ⊢
  unfold recovery_core.RecoveryEvidence.impl.try_remember_model_loop.body
  simp only [alloc.collections.btree.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next,
    bind_ok, uncurry_apply_pair]
  cases current with
  | nil =>
      simp only [modelLoad, List.map_nil, List.sum_nil, Nat.zero_add] at nowRoom
      simpa [LoopOutcome, RememberPost] using And.intro nowValid nowRoom
  | cons head tail =>
      obtain ⟨cell, values⟩ := head
      simp only [List.head?_cons, List.tail_cons, alloc.collections.btree.set.BTreeSet.impl.iter,
        core.iter.traits.iterator.Iterator.map.default, bind_ok, uncurry_apply_pair,
        core.iter.traits.iterator.Iterator.collect.default, core.iter.traits.collect.FromIteratorVec,
        alloc.vec.FromIteratorVec.from_iter, core.iter.traits.collect.IntoIterator.Blanket.into_iter]
      have listed := clone_iter_to_list values.toList []
      simp only [List.reverse_nil, List.nil_append] at listed
      rw [listed]
      have loadSplit : modelLoad ((cell, values) :: tail) = values.card + modelLoad tail := by
        simp [modelLoad]
      have fits : values.card ≤ Usize.max := by
        have := nowRoom.1
        rw [loadSplit] at this
        omega
      have listFits : values.toList.length ≤ Usize.max := by simpa using fits
      simp only [bind_ok, Finset.length_toList, fits, ↓reduceDIte]
      have tailFeasible : ModelFeasible context tail := fun entry member =>
        nowFeasible entry (List.mem_cons_of_mem _ member)
      have here : ∀ sample ∈ (alloc.vec.Vec.from values.toList (by simpa using fits)).val,
          Feasible context cell (fieldValue sample) := by
        intro sample member
        rw [alloc.vec.Vec.from_val] at member
        exact nowFeasible (cell, values) (List.mem_cons_self) sample (Finset.mem_toList.mp member)
      have roomHere : Headroom state.feasible
          ((alloc.vec.Vec.from values.toList (by simpa using fits)).val.length + (modelLoad tail + remaining)) := by
        rw [alloc.vec.Vec.from_val, Finset.length_toList, ← Nat.add_assoc, ← loadSplit]
        exact nowRoom
      apply WP.dspec_bind (rust_remember_list_sound p positive bits context cell _ state _ nowValid roomHere here)
      rintro ⟨result, next⟩ post
      cases result with
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, LoopOutcome, RememberPost]
      | Ok unit =>
          obtain ⟨nextValid, nextRoom⟩ := post
          simpa [core.result.Result.Insts.CoreOpsTry.branch, LoopOutcome] using
            And.intro nextValid (And.intro nextRoom tailFeasible)

/-- A beolvasztando keresesi eredmeny bizonyitasi kotelezettsege. -/
structure EvidenceClaim (context : OriginalContext cells.CellId F)
    (entries : EvidenceMap) (established : recovery_core.EstablishedEvidence) : Prop where
  samples : ∀ sample ∈ established.samples.val, Feasible context established.cell (fieldValue sample)
  models : ModelFeasible context established.model_samples
  domain : ∀ domain, established.domain = some domain -> DomainClaim p context established.cell domain
  unique : established.unique = true ->
    ∀ left right, context left -> context right -> left established.cell = right established.cell
  nonUnique : established.non_unique = true ->
    ∃ left right, context left ∧ context right ∧ left established.cell ≠ right established.cell
  capacity : Headroom entries (established.samples.val.length + modelLoad established.model_samples)

def MergePost (context : OriginalContext cells.CellId F) :
    core.result.Result Bool recovery_core.UnsupportedSample × recovery_core.RecoveryEvidence ×
      knowledge.UcpFacts × domains.UcpValueFacts ×
      std.collections.hash.set.HashSet cells.CellId std.hash.random.RandomState alloc.alloc.Global -> Prop
  | (.Ok _, evidence, facts, values, marks) => CoreSound p context facts values evidence marks
  | (.Err _, _, _, _, _) => True

theorem knowledge_with_facts (context : OriginalContext cells.CellId F) (facts next : knowledge.UcpFacts)
    (values : domains.UcpValueFacts) (sound : KnowledgeSound p context facts values)
    (known : KnownSound context next) : KnowledgeSound p context next values :=
  { sound with known := known }

include surjective in
-- A tenyleges Rust-beolvasztas elso fele: minden tudaselem csak igazolt eredmenybol bovul.
theorem rust_merge_evidence_sound (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (values : domains.UcpValueFacts) (evidence : recovery_core.RecoveryEvidence)
    (marks : std.collections.hash.set.HashSet cells.CellId std.hash.random.RandomState alloc.alloc.Global)
    (sound : CoreSound p context facts values evidence marks)
    (established : recovery_core.EstablishedEvidence)
    (claim : EvidenceClaim p context evidence.feasible established) :
    WP.dspec (recovery_core.merge_established_evidence evidence facts values marks established (p : Int))
      (MergePost p context) := by
  classical
  unfold recovery_core.merge_established_evidence
  have firstRoom : Headroom evidence.feasible
      (established.samples.val.length + (modelLoad established.model_samples + 0)) := by
    simpa using claim.capacity
  apply WP.dspec_bind (rust_remember_list_sound p positive bits context established.cell
    established.samples evidence _ sound.samples firstRoom claim.samples)
  rintro ⟨result, afterList⟩ post
  cases result with
  | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, MergePost]
  | Ok unit =>
      obtain ⟨listValid, listRoom⟩ := post
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
      apply WP.dspec_bind (rust_remember_model_sound p positive bits context established.model_samples
        afterList 0 listValid listRoom claim.models)
      rintro ⟨result, afterModel⟩ post
      cases result with
      | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, MergePost]
      | Ok unit =>
          obtain ⟨modelValid, modelRoom⟩ := post
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
          have uniquePost : WP.dspec (if established.unique = true then (do
                let ci ← cells.CellId.Insts.CoreCloneClone.clone established.cell
                let (changed1, facts2) ← knowledge.UcpFacts.impl.mark_unique facts ci
                Result.ok (facts2, changed1)) else Result.ok (facts, false))
              (fun answer => KnowledgeSound p context answer.1 values) := by
            split
            · rename_i marked
              simp only [cell_clone_correct, bind_ok, rust_mark_unique_matches_insert, uncurry_apply_pair]
              have kept := knowledge_with_facts p context facts (insertedFacts facts established.cell) values
                sound.knowledge (rust_mark_unique_preserves_soundness context facts _ established.cell _
                  sound.knowledge.known (claim.unique marked) (rust_mark_unique_matches_insert facts established.cell))
              simpa using kept
            · simpa using sound.knowledge
          apply WP.dspec_bind uniquePost
          rintro ⟨nextFacts, changed⟩ factsSound
          dsimp only at factsSound
          simp only [uncurry_apply_pair]
          have domainPost : WP.dspec (match established.domain with
              | Option.none => Result.ok (values, changed)
              | Option.some domain => do
                let ci ← cells.CellId.Insts.CoreCloneClone.clone established.cell
                let (b, values2) ← domains.UcpValueFacts.impl.mark_domain values ci domain
                let b1 ← if b = true then Result.ok true else Result.ok changed
                Result.ok (values2, b1))
              (fun answer => KnowledgeSound p context nextFacts answer.1) := by
            cases domainEntry : established.domain with
            | none => simpa using factsSound
            | some domain =>
                simp only [cell_clone_correct, bind_ok]
                apply WP.spec_dspec
                apply WP.spec_bind (rust_mark_domain_preserves_knowledge p surjective positive context
                  nextFacts values factsSound established.cell domain (claim.domain domain domainEntry))
                rintro ⟨merged, nextValues⟩ ⟨mergedSound, _⟩
                simp only [uncurry_apply_pair]
                split <;> simpa using mergedSound
          apply WP.dspec_bind domainPost
          rintro ⟨nextValues, changedAgain⟩ valuesSound
          dsimp only at valuesSound
          simp only [uncurry_apply_pair]
          split
          · rename_i marked
            have nextMarks : NonUniqueSound context
                (fun key => if key = established.cell then true else marks key) := by
              intro cell flagged
              by_cases same : cell = established.cell
              · subst cell
                exact claim.nonUnique marked
              · exact sound.nonUnique cell (by simpa [same] using flagged)
            have final : CoreSound p context nextFacts nextValues afterModel
                (fun key => if key = established.cell then true else marks key) :=
              ⟨sound.satisfiable, valuesSound, modelValid, modelRoom, nextMarks⟩
            simpa [std.collections.hash.set.HashSet.impl.insert, MergePost] using final
          · have final : CoreSound p context nextFacts nextValues afterModel marks :=
              ⟨sound.satisfiable, valuesSound, modelValid, modelRoom, sound.nonUnique⟩
            simpa [MergePost] using final

def CertifyPost (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts) :
    core.result.Result Bool recovery_core.CertificationError × domains.UcpValueFacts -> Prop
  | (.Ok _, values) => KnowledgeSound p context facts values
  | (.Err _, _) => True

theorem btree_card_length (members : Finset Int) (fits : members.card ≤ Usize.max) :
    ∃ size : Usize, alloc.collections.btree.set.BTreeSet.impl.len
        alloc.alloc.Global.Insts.CoreAllocAllocatorClone members = .ok size ∧ size.val = members.card := by
  have bounded : UScalar.check_bounds .Usize members.card := by
    scalar_tac
  simp only [alloc.collections.btree.set.BTreeSet.impl.len, UScalar.tryMk, UScalar.tryMkOpt,
    dite_eq_left bounded, Result.ofOption]
  exact ⟨_, rfl, UScalar.ofNatCore_val_eq _⟩

theorem certify_step_sound (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (values : domains.UcpValueFacts) (sound : KnowledgeSound p context facts values)
    (cell : cells.CellId) (samples : Finset Int)
    (feasible : ∀ sample ∈ samples, Feasible context cell (fieldValue sample)) :
    WP.dspec (domains.UcpValueFacts.impl.try_mark_complete_from_samples values cell samples (p : Int))
      (fun answer => match answer with
        | (.Ok _, next) => KnowledgeSound p context facts next
        | (.Err _, _) => True) :=
  WP.dspec_mono (rust_certification_preserves_knowledge p positive bits context facts values sound
    cell samples feasible) (by
      rintro ⟨result, next⟩ post
      cases result <;> simpa [CertificationPost] using post)

theorem rust_certify_domains_sound (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (values : domains.UcpValueFacts) (evidence : recovery_core.RecoveryEvidence)
    (sound : KnowledgeSound p context facts values)
    (samplesValid : SamplesValid p context evidence.feasible)
    (room : Headroom evidence.feasible 0) :
    WP.dspec (recovery_core.RecoveryEvidence.impl.try_certify_complete_domains evidence facts values (p : Int))
      (CertifyPost p context facts) := by
  classical
  unfold recovery_core.RecoveryEvidence.impl.try_certify_complete_domains
    SharedABTreeMap.Insts.CoreIterTraitsCollectIntoIteratorPairSharedAKSharedAVIter.into_iter
    recovery_core.RecoveryEvidence.impl.try_certify_complete_domains_loop
  simp only [bind_ok]
  refine generated_loop_preserves _
    (fun state : alloc.collections.btree.map.Iter cells.CellId (Finset Int) × domains.UcpValueFacts × Bool =>
      KnowledgeSound p context facts state.2.1 ∧ (∀ entry ∈ state.1, entry ∈ evidence.feasible))
    (CertifyPost p context facts) ?_ (evidence.feasible, values, false) ⟨sound, fun _ member => member⟩
  rintro ⟨current, nowValues, added⟩ ⟨nowSound, included⟩
  dsimp only at nowSound included ⊢
  unfold recovery_core.RecoveryEvidence.impl.try_certify_complete_domains_loop.body
  simp only [alloc.collections.btree.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next,
    bind_ok, uncurry_apply_pair]
  cases current with
  | nil => simpa [LoopOutcome, CertifyPost] using nowSound
  | cons head tail =>
      obtain ⟨cell, samples⟩ := head
      have member : (cell, samples) ∈ evidence.feasible := included _ List.mem_cons_self
      have cardFits : samples.card ≤ Usize.max := by
        have := room.2 _ member
        simpa using this
      have feasible : ∀ sample ∈ samples, Feasible context cell (fieldValue sample) :=
        fun sample inside => (samplesValid _ member sample inside).1
      obtain ⟨size, length, _⟩ := btree_card_length samples cardFits
      have tailIncluded : ∀ entry ∈ tail, entry ∈ evidence.feasible :=
        fun entry inside => included entry (List.mem_cons_of_mem _ inside)
      -- A ket generalt ag azonos folytatasa: domain-igazolas, majd a pontos ertek figyelese.
      have continuation : ∀ wasExact : Bool, WP.dspec (do
          let (r, values1) ← domains.UcpValueFacts.impl.try_mark_complete_from_samples nowValues cell samples (p : Int)
          match r with
          | core.result.Result.Ok _ =>
            if wasExact = true then Result.ok (ControlFlow.cont (tail, values1, added))
            else do
              let o2 ← domains.UcpValueFacts.impl.known_value values1 cell
              if (core.option.Option.is_some o2) = true then Result.ok (ControlFlow.cont (tail, values1, true))
              else Result.ok (ControlFlow.cont (tail, values1, added))
          | core.result.Result.Err error => do
            let ci ← cells.CellId.Insts.CoreCloneClone.clone cell
            Result.ok (ControlFlow.done (core.result.Result.Err
              (recovery_core.CertificationError.Domain ci error), values1)))
          (LoopOutcome (fun state : alloc.collections.btree.map.Iter cells.CellId (Finset Int) × domains.UcpValueFacts × Bool =>
            KnowledgeSound p context facts state.2.1 ∧ (∀ entry ∈ state.1, entry ∈ evidence.feasible))
            (CertifyPost p context facts)) := by
        intro wasExact
        apply WP.dspec_bind (certify_step_sound p positive bits context facts nowValues nowSound cell samples feasible)
        rintro ⟨result, next⟩ post
        cases result with
        | Err error => simp [cell_clone_correct, LoopOutcome, CertifyPost]
        | Ok unused =>
            have nextSound : KnowledgeSound p context facts next := by simpa using post
            simp only [uncurry_apply_pair]
            split
            · simpa [LoopOutcome] using And.intro nextSound tailIncluded
            · rw [rust_known_value_matches]
              simp only [bind_ok]
              split <;> simpa [LoopOutcome] using And.intro nextSound tailIncluded
      simp only [List.head?_cons, List.tail_cons, uncurry_apply_pair]
      rw [length]
      have readKnown := rust_known_value_matches nowValues cell
      simp only [bind_ok, readKnown, known_cell_correct]
      split
      · split
        · simp [cell_clone_correct, LoopOutcome, CertifyPost]
        · exact continuation _
      · exact continuation _

def NonUniqueLoopPost (context : OriginalContext cells.CellId F)
    (marks : std.collections.hash.set.HashSet cells.CellId std.hash.random.RandomState alloc.alloc.Global) : Prop :=
  NonUniqueSound context marks

theorem two_samples_prove_non_unique (positive : 1 < (p : Int))
    (context : OriginalContext cells.CellId F) (cell : cells.CellId) (samples : Finset Int)
    (valid : ∀ sample ∈ samples, Feasible context cell (fieldValue sample) ∧
      centeredRepresentative sample (p : Int) = sample)
    (two : 2 ≤ samples.card) :
    ∃ left right, context left ∧ context right ∧ left cell ≠ right cell := by
  obtain ⟨first, firstMember, second, secondMember, different⟩ := Finset.one_lt_card.mp two
  obtain ⟨⟨left, leftValid, leftValue⟩, firstCanonical⟩ := valid first firstMember
  obtain ⟨⟨right, rightValid, rightValue⟩, secondCanonical⟩ := valid second secondMember
  refine ⟨left, right, leftValid, rightValid, ?_⟩
  rw [leftValue, rightValue]
  intro same
  have residue := (field_eq_iff_residue (F := F) p first second).mp same
  have centered := (centered_eq_iff_same_residue (by omega : (0 : Int) < p)).mpr residue
  rw [firstCanonical, secondCanonical] at centered
  exact different centered

theorem rust_record_non_unique_sound (positive : 1 < (p : Int))
    (context : OriginalContext cells.CellId F) (evidence : recovery_core.RecoveryEvidence)
    (marks : std.collections.hash.set.HashSet cells.CellId std.hash.random.RandomState alloc.alloc.Global)
    (samplesValid : SamplesValid p context evidence.feasible) (room : Headroom evidence.feasible 0)
    (sound : NonUniqueSound context marks) :
    WP.dspec (recovery_core.RecoveryEvidence.impl.record_non_unique_cells evidence marks)
      (NonUniqueSound context) := by
  classical
  unfold recovery_core.RecoveryEvidence.impl.record_non_unique_cells
    SharedABTreeMap.Insts.CoreIterTraitsCollectIntoIteratorPairSharedAKSharedAVIter.into_iter
    recovery_core.RecoveryEvidence.impl.record_non_unique_cells_loop
  simp only [bind_ok]
  refine generated_loop_preserves _
    (fun state : alloc.collections.btree.map.Iter cells.CellId (Finset Int) ×
        std.collections.hash.set.HashSet cells.CellId std.hash.random.RandomState alloc.alloc.Global =>
      NonUniqueSound context state.2 ∧ ∀ entry ∈ state.1, entry ∈ evidence.feasible)
    (NonUniqueSound context) ?_ (evidence.feasible, marks) ⟨sound, fun _ member => member⟩
  rintro ⟨current, nowMarks⟩ ⟨nowSound, included⟩
  dsimp only at nowSound included ⊢
  unfold recovery_core.RecoveryEvidence.impl.record_non_unique_cells_loop.body
  simp only [alloc.collections.btree.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next,
    bind_ok, uncurry_apply_pair]
  cases current with
  | nil => simpa [LoopOutcome] using nowSound
  | cons head tail =>
      obtain ⟨cell, samples⟩ := head
      have member : (cell, samples) ∈ evidence.feasible := included _ List.mem_cons_self
      have cardFits : samples.card ≤ Usize.max := by simpa using room.2 _ member
      obtain ⟨size, length, sizeValue⟩ := btree_card_length samples cardFits
      have tailIncluded : ∀ entry ∈ tail, entry ∈ evidence.feasible :=
        fun entry inside => included entry (List.mem_cons_of_mem _ inside)
      simp only [List.head?_cons, List.tail_cons, uncurry_apply_pair]
      rw [length]
      simp only [bind_ok]
      split
      · rename_i atLeast
        have two : 2 ≤ samples.card := by
          rw [← sizeValue]
          simpa [UScalar.le_equiv] using atLeast
        have witness := two_samples_prove_non_unique p positive context cell samples
          (samplesValid _ member) two
        have nextSound : NonUniqueSound context (fun key => if key = cell then true else nowMarks key) := by
          intro key flagged
          by_cases same : key = cell
          · subst key
            exact witness
          · exact nowSound key (by simpa [same] using flagged)
        simpa [cell_clone_correct, std.collections.hash.set.HashSet.impl.insert, LoopOutcome] using
          And.intro nextSound tailIncluded
      · simpa [LoopOutcome] using And.intro nowSound tailIncluded

def FinishPost (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (evidence : recovery_core.RecoveryEvidence) :
    core.result.Result Bool recovery_core.CertificationError × domains.UcpValueFacts ×
      std.collections.hash.set.HashSet cells.CellId std.hash.random.RandomState alloc.alloc.Global -> Prop
  | (.Ok _, values, marks) => CoreSound p context facts values evidence marks
  | (.Err _, _, _) => True

-- A beolvasztas masodik fele: teljesseget igazol es a mintakbol non-unique cimket kepez.
theorem rust_finish_merge_sound (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (values : domains.UcpValueFacts) (evidence : recovery_core.RecoveryEvidence)
    (marks : std.collections.hash.set.HashSet cells.CellId std.hash.random.RandomState alloc.alloc.Global)
    (sound : CoreSound p context facts values evidence marks) :
    WP.dspec (recovery_core.finish_merge evidence facts values marks (p : Int))
      (FinishPost p context facts evidence) := by
  unfold recovery_core.finish_merge
  apply WP.dspec_bind (rust_certify_domains_sound p positive bits context facts values evidence
    sound.knowledge sound.samples sound.capacity)
  rintro ⟨result, next⟩ post
  cases result with
  | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, FinishPost]
  | Ok added =>
      have nextSound : KnowledgeSound p context facts next := by simpa [CertifyPost] using post
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
      apply WP.dspec_bind (rust_record_non_unique_sound p positive context evidence marks
        sound.samples sound.capacity sound.nonUnique)
      intro nextMarks marksSound
      have final : CoreSound p context facts next evidence nextMarks :=
        ⟨sound.satisfiable, nextSound, sound.samples, sound.capacity, marksSound⟩
      simpa [FinishPost] using final

end Core

end SourceProof
