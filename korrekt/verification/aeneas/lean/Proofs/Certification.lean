import Proofs.FieldKnowledge
import Proofs.CertificationControl
import Proofs.RecoveryLoop

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! A teljessegjelolo Rust-fuggveny teljes bizonyitasa: mintak gyujtese, tartalmazas, elemszam, iras. -/

abbrev SampleClosure := domains.UcpValueFacts.try_mark_complete_from_samples.closure_1
abbrev SampleIterator :=
  core.iter.adapters.map.Map (alloc.collections.btree.set.Iter num_bigint.bigint.BigInt) SampleClosure

theorem collect_list_result (values acc : List Int) :
    collectIteratorList (collectionListInput Int).iteratorInst values acc =
      .ok (acc.reverse ++ values) := by
  induction values generalizing acc with
  | nil => rw [collectIteratorList]; simp [collectionListInput]
  | cons head tail ih =>
      rw [collectIteratorList]
      simp [collectionListInput] at ih ⊢
      simp [ih]

theorem collect_samples_result (modulus : Int) (valid : 1 < modulus)
    (fits : modulus.natAbs.size ≤ 4096) (values acc : List Int) :
    collectIteratorResults (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT
        num_bigint.bigint.BigInt)
        domains.UcpValueFacts.try_mark_complete_from_samples.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0BigIntResultBigIntCompleteDomainError)
      ⟨values, modulus⟩ acc =
      .ok (.Ok (acc.reverse ++ values.map (fun value => centeredRepresentative value modulus))) := by
  induction values generalizing acc with
  | nil =>
      rw [collectIteratorResults]
      simp [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator,
        core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next]
  | cons head tail ih =>
      rw [collectIteratorResults]
      simp [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator,
        core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
        domains.UcpValueFacts.try_mark_complete_from_samples.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0BigIntResultBigIntCompleteDomainError,
        domains.UcpValueFacts.try_mark_complete_from_samples.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0BigIntResultBigIntCompleteDomainError.call_mut,
        num_bigint.bigint.BigInt.Insts.CoreCloneClone.clone,
        rust_normalization_succeeds _ modulus valid fits, core.option.Option.ok_or] at ih ⊢
      simp [ih]

theorem contains_key_model (candidates : List (Int × Int)) (query : Int) :
    alloc.collections.btree.map.BTreeMap.impl.contains_key
      alloc.alloc.Global.Insts.CoreAllocAllocatorClone
      (core.borrow.Borrow.Blanket num_bigint.bigint.BigInt)
      num_bigint.bigint.BigInt.Insts.CoreCmpOrd
      num_bigint.bigint.BigInt.Insts.CoreCmpOrd candidates query =
      .ok (@decide (query ∈ candidates.map Prod.fst) (Classical.propDecidable _)) := by
  classical
  unfold alloc.collections.btree.map.BTreeMap.impl.contains_key
  congr 2
  simp [core.borrow.Borrow.Blanket.borrow]

theorem all_contained_result (candidates : List (Int × Int)) (values : List Int) :
    ∃ rest, core.iter.traits.iterator.Iterator.all.default
      (alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT
        num_bigint.bigint.BigInt)
      domains.UcpValueFacts.try_mark_complete_from_samples.closure_2.Insts.CoreOpsFunctionFnMutTupleShared0BigIntBool
      values candidates =
      .ok (@decide (∀ value ∈ values, value ∈ candidates.map Prod.fst) (Classical.propDecidable _), rest) := by
  classical
  induction values with
  | nil =>
      rw [core.iter.traits.iterator.Iterator.all.default]
      simp [alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next]
  | cons head tail ih =>
      rw [core.iter.traits.iterator.Iterator.all.default]
      simp only [alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
        List.head?_cons, List.tail_cons, bind_ok,
        domains.UcpValueFacts.try_mark_complete_from_samples.closure_2.Insts.CoreOpsFunctionFnMutTupleShared0BigIntBool,
        domains.UcpValueFacts.try_mark_complete_from_samples.closure_2.Insts.CoreOpsFunctionFnMutTupleShared0BigIntBool.call_mut,
        contains_key_model]
      by_cases member : head ∈ candidates.map Prod.fst
      · obtain ⟨rest, result⟩ := ih
        refine ⟨rest, ?_⟩
        simp only [alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT,
          domains.UcpValueFacts.try_mark_complete_from_samples.closure_2.Insts.CoreOpsFunctionFnMutTupleShared0BigIntBool] at result
        have present : ∃ x, (head, x) ∈ candidates := by simpa using member
        simp [present, result]
      · have absent : ¬ ∃ x, (head, x) ∈ candidates := by simpa using member
        exact ⟨tail, by simp [absent]⟩

theorem samples_collect_result (modulus : Int) (valid : 1 < modulus)
    (fits : modulus.natAbs.size ≤ 4096) (samples : List Int) :
    core.iter.traits.iterator.Iterator.collect.default
        (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT
        num_bigint.bigint.BigInt)
        domains.UcpValueFacts.try_mark_complete_from_samples.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0BigIntResultBigIntCompleteDomainError)
        (core.result.Result.Insts.CoreIterTraitsCollectFromIteratorResult
        domains.CompleteDomainError
        (alloc.collections.btree.set.BTreeSetTGlobal.Insts.CoreIterTraitsCollectFromIterator
        num_bigint.bigint.BigInt.Insts.CoreCmpOrd)) ⟨samples, modulus⟩ =
      .ok (.Ok (samples.map (fun value => centeredRepresentative value modulus)).toFinset) := by
  classical
  simp only [core.iter.traits.iterator.Iterator.collect.default,
    core.result.Result.Insts.CoreIterTraitsCollectFromIteratorResult,
    core.result.Result.Insts.CoreIterTraitsCollectFromIteratorResult.from_iter,
    core.iter.traits.collect.IntoIterator.Blanket,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_ok]
  have collected := collect_samples_result modulus valid fits samples []
  simp only [List.reverse_nil, List.nil_append] at collected
  rw [collected]
  simp only [bind_ok,
    alloc.collections.btree.set.BTreeSetTGlobal.Insts.CoreIterTraitsCollectFromIterator,
    alloc.collections.btree.set.BTreeSetTGlobal.Insts.CoreIterTraitsCollectFromIterator.from_iter,
    collectionListInput, bind_ok]
  have listed := collect_list_result (samples.map (fun value => centeredRepresentative value modulus)) []
  simp only [List.reverse_nil, List.nil_append, collectionListInput] at listed
  rw [listed]
  simp only [bind_ok]
  congr 2
  ext candidate
  simp

def CandidateInvariant (members : Finset Int)
    (state : alloc.vec.into_iter.IntoIter Int × List (Int × Int)) : Prop :=
  (state.2.map Prod.fst).Nodup ∧ (∀ entry ∈ state.2, entry.1 = entry.2 ∧ entry.1 ∈ members) ∧
    (state.2.map Prod.fst).toFinset ∪ state.1.val.toFinset = members

theorem remember_selected (candidates : List (Int × Int)) (value : Int)
    (same : ∀ entry ∈ candidates, entry.1 = entry.2) :
    rememberRepresentative candidates value value =
      (value, value) :: candidates.filter (fun pair => @decide (pair.1 ≠ value) (Classical.propDecidable _)) := by
  classical
  unfold rememberRepresentative
  cases found : candidates.find? (fun pair => @decide (pair.1 = value) (Classical.propDecidable _)) with
  | none => simp [found]
  | some entry =>
      have member := List.mem_of_find?_eq_some found
      have key : entry.1 = value := by simpa using List.find?_some found
      have equal : entry.2 = value := (same entry member).symm.trans key
      simp [found, equal]

theorem candidate_step (members : Finset Int) (candidates : List (Int × Int))
    (iter next : alloc.vec.into_iter.IntoIter Int) (value : Int) (tail : List Int)
    (invariant : CandidateInvariant members (iter, candidates))
    (current : iter.val = value :: tail) (advanced : next.val = tail) :
    CandidateInvariant members (next, rememberRepresentative candidates value value) := by
  classical
  obtain ⟨nodup, entries, union⟩ := invariant
  simp only at nodup entries union
  rw [remember_selected candidates value (fun entry member => (entries entry member).1)]
  have inMembers : value ∈ members := by
    rw [← union, current]
    simp
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro member
      obtain ⟨entry, inFilter, key⟩ := List.mem_map.mp member
      have := (List.mem_filter.mp inFilter).2
      simp [key] at this
    · exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) nodup
  · intro entry member
    rcases List.mem_cons.mp member with rfl | inFilter
    · exact ⟨rfl, inMembers⟩
    · exact entries entry (List.mem_filter.mp inFilter).1
  · ext candidate
    simp only at union ⊢
    have original := Finset.ext_iff.mp union candidate
    rw [current] at original
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons] at original
    simp only [advanced, Finset.mem_union, List.mem_toFinset, List.map_cons, List.mem_cons, List.mem_map,
      List.mem_filter] at original ⊢
    constructor
    · rintro ((rfl | ⟨entry, ⟨inList, _⟩, key⟩) | inTail)
      · exact inMembers
      · exact original.mp (Or.inl ⟨entry, inList, key⟩)
      · exact original.mp (Or.inr (Or.inr inTail))
    · intro member
      rcases original.mpr member with ⟨entry, inList, key⟩ | rfl | inTail
      · by_cases same : candidate = value
        · exact Or.inl (Or.inl same)
        · refine Or.inl (Or.inr ⟨entry, ⟨inList, ?_⟩, key⟩)
          simp [key, same]
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr inTail

section Main

variable {F : Type} [Field F] (p : Nat) [CharP F p]
  (surjective : Function.Surjective (fun value : Int => (value : F)))

def CertificationPost (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts) :
    core.result.Result Bool domains.CompleteDomainError × domains.UcpValueFacts -> Prop
  | (.Ok _, next) => KnowledgeSound p context facts next
  | (.Err _, _) => True

def CertificationLoopPost (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts) :
    (core.result.Result Bool domains.CompleteDomainError ×
      std.collections.hash.map.HashMap cells.CellId domains.UcpValueDomain
        std.hash.random.RandomState alloc.alloc.Global ×
      std.collections.hash.set.HashSet cells.CellId std.hash.random.RandomState alloc.alloc.Global) -> Prop
  | (result, hm, hs) => CertificationPost p context facts (result, ⟨hm, hs⟩)

theorem into_values_enumerates :
    Enumerates (core.iter.traits.collect.IntoIterator.Blanket
      (alloc.collections.btree.map.IntoValues.Insts.CoreIterTraitsIteratorIterator
        num_bigint.bigint.BigInt num_bigint.bigint.BigInt
        alloc.alloc.Global.Insts.CoreAllocAllocatorClone)).iteratorInst (fun state : List Int => state) := by
  intro state
  exact ⟨state.tail, rfl, rfl⟩

-- A kulcsok es az osszes kanonikus domainelem egybeesik, a mintak pedig ezek reszhalmazat adjak.
theorem certification_store_sound (positive : 1 < (p : Int))
    (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (values : domains.UcpValueFacts) (sound : KnowledgeSound p context facts values)
    (cell : cells.CellId) (domain : domains.UcpValueDomain)
    (recorded : values.domains cell = some domain) (samples : Finset Int)
    (feasible : ∀ sample ∈ samples, Feasible context cell (fieldValue sample))
    (replacement : domains.UcpValueDomain)
    (sameMembers : DomainMembers replacement = DomainMembers domain)
    (certified : DomainMembers domain ⊆ samples.image (fun value => centeredRepresentative value (p : Int)))
    (next : domains.UcpValueFacts) (nextDomain : next.domains cell = some replacement)
    (nextOther : ∀ other, other ≠ cell -> next.domains other = values.domains other)
    (nextFlag : ∀ other, other ≠ cell -> next.complete_domains other = values.complete_domains other) :
    KnowledgeSound p context facts next := by
  classical
  have cover := sound.covers cell domain recorded
  have replaced : ∀ stored, next.domains cell = some stored -> replacement = stored := by
    intro stored entry
    exact Option.some.inj (nextDomain.symm.trans entry)
  refine ⟨sound.known, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro other stored entry assignment valid
    by_cases same : other = cell
    · subst other
      have equal := replaced stored entry
      subst stored
      rw [domain_contains_iff, sameMembers, ← domain_contains_iff]
      exact cover assignment valid
    · exact sound.covers other stored ((nextOther other same).symm.trans entry) assignment valid
  · intro other stored entry
    by_cases same : other = cell
    · subst other
      have equal := replaced stored entry
      subst stored
      intro value member
      rw [sameMembers] at member
      exact sound.canonical _ domain recorded value member
    · exact sound.canonical other stored ((nextOther other same).symm.trans entry)
  · intro other stored entry
    by_cases same : other = cell
    · subst other
      have equal := replaced stored entry
      subst stored
      simp only [sameMembers]
      exact sound.small _ domain recorded
    · exact sound.small other stored ((nextOther other same).symm.trans entry)
  · intro other stored entry
    by_cases same : other = cell
    · subst other
      have equal := replaced stored entry
      subst stored
      intro value member
      rw [sameMembers] at member
      exact sound.fits _ domain recorded value member
    · exact sound.fits other stored ((nextOther other same).symm.trans entry)
  · intro other flagged
    by_cases same : other = cell
    · subst other
      exact ⟨replacement, nextDomain⟩
    · obtain ⟨stored, entry⟩ := sound.stored other ((nextFlag other same).symm.trans flagged)
      exact ⟨stored, (nextOther other same).trans entry⟩
  · intro other stored entry flagged value member
    by_cases same : other = cell
    · subst other
      have equal := replaced stored entry
      subst stored
      rw [domain_contains_iff, sameMembers] at member
      obtain ⟨representative, inDomain, assigned⟩ := member
      obtain ⟨sample, sampleMember, canonicalSample⟩ := Finset.mem_image.mp (certified inDomain)
      obtain ⟨assignment, valid, sampled⟩ := feasible sample sampleMember
      refine ⟨assignment, valid, sampled.trans ?_⟩
      rw [← assigned]
      apply (field_eq_iff_residue (F := F) p sample representative).mpr
      rw [← canonicalSample]
      exact (centered_preserves_residue (by omega)).symm
    · exact sound.flags other stored ((nextOther other same).symm.trans entry) ((nextFlag other same).symm.trans flagged) value member

theorem btree_map_length (candidates : List (Int × Int)) (small : candidates.length ≤ 257) :
    ∃ size : Usize, alloc.collections.btree.map.BTreeMap.impl.len
        alloc.alloc.Global.Insts.CoreAllocAllocatorClone candidates = .ok size ∧
      size.val = candidates.length := by
  have bounded : UScalar.check_bounds .Usize candidates.length := by scalar_tac
  simp only [alloc.collections.btree.map.BTreeMap.impl.len, UScalar.tryMk, UScalar.tryMkOpt,
    dite_eq_left bounded, Result.ofOption]
  exact ⟨_, rfl, UScalar.ofNatCore_val_eq _⟩

theorem certification_terminal_sound (positive : 1 < (p : Int))
    (bits : (p : Int).natAbs.size ≤ 4096)
    (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (values : domains.UcpValueFacts) (sound : KnowledgeSound p context facts values)
    (cell : cells.CellId) (domain : domains.UcpValueDomain)
    (recorded : values.domains cell = some domain) (samples : Finset Int)
    (feasible : ∀ sample ∈ samples, Feasible context cell (fieldValue sample))
    (iter : alloc.vec.into_iter.IntoIter Int) (candidates : List (Int × Int))
    (invariant : CandidateInvariant (DomainMembers domain) (iter, candidates))
    (finished : iter.val = []) :
    WP.dspec (domains.UcpValueFacts.impl.try_mark_complete_from_samples_loop.body values.domains
        values.complete_domains cell samples (p : Int) iter candidates)
      (LoopOutcome (CandidateInvariant (DomainMembers domain))
        (CertificationLoopPost p context facts)) := by
  classical
  obtain ⟨nodup, entries, union⟩ := invariant
  simp only [finished, List.toFinset_nil, Finset.union_empty] at union
  have read : alloc.vec.into_iter.IteratorIntoIter.next iter = .ok (none, iter) := by
    simp only [alloc.vec.into_iter.IteratorIntoIter.next]
    split
    · rfl
    · simp_all
  have keysLength : candidates.length = (DomainMembers domain).card := by
    rw [← union, List.toFinset_card_of_nodup nodup, List.length_map]
  have smallDomain : (DomainMembers domain).card ≤ 256 := sound.small cell domain recorded
  unfold domains.UcpValueFacts.impl.try_mark_complete_from_samples_loop.body
  rw [read, bind_ok]
  simp only [uncurry_apply_pair, alloc.collections.btree.set.BTreeSet.impl.iter,
    core.iter.traits.iterator.Iterator.map.default, bind_ok]
  rw [samples_collect_result (p : Int) positive bits]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  set collected := (samples.toList.map (fun value => centeredRepresentative value (p : Int))).toFinset with collectedDef
  obtain ⟨rest, contained⟩ := all_contained_result candidates collected.toList
  rw [contained, bind_ok]
  simp only [uncurry_apply_pair]
  split
  · rename_i containedFlag
    have allContained : ∀ value ∈ collected.toList, value ∈ candidates.map Prod.fst :=
      @of_decide_eq_true _ (Classical.propDecidable _) containedFlag
    have subset : collected ⊆ DomainMembers domain := by
      intro value member
      have := allContained value (Finset.mem_toList.mpr member)
      rw [← union]
      exact List.mem_toFinset.mpr this
    have smallCollected : collected.card ≤ 257 :=
      (Finset.card_le_card subset).trans (by omega)
    obtain ⟨leftSize, leftLength, leftValue⟩ := small_btree_length collected smallCollected
    obtain ⟨rightSize, rightLength, rightValue⟩ := btree_map_length candidates (by omega)
    rw [leftLength, rightLength]
    simp only [bind_ok]
    by_cases different : leftSize != rightSize
    · simpa [different, LoopOutcome, CertificationLoopPost, CertificationPost] using sound
    · have sameSize : collected.card = (DomainMembers domain).card := by
        have : leftSize.val = rightSize.val := by simpa using different
        rw [← leftValue, this, rightValue, keysLength]
      have equalSets : collected = DomainMembers domain :=
        Finset.eq_of_subset_of_card_le subset (by omega)
      simp only [different, Bool.false_eq_true, ↓reduceIte,
        alloc.collections.btree.set.BTreeSet.impl.is_empty, bind_ok]
      by_cases empty : collected.card = 0
      · simpa [empty, LoopOutcome, CertificationLoopPost, CertificationPost] using sound
      · simp only [empty, decide_false, Bool.false_eq_true, ↓reduceIte,
          alloc.collections.btree.map.BTreeMap.impl.into_values, bind_ok]
        have valuesEq : candidates.map Prod.snd = candidates.map Prod.fst :=
          List.map_congr_left (fun entry member => (entries entry member).1.symm)
        have representable : ∀ value ∈ candidates.map Prod.snd, value.natAbs.size < 2 ^ 64 := by
          intro value member
          rw [valuesEq] at member
          exact sound.fits cell domain recorded value (by rw [← union]; exact List.mem_toFinset.mpr member)
        have built := rust_finite_set_sound
          (core.iter.traits.collect.IntoIterator.Blanket
            (alloc.collections.btree.map.IntoValues.Insts.CoreIterTraitsIteratorIterator
              num_bigint.bigint.BigInt num_bigint.bigint.BigInt
              alloc.alloc.Global.Insts.CoreAllocAllocatorClone))
          (fun state : List Int => state) into_values_enumerates (candidates.map Prod.snd)
          (candidates.map Prod.snd) rfl representable
        apply WP.dspec_bind (WP.spec_dspec _ _ _ built)
        intro replacement checked
        cases replacement with
        | none =>
            simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, LoopOutcome, CertificationLoopPost, CertificationPost]
        | some replacement =>
            have sameMembers : DomainMembers replacement = DomainMembers domain := by
              rw [checked.1, valuesEq, union]
            have certified : DomainMembers domain ⊆
                samples.image (fun value => centeredRepresentative value (p : Int)) := by
              rw [← equalSets, collectedDef]
              intro value member
              obtain ⟨sample, inList, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
              exact Finset.mem_image.mpr ⟨sample, Finset.mem_toList.mp inList, equal⟩
            have stored := certification_store_sound p positive context facts values sound cell domain
              recorded samples feasible replacement sameMembers certified
            simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
              rust_domain_lookup, core.cmp.PartialEq.ne.trait_default, uncurry_apply_pair,
              core.cmp.PartialEq.ne.default, recorded, cell_clone_correct,
              core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.cmp.PartialEqShared,
              rust_domain_eq_matches, std.collections.hash.map.HashMap.impl.insert,
              std.collections.hash.set.HashSet.impl.insert]
            have final := stored ⟨Function.update values.domains cell (some replacement),
                fun key => if key = cell then true else values.complete_domains key⟩ (by simp)
              (by intro other different; simp [different]) (by intro other different; simp [different])
            split <;> simpa [rust_domain_eq_matches, LoopOutcome, CertificationLoopPost, CertificationPost] using final
  · simp [LoopOutcome, CertificationLoopPost, CertificationPost]

theorem iterator_step (iter : alloc.vec.into_iter.IntoIter Int) (value : Int) (tail : List Int)
    (current : iter.val = value :: tail) :
    ∃ next, alloc.vec.into_iter.IteratorIntoIter.next iter = .ok (some value, next) ∧ next.val = tail := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · simp_all
  · rename_i head rest same
    have equal : head :: rest = value :: tail := same.symm.trans current
    simp only [List.cons.injEq] at equal
    obtain ⟨rfl, rfl⟩ := equal
    exact ⟨_, rfl, alloc.vec.Vec.from_val _ _⟩

theorem certification_body_sound (positive : 1 < (p : Int)) (bits : (p : Int).natAbs.size ≤ 4096)
    (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (values : domains.UcpValueFacts) (sound : KnowledgeSound p context facts values)
    (cell : cells.CellId) (domain : domains.UcpValueDomain)
    (recorded : values.domains cell = some domain) (samples : Finset Int)
    (feasible : ∀ sample ∈ samples, Feasible context cell (fieldValue sample))
    (state : alloc.vec.into_iter.IntoIter Int × List (Int × Int))
    (invariant : CandidateInvariant (DomainMembers domain) state) :
    WP.dspec (domains.UcpValueFacts.impl.try_mark_complete_from_samples_loop.body values.domains
        values.complete_domains cell samples (p : Int) state.1 state.2)
      (LoopOutcome (CandidateInvariant (DomainMembers domain)) (CertificationLoopPost p context facts)) := by
  obtain ⟨iter, candidates⟩ := state
  cases current : iter.val with
  | nil =>
      exact certification_terminal_sound p positive bits context facts values sound cell domain recorded
        samples feasible iter candidates invariant current
  | cons value tail =>
      obtain ⟨next, read, advanced⟩ := iterator_step iter value tail current
      have member : value ∈ DomainMembers domain := by
        have union := invariant.2.2
        rw [← union]
        simp [current]
      have canonicalValue := sound.canonical cell domain recorded value member
      have stepped := rust_certification_step_uses_canonical_key values cell samples (p : Int) value
        positive bits iter next candidates read
      rw [canonicalValue] at stepped
      simp only [stepped]
      rw [show WP.dspec (Result.ok (ControlFlow.cont (next, rememberRepresentative candidates value value)))
        (LoopOutcome (CandidateInvariant (DomainMembers domain)) (CertificationLoopPost p context facts)) =
        CandidateInvariant (DomainMembers domain) (next, rememberRepresentative candidates value value) by
          simp [LoopOutcome]]
      exact candidate_step _ candidates iter next value tail invariant current advanced

theorem iter_to_list_result (values acc : List Int) :
    alloc.vec.FromIteratorVec.iterToList
      (core.iter.traits.collect.IntoIterator.Blanket
        (alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT
          num_bigint.bigint.BigInt)).iteratorInst values acc = .ok (acc.reverse ++ values) := by
  induction values generalizing acc with
  | nil =>
      rw [alloc.vec.FromIteratorVec.iterToList]
      simp [core.iter.traits.collect.IntoIterator.Blanket,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next]
  | cons head tail ih =>
      rw [alloc.vec.FromIteratorVec.iterToList]
      simp only [core.iter.traits.collect.IntoIterator.Blanket,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT,
        alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
        List.head?_cons, List.tail_cons, bind_ok, uncurry_apply_pair] at ih ⊢
      rw [ih]
      simp

theorem entries_list_result (domain : domains.UcpValueDomain) (small : (DomainMembers domain).card ≤ 256) :
    WP.spec (match domain with
        | domains.UcpValueDomain.Exact value =>
          alloc.vec.Vec.push (alloc.vec.Vec.new num_bigint.bigint.BigInt) value
        | domains.UcpValueDomain.FiniteSet values => do
          let i ← alloc.collections.btree.set.BTreeSet.impl.iter
            alloc.alloc.Global.Insts.CoreAllocAllocatorClone values
          core.iter.traits.iterator.Iterator.collect.default
            (alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT
            num_bigint.bigint.BigInt) (core.iter.traits.collect.FromIteratorVec
            num_bigint.bigint.BigInt) i)
      (fun entries : alloc.vec.Vec Int => entries.val.toFinset = DomainMembers domain) := by
  classical
  cases domain with
  | Exact value =>
      have bound : (alloc.vec.Vec.new Int).val.length < Usize.max := by
        simp only [alloc.vec.Vec.from_val, List.length_nil]
        scalar_tac
      apply WP.spec_mono (alloc.vec.Vec.push_spec (alloc.vec.Vec.new Int) value bound)
      intro entries pushed
      simp [pushed, DomainMembers]
  | FiniteSet values =>
      have fits : values.toList.length ≤ Usize.max := by
        simp only [Finset.length_toList]
        have : values.card ≤ 256 := small
        scalar_tac
      simp only [alloc.collections.btree.set.BTreeSet.impl.iter, bind_ok,
        core.iter.traits.iterator.Iterator.collect.default, core.iter.traits.collect.FromIteratorVec,
        alloc.vec.FromIteratorVec.from_iter, core.iter.traits.collect.IntoIterator.Blanket.into_iter]
      have listed := iter_to_list_result values.toList []
      simp only [List.reverse_nil, List.nil_append] at listed
      rw [listed]
      have cardFits : values.card ≤ Usize.max := by simpa using fits
      simp only [bind_ok, Finset.length_toList, cardFits, ↓reduceDIte]
      simp only [WP.spec_ok, alloc.vec.Vec.from_val]
      ext candidate
      simp [DomainMembers]

-- A teljessegjelolo Rust-fuggveny teljes hivasa megorzi a testbeli tudasinvarianst.
theorem rust_certification_preserves_knowledge (positive : 1 < (p : Int))
    (bits : (p : Int).natAbs.size ≤ 4096)
    (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (values : domains.UcpValueFacts) (sound : KnowledgeSound p context facts values)
    (cell : cells.CellId) (samples : Finset Int)
    (feasible : ∀ sample ∈ samples, Feasible context cell (fieldValue sample)) :
    WP.dspec (domains.UcpValueFacts.impl.try_mark_complete_from_samples values cell samples (p : Int))
      (CertificationPost p context facts) := by
  classical
  unfold domains.UcpValueFacts.impl.try_mark_complete_from_samples
  rw [rust_domain_lookup]
  simp only [bind_ok]
  cases recorded : values.domains cell with
  | none => simpa [CertificationPost] using sound
  | some domain =>
      apply WP.dspec_bind (WP.spec_dspec _ _ _ (entries_list_result domain (sound.small cell domain recorded)))
      intro entries members
      simp only [bind_ok, alloc.collections.btree.map.BTreeMapKVGlobal.impl.new]
      have started : WP.dspec (alloc.vec.IntoIteratorVec.into_iter entries)
          (fun iter : alloc.vec.into_iter.IntoIter Int => iter.val = entries.val) := by
        simp [alloc.vec.IntoIteratorVec.into_iter, alloc.vec.into_iter.IntoIter]
      apply WP.dspec_bind started
      intro iter sameEntries
      apply WP.dspec_bind (Pₘ := CertificationLoopPost p context facts)
      · unfold domains.UcpValueFacts.impl.try_mark_complete_from_samples_loop
        apply generated_loop_preserves _ (CandidateInvariant (DomainMembers domain))
          (CertificationLoopPost p context facts)
        · rintro ⟨current, candidates⟩ invariant
          exact certification_body_sound p positive bits context facts values sound cell domain recorded
            samples feasible (current, candidates) invariant
        · exact ⟨List.nodup_nil, by simp, by simpa [sameEntries] using members⟩
      · rintro ⟨result, hm, hs⟩ post
        simpa [CertificationLoopPost, uncurry_apply_pair] using post

end Main

end SourceProof
