import Proofs.DomainState

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000

def DomainMembers : domains.UcpValueDomain -> Finset Int
  | .Exact value => {value}
  | .FiniteSet values => values

def BuiltDomain (expected : Finset Int) : Option domains.UcpValueDomain -> Prop
  | none => True
  | some domain => DomainMembers domain = expected ∧ expected.Nonempty

-- A veges iterator minden elemet egyszer ad at, es csak a bejaras vegen all meg.
def Enumerates {Iter : Type} (iterator : core.iter.traits.iterator.Iterator Iter Int)
    (remaining : Iter -> List Int) : Prop :=
  ∀ state, ∃ next, iterator.next state = .ok ((remaining state).head?, next) ∧
    remaining next = (remaining state).tail

theorem int_btree_insert (members : Finset Int) (value : Int) :
    alloc.collections.btree.set.BTreeSet.impl.insert
      alloc.alloc.Global.Insts.CoreAllocAllocatorClone
      num_bigint.bigint.BigInt.Insts.CoreCmpOrd members value =
      .ok (decide (value ∉ members), insert value members) := by
  classical
  simp [alloc.collections.btree.set.BTreeSet.impl.insert]
  ext candidate
  simp

theorem int_btree_intersection (left right : Finset Int) :
    alloc.collections.btree.set.BTreeSet.impl.intersection
      alloc.alloc.Global.Insts.CoreAllocAllocatorClone
      num_bigint.bigint.BigInt.Insts.CoreCmpOrd left right = .ok (left ∩ right).toList := by
  classical
  unfold alloc.collections.btree.set.BTreeSet.impl.intersection
  congr 2
  ext candidate
  simp

theorem int_btree_contains (members : Finset Int) (value : Int) :
    alloc.collections.btree.set.BTreeSet.impl.contains
      alloc.alloc.Global.Insts.CoreAllocAllocatorClone
      (core.borrow.Borrow.Blanket Int) num_bigint.bigint.BigInt.Insts.CoreCmpOrd
      num_bigint.bigint.BigInt.Insts.CoreCmpOrd members value = .ok (decide (value ∈ members)) := by
  classical
  simp [alloc.collections.btree.set.BTreeSet.impl.contains,
    core.borrow.Borrow.Blanket.borrow]

theorem small_btree_length (members : Finset Int) (small : members.card ≤ 257) :
    ∃ size : Usize,
      alloc.collections.btree.set.BTreeSet.impl.len
        alloc.alloc.Global.Insts.CoreAllocAllocatorClone members = .ok size ∧ size.val = members.card := by
  have bounded : UScalar.check_bounds .Usize members.card := by scalar_tac
  simp only [alloc.collections.btree.set.BTreeSet.impl.len, UScalar.tryMk, UScalar.tryMkOpt,
    dite_eq_left bounded, Result.ofOption]
  exact ⟨_, rfl, UScalar.ofNatCore_val_eq _⟩

theorem finite_set_end_sound (members : Finset Int) (small : members.card ≤ 256) :
    (do
      let size ← alloc.collections.btree.set.BTreeSet.impl.len
        alloc.alloc.Global.Insts.CoreAllocAllocatorClone members
      match size.val with
      | 0 => .ok (none : Option domains.UcpValueDomain)
      | 1 =>
          let entries ← alloc.collections.btree.set.BTreeSet.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
            alloc.alloc.Global.Insts.CoreAllocAllocatorClone members
          let (entry, _) ← alloc.collections.btree.set.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
            alloc.alloc.Global.Insts.CoreAllocAllocatorClone entries
          let value ← core.option.Option.unwrap entry
          .ok (some (.Exact value))
      | _ => .ok (some (.FiniteSet members))) ⦃ BuiltDomain members ⦄ := by
  classical
  obtain ⟨size, length, same⟩ := small_btree_length members (by omega)
  rw [length]
  simp only [bind_ok, same]
  by_cases empty : members.card = 0
  · simp [empty, BuiltDomain]
  · by_cases singleton : members.card = 1
    · obtain ⟨value, equal⟩ := Finset.card_eq_one.mp singleton
      subst members
      simp [alloc.collections.btree.set.BTreeSet.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
        alloc.collections.btree.set.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
        core.option.Option.unwrap, BuiltDomain, DomainMembers]
    · simp [BuiltDomain, DomainMembers, Finset.nonempty_iff_ne_empty]
      exact Finset.nonempty_iff_ne_empty.mp (Finset.card_ne_zero.mp empty)

def DomainInventory {Iter : Type} (remaining : Iter -> List Int) (expected : Finset Int)
    (state : Iter × Finset Int) : Prop :=
  state.2.card ≤ 256 ∧
  (∀ value ∈ remaining state.1, value.natAbs.size < 2^64) ∧
  state.2 ∪ (remaining state.1).toFinset = expected

-- A ciklus a megvizsgalt es a meg hatralevo ertekek uniojat orzi meg.
-- A none megengedett korlatjelzes; some csak a teljes bemeneti halmazt jelolheti.
theorem rust_finite_set_loop_sound {Input Iter : Type}
    (iterator : core.iter.traits.collect.IntoIterator Input Int Iter)
    (remaining : Iter -> List Int) (lawful : Enumerates iterator.iteratorInst remaining)
    (expected : Finset Int) (state : Iter × Finset Int)
    (initial : DomainInventory remaining expected state) :
    domains.UcpValueDomain.impl.finite_set_loop iterator state.1 state.2 ⦃ BuiltDomain expected ⦄ := by
  classical
  unfold domains.UcpValueDomain.impl.finite_set_loop
  apply loop.spec_decr_nat (fun state : Iter × Finset Int => (remaining state.1).length)
    (DomainInventory remaining expected)
  · rintro ⟨current, members⟩ ⟨small, fits, inventory⟩
    dsimp only at small fits inventory
    obtain ⟨next, read, rest⟩ := lawful current
    change WP.spec (domains.UcpValueDomain.impl.finite_set_loop.body iterator current members) _
    unfold domains.UcpValueDomain.impl.finite_set_loop.body
    dsimp only
    rw [read]
    simp only [bind_ok]
    cases entries : remaining current with
    | nil =>
        have sameExpected : members = expected := by simpa [entries] using inventory
        rw [← sameExpected]
        simp only [List.head?_nil]
        obtain ⟨size, length, same⟩ := small_btree_length members (by omega)
        rw [length]
        simp only [bind_ok, same]
        by_cases empty : members.card = 0
        · simp [empty, BuiltDomain]
        · by_cases singleton : members.card = 1
          · obtain ⟨value, equal⟩ := Finset.card_eq_one.mp singleton
            rw [equal]
            simp [alloc.collections.btree.set.BTreeSet.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
              alloc.collections.btree.set.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
              core.option.Option.unwrap, BuiltDomain, DomainMembers]
          · simp [BuiltDomain, DomainMembers, Finset.nonempty_iff_ne_empty]
            exact Finset.nonempty_iff_ne_empty.mp (Finset.card_ne_zero.mp empty)
    | cons value tail =>
        simp only [List.head?_cons]
        change WP.spec (do
          let candidate ← domains.bounded_value value
          let branch ← core.option.Option.Insts.CoreOpsTry_traitTry.branch candidate
          match branch with
          | .Continue kept => do
              let (_, updated) ← alloc.collections.btree.set.BTreeSet.impl.insert
                alloc.alloc.Global.Insts.CoreAllocAllocatorClone
                num_bigint.bigint.BigInt.Insts.CoreCmpOrd members kept
              let count ← alloc.collections.btree.set.BTreeSet.impl.len
                alloc.alloc.Global.Insts.CoreAllocAllocatorClone updated
              if count > domains.MAX_FINITE_DOMAIN_SIZE
              then .ok (ControlFlow.done (none : Option domains.UcpValueDomain))
              else .ok (ControlFlow.cont (next, updated))
          | .Break residual => do
              let result ← core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
                domains.UcpValueDomain residual
              .ok (ControlFlow.done result)) _
        have representable : value.natAbs.size < 2^64 := fits value (by simp [entries])
        simp only [rust_bounded_value_matches]
        simp only [ite_eq_left representable, bind_ok]
        by_cases supported : value.natAbs.size ≤ 4096
        · simp only [ite_eq_left supported,
            core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
          simp only [int_btree_insert, bind_ok]
          change WP.spec (do
            let count ← alloc.collections.btree.set.BTreeSet.impl.len
              alloc.alloc.Global.Insts.CoreAllocAllocatorClone (insert value members)
            if count > domains.MAX_FINITE_DOMAIN_SIZE
            then .ok (ControlFlow.done (none : Option domains.UcpValueDomain))
            else .ok (ControlFlow.cont (next, insert value members))) _
          have nextSmall : (insert value members).card ≤ 257 :=
            (Finset.card_insert_le value members).trans (by omega)
          obtain ⟨size, length, same⟩ := small_btree_length (insert value members) nextSmall
          rw [length]
          simp only [bind_ok, domains.MAX_FINITE_DOMAIN_SIZE, UScalar.lt_equiv]
          split
          · simp [BuiltDomain]
          · rename_i continueSearch
            simp only [WP.spec_ok]
            have remainingNext : remaining next = tail := by simpa [entries] using rest
            refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
            · simpa [same] using Nat.le_of_not_gt continueSearch
            · intro candidate member
              apply fits candidate
              simp only [entries, List.mem_cons]
              exact Or.inr (by simpa [remainingNext] using member)
            · rw [remainingNext]
              simpa [entries, Finset.insert_union, Finset.union_insert] using inventory
            · simp [remainingNext]
        · simp [ite_eq_right supported,
            core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual, BuiltDomain]
  · exact initial

theorem rust_finite_set_sound {Input Iter : Type}
    (iterator : core.iter.traits.collect.IntoIterator Input Int Iter)
    (remaining : Iter -> List Int) (lawful : Enumerates iterator.iteratorInst remaining)
    (values : Input) (initial : Iter)
    (started : iterator.into_iter values = .ok initial)
    (fits : ∀ value ∈ remaining initial, value.natAbs.size < 2^64) :
    domains.UcpValueDomain.impl.finite_set iterator values ⦃ BuiltDomain (remaining initial).toFinset ⦄ := by
  unfold domains.UcpValueDomain.impl.finite_set
  rw [alloc.collections.btree.set.BTreeSetTGlobal.impl.new]
  simp only [bind_ok]
  rw [started]
  simp only [bind_ok]
  apply rust_finite_set_loop_sound iterator remaining lawful _ (initial, ∅)
  exact ⟨by simp, fits, by simp⟩

theorem rust_finite_set_from_btree_sound (values : Finset Int)
    (fits : ∀ value ∈ values, value.natAbs.size < 2^64) :
    domains.UcpValueDomain.impl.finite_set
      (alloc.collections.btree.set.BTreeSet.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter
        Int alloc.alloc.Global.Insts.CoreAllocAllocatorClone) values ⦃ BuiltDomain values ⦄ := by
  classical
  have lawful : Enumerates
      (alloc.collections.btree.set.BTreeSet.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter
        Int alloc.alloc.Global.Insts.CoreAllocAllocatorClone).iteratorInst id := by
    intro state
    exact ⟨state.tail, rfl, rfl⟩
  have valuesFit : ∀ value ∈ id values.toList, value.natAbs.size < 2^64 := by
    intro value member
    exact fits value (by simpa using member)
  apply WP.spec_mono (rust_finite_set_sound _ id lawful values values.toList rfl valuesFit)
  intro result valid
  simpa using valid

abbrev CloneIntersectionIterator := core.iter.adapters.map.Map (List Int)
  domains.UcpValueDomain.intersect.closure

abbrev cloneIntersectionTrait : core.iter.traits.collect.IntoIterator
    CloneIntersectionIterator Int CloneIntersectionIterator :=
  core.iter.traits.collect.IntoIterator.Blanket
    (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
      (alloc.collections.btree.set.Intersection.Insts.CoreIterTraitsIteratorIteratorSharedAT
        num_bigint.bigint.BigInt.Insts.CoreCmpOrd alloc.alloc.Global.Insts.CoreAllocAllocatorClone)
      domains.UcpValueDomain.intersect.closure.Insts.CoreOpsFunctionFnMutTupleShared0BigIntBigInt)

theorem clone_intersection_enumerates : Enumerates cloneIntersectionTrait.iteratorInst
    (fun state : CloneIntersectionIterator => state.iter) := by
  intro state
  refine ⟨⟨state.iter.tail, ()⟩, ?_, rfl⟩
  cases entries : state.iter <;>
    simp [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
      alloc.collections.btree.set.Intersection.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      domains.UcpValueDomain.intersect.closure.Insts.CoreOpsFunctionFnMutTupleShared0BigIntBigInt.call_mut,
      num_bigint.bigint.BigInt.Insts.CoreCloneClone.clone, entries]

theorem rust_intersection_set_sound (left right : Finset Int)
    (fits : ∀ value ∈ left, value.natAbs.size < 2^64) :
    domains.UcpValueDomain.impl.intersect (.FiniteSet left) (.FiniteSet right)
      ⦃ BuiltDomain (left ∩ right) ⦄ := by
  classical
  simp only [domains.UcpValueDomain.impl.intersect,
    int_btree_intersection, bind_ok,
    core.iter.traits.iterator.Iterator.map.default]
  have valuesFit : ∀ value ∈ (left ∩ right).toList, value.natAbs.size < 2^64 := by
    intro value member
    exact fits value (Finset.mem_inter.mp (by simpa using member)).1
  have checked := rust_finite_set_sound cloneIntersectionTrait (fun state => state.iter)
    clone_intersection_enumerates ⟨(left ∩ right).toList, ()⟩ ⟨(left ∩ right).toList, ()⟩ rfl valuesFit
  apply WP.spec_mono checked
  intro result valid
  simpa using valid

def DomainFits (domain : domains.UcpValueDomain) : Prop :=
  ∀ value ∈ DomainMembers domain, value.natAbs.size < 2^64

theorem rust_intersection_sound (left right : domains.UcpValueDomain) (fits : DomainFits left) :
    domains.UcpValueDomain.impl.intersect left right
      ⦃ BuiltDomain (DomainMembers left ∩ DomainMembers right) ⦄ := by
  classical
  cases left with
  | Exact value =>
      cases right with
      | Exact other =>
          by_cases equal : value = other
          · subst other
            simp [domains.UcpValueDomain.impl.intersect,
              num_bigint.bigint.BigInt.Insts.CoreCmpPartialEqBigInt.eq,
              num_bigint.bigint.BigInt.Insts.CoreCloneClone.clone, BuiltDomain, DomainMembers]
          · simp [domains.UcpValueDomain.impl.intersect,
              num_bigint.bigint.BigInt.Insts.CoreCmpPartialEqBigInt.eq, equal, BuiltDomain]
      | FiniteSet members =>
          by_cases member : value ∈ members
          · simp [domains.UcpValueDomain.impl.intersect, int_btree_contains, member,
              num_bigint.bigint.BigInt.Insts.CoreCloneClone.clone, BuiltDomain, DomainMembers]
          · simp [domains.UcpValueDomain.impl.intersect, int_btree_contains, member, BuiltDomain]
  | FiniteSet members =>
      cases right with
      | Exact value =>
          by_cases member : value ∈ members
          · simp [domains.UcpValueDomain.impl.intersect, int_btree_contains, member,
              num_bigint.bigint.BigInt.Insts.CoreCloneClone.clone, BuiltDomain, DomainMembers]
          · simp [domains.UcpValueDomain.impl.intersect, int_btree_contains, member, BuiltDomain]
      | FiniteSet other => exact rust_intersection_set_sound members other fits

end SourceProof
