import UcpVerified.Types

open Aeneas Aeneas.Std ucp_verified

/-!
A standard konyvtari iteratorok es rendezett tarolok tagsagi modelljei.
A konkret fa-, allocator- es iterator-implementacio nem itt bizonyitott.
A modell a bejaras sorrendjet absztrahalja, a korai hibat es az allapotot nem.
-/

def collectionListInput (T : Type) :
    core.iter.traits.collect.IntoIterator (List T) T (List T) := {
  iteratorInst := { next := fun xs => .ok (xs.head?, xs.tail) }
  into_iter := fun xs => .ok xs
}

def collectIteratorList {T I : Type} (iterator : core.iter.traits.iterator.Iterator I T)
    (state : I) (accumulated : List T) : Result (List T) := do
  let (entry, next) ← iterator.next state
  match entry with
  | none => .ok accumulated.reverse
  | some value => collectIteratorList iterator next (value :: accumulated)
partial_fixpoint

def collectIteratorResults {T E I : Type}
    (iterator : core.iter.traits.iterator.Iterator I (core.result.Result T E))
    (state : I) (accumulated : List T) : Result (core.result.Result (List T) E) := do
  let (entry, next) ← iterator.next state
  match entry with
  | none => .ok (.Ok accumulated.reverse)
  | some (.Err error) => .ok (.Err error)
  | some (.Ok value) => collectIteratorResults iterator next (value :: accumulated)
partial_fixpoint

def core.result.Result.Insts.CoreIterTraitsCollectFromIteratorResult.from_iter
    {T E V I Iter : Type} (output : core.iter.traits.collect.FromIterator V T)
    (input : core.iter.traits.collect.IntoIterator I (core.result.Result T E) Iter)
    (values : I) : Result (core.result.Result V E) := do
  let initial ← input.into_iter values
  let entries ← collectIteratorResults input.iteratorInst initial []
  match entries with
  | .Err error => .ok (.Err error)
  | .Ok values =>
      let collected ← output.from_iter (collectionListInput T) values
      .ok (.Ok collected)

def core.iter.traits.iterator.Iterator.all.default
    {I F T : Type} (iterator : core.iter.traits.iterator.Iterator I T)
    (predicate : core.ops.function.FnMut F T Bool) (state : I) (function : F) : Result (Bool × I) := do
  let (entry, next) ← iterator.next state
  match entry with
  | none => .ok (true, next)
  | some value =>
      let (accepted, nextFunction) ← predicate.call_mut function value
      if accepted then Iterator.all.default iterator predicate next nextFunction
      else .ok (false, next)
partial_fixpoint

def core.option.Option.Insts.CoreCmpPartialEqOption.eq
    {T : Type} (equality : core.cmp.PartialEq T T) (left right : Option T) : Result Bool :=
  match left, right with
  | none, none => .ok true
  | some left, some right => equality.eq left right
  | _, _ => .ok false

def alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
    {T : Type} (remaining : alloc.collections.btree.set.Iter T) :
    Result (Option T × alloc.collections.btree.set.Iter T) := .ok (remaining.head?, remaining.tail)

noncomputable def alloc.collections.btree.set.BTreeSet.impl.iter
    {T A : Type} (_ : core.alloc.AllocatorClone A) (values : alloc.collections.btree.set.BTreeSet T A) :
    Result (alloc.collections.btree.set.Iter T) := .ok values.toList

def alloc.collections.btree.set.BTreeSet.impl.is_empty
    {T A : Type} (_ : core.alloc.AllocatorClone A) (values : alloc.collections.btree.set.BTreeSet T A) :
    Result Bool := .ok (decide (values.card = 0))

noncomputable def alloc.collections.btree.set.BTreeSetTGlobal.Insts.CoreIterTraitsCollectFromIterator.from_iter
    {T I Iter : Type} (_ : core.cmp.Ord T)
    (input : core.iter.traits.collect.IntoIterator I T Iter) (values : I) :
    Result (alloc.collections.btree.set.BTreeSet T alloc.alloc.Global) := by
  classical
  exact do
    let initial ← input.into_iter values
    let collected ← collectIteratorList input.iteratorInst initial []
    .ok collected.toFinset

def alloc.collections.btree.map.BTreeMapKVGlobal.impl.new (K V : Type) :
    Result (alloc.collections.btree.map.BTreeMap K V alloc.alloc.Global) := .ok []

def alloc.collections.btree.map.BTreeMap.impl.len
    {K V A : Type} (_ : core.alloc.AllocatorClone A)
    (entries : alloc.collections.btree.map.BTreeMap K V A) : Result Usize :=
  UScalar.tryMk .Usize entries.length

noncomputable def alloc.collections.btree.map.BTreeMap.impl.contains_key
    {K V A Q : Type} (_ : core.alloc.AllocatorClone A) (borrow : core.borrow.Borrow K Q)
    (_ : core.cmp.Ord K) (_ : core.cmp.Ord Q)
    (entries : alloc.collections.btree.map.BTreeMap K V A) (query : Q) : Result Bool := by
  classical
  exact .ok (decide (∃ entry ∈ entries, borrow.borrow entry.1 = .ok query))

def alloc.collections.btree.map.BTreeMap.impl.into_values
    {K V A : Type} (_ : core.alloc.AllocatorClone A)
    (entries : alloc.collections.btree.map.BTreeMap K V A) :
    Result (alloc.collections.btree.map.IntoValues K V A) := .ok (entries.map Prod.snd)

def alloc.collections.btree.map.IntoValues.Insts.CoreIterTraitsIteratorIterator.next
    {K V A : Type} (_ : core.alloc.AllocatorClone A)
    (remaining : alloc.collections.btree.map.IntoValues K V A) :
    Result (Option V × alloc.collections.btree.map.IntoValues K V A) :=
  .ok (remaining.head?, remaining.tail)

noncomputable def mapEntryBack {K V A : Type}
    (entry : alloc.collections.btree.map.entry.Entry K V A) : alloc.collections.btree.map.BTreeMap K V A := by
  classical
  exact match entry with
  | .Vacant (entries, _) => entries
  | .Occupied (entries, key, value) => (key, value) :: entries.filter (fun pair => decide (pair.1 ≠ key))

noncomputable def alloc.collections.btree.map.BTreeMap.impl.entry
    {K V A : Type} (_ : core.alloc.AllocatorClone A) (_ : core.cmp.Ord K)
    (entries : alloc.collections.btree.map.BTreeMap K V A) (key : K) :
    Result (alloc.collections.btree.map.entry.Entry K V A ×
      (alloc.collections.btree.map.entry.Entry K V A -> alloc.collections.btree.map.BTreeMap K V A)) := by
  classical
  exact .ok ((match entries.find? (fun pair => decide (pair.1 = key)) with
    | none => .Vacant (entries, key)
    | some (_, value) => .Occupied (entries, key, value)), mapEntryBack)

def alloc.collections.btree.map.entry.Entry.impl.or_insert_with
    {K V A F : Type} (_ : core.cmp.Ord K) (_ : core.alloc.AllocatorClone A)
    (closure : core.ops.function.FnOnce F Unit V)
    (entry : alloc.collections.btree.map.entry.Entry K V A) (function : F) :
    Result (V × (V -> alloc.collections.btree.map.entry.Entry K V A)) := do
  match entry with
  | .Occupied (entries, key, value) => .ok (value, fun value => .Occupied (entries, key, value))
  | .Vacant (entries, key) =>
      let value ← closure.call_once function ()
      .ok (value, fun value => .Occupied (entries, key, value))

def alloc.collections.btree.map.entry.Entry.impl.or_default
    {K V A : Type} (_ : core.cmp.Ord K) (defaultValue : core.default.Default V)
    (_ : core.alloc.AllocatorClone A)
    (entry : alloc.collections.btree.map.entry.Entry K V A) :
    Result (V × (V -> alloc.collections.btree.map.entry.Entry K V A)) := do
  match entry with
  | .Occupied (entries, key, value) => .ok (value, fun value => .Occupied (entries, key, value))
  | .Vacant (entries, key) =>
      let value ← defaultValue.default
      .ok (value, fun value => .Occupied (entries, key, value))

def alloc.collections.btree.set.BTreeSetTGlobal.Insts.CoreDefaultDefault.default (T : Type) :
    Result (alloc.collections.btree.set.BTreeSet T alloc.alloc.Global) := .ok ∅

/- A bejaras a lista tetszoleges kulcssorrendjere ervenyes; a bizonyitasok nem hasznaljak a sorrendet. -/
def SharedABTreeMap.Insts.CoreIterTraitsCollectIntoIteratorPairSharedAKSharedAVIter.into_iter
    {K V A : Type} (_ : core.alloc.AllocatorClone A)
    (entries : alloc.collections.btree.map.BTreeMap K V A) :
    Result (alloc.collections.btree.map.Iter K V) := .ok entries

def alloc.collections.btree.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next
    {K V : Type} (remaining : alloc.collections.btree.map.Iter K V) :
    Result (Option (K × V) × alloc.collections.btree.map.Iter K V) :=
  .ok (remaining.head?, remaining.tail)
