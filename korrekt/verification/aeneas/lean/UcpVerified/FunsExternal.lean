import UcpVerified.Types
import UcpVerified.CollectionModels

open Aeneas Aeneas.Std
open ucp_verified

set_option linter.dupNamespace false

/- A HashSet modellje a tagsagot, nem a hash-tabla fizikai mukodeset irja le. -/
def core.borrow.Borrow.Blanket.borrow {T : Type} (value : T) : Result T := .ok value

def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type} (value : Option T) :
    Result (core.ops.control_flow.ControlFlow (Option Never) T) :=
  match value with
  | some entry => .ok (.Continue entry)
  | none => .ok (.Break none)

def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
    (T : Type) (residual : Option Never) : Result (Option T) :=
  match residual with
  | none => .ok none
  | some impossible => nomatch impossible

def Usize.Insts.CoreHashHash.hash {H : Type} (_ : core.hash.Hasher H)
    (_ : Usize) (state : H) : Result H := .ok state
def I32.Insts.CoreHashHash.hash {H : Type} (_ : core.hash.Hasher H)
    (_ : I32) (state : H) : Result H := .ok state
def Isize.Insts.CoreHashHash.hash {H : Type} (_ : core.hash.Hasher H)
    (_ : Isize) (state : H) : Result H := .ok state

noncomputable def std.collections.hash.set.HashSet.impl.contains
    {T S A Q H : Type} (_ : core.cmp.Eq T) (_ : core.hash.Hash T)
    (_ : core.hash.BuildHasher S H) (borrow : core.borrow.Borrow T Q)
    (_ : core.hash.Hash Q) (_ : core.cmp.Eq Q)
    (members : std.collections.hash.set.HashSet T S A) (query : Q) : Result Bool :=
  .ok (@decide (Exists fun value => members value = true /\ borrow.borrow value = .ok query)
    (Classical.propDecidable _))

noncomputable def std.collections.hash.set.HashSet.impl.insert
    {T S A H : Type} (_ : core.cmp.Eq T) (_ : core.hash.Hash T)
    (_ : core.hash.BuildHasher S H)
    (members : std.collections.hash.set.HashSet T S A) (value : T) :
    Result (Bool × std.collections.hash.set.HashSet T S A) := by
  classical
  exact .ok (!members value, fun key => if key = value then true else members key)

def std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish
    (_ : std.hash.random.DefaultHasher) : Result U64 := .ok 0#u64
def std.hash.random.DefaultHasher.Insts.CoreHashHasher.write
    (state : std.hash.random.DefaultHasher) (_ : Slice U8) :
    Result std.hash.random.DefaultHasher := .ok state
def std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher
    (_ : std.hash.random.RandomState) : Result std.hash.random.DefaultHasher := .ok ()
def std.hash.random.RandomState.Insts.CoreCloneClone.clone
    (state : std.hash.random.RandomState) : Result std.hash.random.RandomState := .ok state

/- A kolcsonzeses lekerdezes a logikai kulcshoz tartozo bejegyzest olvassa.
   A konkret hivasok identitas-Borrow-t hasznalnak; a HashMap implementacioja nem bizonyitott. -/
noncomputable def std.collections.hash.map.HashMap.impl.get
    {K V S A Q H : Type} (_ : core.cmp.Eq K) (_ : core.hash.Hash K)
    (_ : core.hash.BuildHasher S H) (borrow : core.borrow.Borrow K Q)
    (_ : core.hash.Hash Q) (_ : core.cmp.Eq Q)
    (entries : std.collections.hash.map.HashMap K V S A) (query : Q) : Result (Option V) := by
  classical
  exact .ok (if matching : ∃ key, borrow.borrow key = .ok query
    then entries (Classical.choose matching) else none)

/- A klonozasi modellek ertekazonos masolatot adnak, a tarolas fizikai reszletei nelkul. -/
def std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone
    {K V S A : Type} (_ : core.clone.Clone K) (_ : core.clone.Clone V)
    (_ : core.clone.Clone S) (_ : core.clone.Clone A)
    (entries : std.collections.hash.map.HashMap K V S A) :
    Result (std.collections.hash.map.HashMap K V S A) := .ok entries

def alloc.collections.btree.set.BTreeSet.Insts.CoreCloneClone.clone
    {T A : Type} (_ : core.clone.Clone T) (_ : core.alloc.AllocatorClone A)
    (members : alloc.collections.btree.set.BTreeSet T A) :
    Result (alloc.collections.btree.set.BTreeSet T A) := .ok members

def std.collections.hash.set.HashSetTRandomStateGlobal.impl.new (T : Type) :
    Result (std.collections.hash.set.HashSet T std.hash.random.RandomState alloc.alloc.Global) :=
  .ok (fun _ => false)

/- A BigInt az egeszeket es a Rust elojeles maradekat modellezi. -/
def num_bigint.bigint.BigInt.Insts.CoreConvertFromI32.from (value : I32) :
    Result num_bigint.bigint.BigInt := .ok value.val
def Shared1BigInt.Insts.CoreOpsArithRemShared0BigIntBigInt.rem (left right : Int) :
    Result Int := if right = 0 then .fail .panic else .ok (Int.tmod left right)
def num_bigint.bigint.BigInt.Insts.CoreOpsArithRemShared0BigIntBigInt.rem (left right : Int) :
    Result Int := if right = 0 then .fail .panic else .ok (Int.tmod left right)
def num_bigint.bigint.BigInt.Insts.CoreOpsArithAddAssignShared0BigInt.add_assign (left right : Int) :
    Result Int := .ok (left + right)
def num_bigint.bigint.BigInt.Insts.CoreOpsArithSubAssignShared0BigInt.sub_assign (left right : Int) :
    Result Int := .ok (left - right)
def Shared0BigInt.Insts.CoreOpsArithDivBigIntBigInt.div (left right : Int) :
    Result Int := if right = 0 then .fail .panic else .ok (Int.tdiv left right)
def num_bigint.bigint.BigInt.Insts.CoreCmpPartialEqBigInt.eq (left right : Int) :
    Result Bool := .ok (decide (left = right))
def num_bigint.bigint.BigInt.Insts.CoreCmpPartialOrdBigInt.partial_cmp (left right : Int) :
    Result (Option Ordering) := .ok (some (compare left right))

def num_bigint.bigint.BigInt.Insts.CoreCloneClone.clone (value : Int) : Result Int := .ok value

/- A bits a nagysag bitjeit szamolja; a BigInt korlatlan Int-modelljeben a u64-visszateres is korlatos. -/
def num_bigint.bigint.BigInt.impl.bits (value : Int) : Result U64 :=
  if bounded : value.natAbs.size < 2^64
  then .ok (U64.ofNatCore value.natAbs.size bounded)
  else .fail .panic

noncomputable def std.collections.hash.map.HashMap.impl.insert
    {K V S A H : Type} (_ : core.cmp.Eq K) (_ : core.hash.Hash K)
    (_ : core.hash.BuildHasher S H)
    (entries : std.collections.hash.map.HashMap K V S A) (key : K) (value : V) :
    Result (Option V × std.collections.hash.map.HashMap K V S A) := by
  classical
  exact .ok (entries key, Function.update entries key (some value))

/- A fa es iterator modellje a tagsagot es a teljes veges bejarast koveti.
   Nem igazolja a standard konyvtar kiegyensulyozott fa-implementaciojat. -/
noncomputable def alloc.collections.btree.set.BTreeSet.Insts.CoreCmpPartialEqBTreeSet.eq
    {T A : Type} (_ : core.cmp.PartialEq T T) (_ : core.alloc.AllocatorClone A)
    (left right : alloc.collections.btree.set.BTreeSet T A) : Result Bool := by
  classical
  exact .ok (decide (left = right))

def alloc.collections.btree.set.BTreeSetTGlobal.impl.new (T : Type) :
    Result (alloc.collections.btree.set.BTreeSet T alloc.alloc.Global) := .ok ∅

noncomputable def alloc.collections.btree.set.BTreeSet.impl.contains
    {T A Q : Type} (_ : core.alloc.AllocatorClone A) (borrow : core.borrow.Borrow T Q)
    (_ : core.cmp.Ord T) (_ : core.cmp.Ord Q)
    (members : alloc.collections.btree.set.BTreeSet T A) (query : Q) : Result Bool := by
  classical
  exact .ok (decide (∃ value ∈ members, borrow.borrow value = .ok query))

noncomputable def alloc.collections.btree.set.BTreeSet.impl.insert
    {T A : Type} (_ : core.alloc.AllocatorClone A) (_ : core.cmp.Ord T)
    (members : alloc.collections.btree.set.BTreeSet T A) (value : T) :
    Result (Bool × alloc.collections.btree.set.BTreeSet T A) := by
  classical
  exact .ok (decide (value ∉ members), _root_.Insert.insert value members)

def alloc.collections.btree.set.BTreeSet.impl.len
    {T A : Type} (_ : core.alloc.AllocatorClone A)
    (members : alloc.collections.btree.set.BTreeSet T A) : Result Usize :=
  UScalar.tryMk .Usize members.card

noncomputable def alloc.collections.btree.set.BTreeSet.impl.intersection
    {T A : Type} (_ : core.alloc.AllocatorClone A) (_ : core.cmp.Ord T)
    (left right : alloc.collections.btree.set.BTreeSet T A) :
    Result (alloc.collections.btree.set.Intersection T A) := by
  classical
  exact .ok ((left ∩ right).toList)

def alloc.collections.btree.set.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    {T A : Type} (_ : core.alloc.AllocatorClone A)
    (remaining : alloc.collections.btree.set.IntoIter T A) :
    Result (Option T × alloc.collections.btree.set.IntoIter T A) :=
  .ok (remaining.head?, remaining.tail)

noncomputable def alloc.collections.btree.set.BTreeSet.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    {T A : Type} (_ : core.alloc.AllocatorClone A)
    (members : alloc.collections.btree.set.BTreeSet T A) :
    Result (alloc.collections.btree.set.IntoIter T A) := .ok members.toList

def alloc.collections.btree.set.Intersection.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
    {T A : Type} (_ : core.cmp.Ord T) (_ : core.alloc.AllocatorClone A)
    (remaining : alloc.collections.btree.set.Intersection T A) :
    Result (Option T × alloc.collections.btree.set.Intersection T A) :=
  .ok (remaining.head?, remaining.tail)

def num_bigint.bigint.BigInt.Insts.CoreCmpOrd.cmp (left right : Int) : Result Ordering :=
  .ok (compare left right)

def core.iter.traits.iterator.Iterator.map.default
    {I B F Item : Type} (_ : core.iter.traits.iterator.Iterator I Item)
    (_ : core.ops.function.FnMut F Item B) (iter : I) (function : F) :
    Result (core.iter.adapters.map.Map I F) := .ok ⟨iter, function⟩

def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
    {B I F Item : Type} (iterator : core.iter.traits.iterator.Iterator I Item)
    (function : core.ops.function.FnMut F Item B) (state : core.iter.adapters.map.Map I F) :
    Result (Option B × core.iter.adapters.map.Map I F) := do
  let (entry, next) ← iterator.next state.iter
  match entry with
  | none => .ok (none, ⟨next, state.f⟩)
  | some value =>
      let (mapped, nextFunction) ← function.call_mut state.f value
      .ok (some mapped, ⟨next, nextFunction⟩)
