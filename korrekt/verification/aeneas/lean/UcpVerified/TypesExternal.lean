import Aeneas
import Mathlib.Data.Finset.Basic

/-!
A kulso konyvtarak szemantikai modelljei. Ezek nem a num-bigint es a
HashSet implementaciojanak bizonyitasai; a forrasbol kinyert sajat kod
helyessege e konyvtari szerzodesek mellett ertendo.
-/

abbrev std.collections.hash.set.HashSet (T _S _A : Type) : Type := T -> Bool
abbrev std.collections.hash.map.HashMap (K V _S _A : Type) : Type := K -> Option V
abbrev alloc.collections.btree.set.BTreeSet (T _A : Type) : Type := Finset T
abbrev alloc.collections.btree.set.IntoIter (T _A : Type) : Type := List T
abbrev alloc.collections.btree.set.Intersection (T _A : Type) : Type := List T
abbrev alloc.collections.btree.set.Iter (T : Type) : Type := List T
abbrev alloc.collections.btree.map.BTreeMap (K V _A : Type) : Type := List (K × V)
abbrev alloc.collections.btree.map.entry.VacantEntry (K V A : Type) : Type :=
  alloc.collections.btree.map.BTreeMap K V A × K
abbrev alloc.collections.btree.map.entry.OccupiedEntry (K V A : Type) : Type :=
  alloc.collections.btree.map.BTreeMap K V A × K × V
abbrev alloc.collections.btree.map.IntoValues (_K V _A : Type) : Type := List V
abbrev std.hash.random.RandomState : Type := Unit
abbrev std.hash.random.DefaultHasher : Type := Unit
abbrev num_bigint.bigint.BigInt : Type := Int
