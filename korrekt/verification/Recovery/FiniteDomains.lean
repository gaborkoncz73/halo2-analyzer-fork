import Recovery.Domains

/-!
A veges domaineket listakkal abrazolja; a sorrend es az ismetlodes nem szemantikai adat.
A korlatnal None eredmenyt ad, nem a lista egy reszet tekinti lefedo domainnek.
A Rust BTreeSet-normalizalasat nem modellezi, ezert az ismetlesek miatt korabban is feladhatja.
-/

namespace Recovery

variable {Value : Type}

def ListDomain (values : List Value) : ValueSet Value := fun value => value ∈ values

def boundedList (limit : Nat) (values : List Value) : Option (List Value) :=
  if values.length <= limit then some values else none

def cartesianValues (op : Value -> Value -> Value) (left right : List Value) : List Value :=
  left.flatMap (fun a => right.map (op a))

def boundedMap (limit : Nat) (op : Value -> Value) (values : List Value) : Option (List Value) :=
  boundedList limit (values.map op)

def boundedCombine (limit : Nat) (op : Value -> Value -> Value)
    (left right : List Value) : Option (List Value) :=
  if left.length * right.length <= limit then some (cartesianValues op left right) else none

theorem bounded_list_success {limit : Nat} {input output : List Value}
    (success : boundedList limit input = some output) : output = input := by
  unfold boundedList at success
  split at success
  · exact (Option.some.inj success).symm
  · cases success

theorem bounded_list_preserves_member {limit : Nat} {input output : List Value} {value : Value}
    (success : boundedList limit input = some output) (member : value ∈ input) :
    value ∈ output := by
  rw [bounded_list_success success]
  exact member

theorem bounded_list_overflow {limit : Nat} {values : List Value}
    (overflow : limit < values.length) : boundedList limit values = none := by
  simp [boundedList, Nat.not_le.mpr overflow]

theorem cartesian_preserves_pair {op : Value -> Value -> Value}
    {left right : List Value} {a b : Value} (hasA : a ∈ left) (hasB : b ∈ right) :
    op a b ∈ cartesianValues op left right := by
  exact List.mem_flatMap.mpr ⟨a, hasA, List.mem_map.mpr ⟨b, hasB, rfl⟩⟩

theorem bounded_map_preserves_member {limit : Nat} {op : Value -> Value}
    {input output : List Value} {value : Value}
    (success : boundedMap limit op input = some output) (member : value ∈ input) :
    op value ∈ output := by
  exact bounded_list_preserves_member success (List.mem_map.mpr ⟨value, member, rfl⟩)

theorem bounded_combine_preserves_pair {limit : Nat} {op : Value -> Value -> Value}
    {left right output : List Value} {a b : Value}
    (success : boundedCombine limit op left right = some output)
    (hasA : a ∈ left) (hasB : b ∈ right) : op a b ∈ output := by
  unfold boundedCombine at success
  split at success
  · cases success
    exact cartesian_preserves_pair hasA hasB
  · cases success

end Recovery
