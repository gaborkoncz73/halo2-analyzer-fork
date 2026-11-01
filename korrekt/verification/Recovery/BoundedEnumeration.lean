import Recovery.BaseConversion
import Recovery.Lookup

/-!
A UCP ket kovetkeztetesenek matematikai modellje: a korlatos felsorolas es a nagy tablak
helyierteki szurese. Mindketto csak olyan jelolteket zar ki, amelyek egyetlen megoldasban sem
fordulhatnak elo. A `zero_enumeration.rs` es `infer_table_digits` kodja nincs kinyerve.
-/

namespace Recovery

variable {Cell Value : Type}

/-- Egy ertekadas megfelel a felsorolt jeloltlistaknak, es az egyenlet nem zarja ki. -/
def Surviving (cells : List Cell) (candidates : Cell -> List Value)
    (rejected : Assignment Cell Value -> Prop) (assignment : Assignment Cell Value) : Prop :=
  (forall cell, cell ∈ cells -> assignment cell ∈ candidates cell) /\ Not (rejected assignment)

/-- A megmaradt ertekadasok cellankenti vetulete. -/
def KeptValues (cells : List Cell) (candidates : Cell -> List Value)
    (rejected : Assignment Cell Value -> Prop) (cell : Cell) : ValueSet Value :=
  fun value => exists assignment, Surviving cells candidates rejected assignment /\ assignment cell = value

/-- A felsorolas vetulete lefedo, ha a jeloltek lefedok, es csak hamis ertekadast utasit el. -/
theorem enumeration_keeps_every_solution {ctx : Context Cell Value} {cells : List Cell}
    {candidates : Cell -> List Value} {rejected : Assignment Cell Value -> Prop}
    (covers : forall cell, cell ∈ cells -> Covers ctx cell (ListDomain (candidates cell)))
    (sound : forall assignment, ctx assignment -> Not (rejected assignment)) (cell : Cell) :
    Covers ctx cell (KeptValues cells candidates rejected cell) := by
  intro assignment valid
  exact ⟨assignment, ⟨fun other member => covers other member assignment valid,
    sound assignment valid⟩, rfl⟩

/-- A szuro nem csonkitja a szuksegtelen cellakat: valodi megoldas sosem esik ki. -/
theorem enumeration_solution_survives {ctx : Context Cell Value} {cells : List Cell}
    {candidates : Cell -> List Value} {rejected : Assignment Cell Value -> Prop}
    (covers : forall cell, cell ∈ cells -> Covers ctx cell (ListDomain (candidates cell)))
    (sound : forall assignment, ctx assignment -> Not (rejected assignment))
    (assignment : Assignment Cell Value) (valid : ctx assignment) :
    Surviving cells candidates rejected assignment :=
  ⟨fun other member => covers other member assignment valid, sound assignment valid⟩

/-- A tablaba tartozo csomagolt ertek szamjegyei a domainekben vannak, igy a szures megtartja a sort. -/
theorem table_filter_keeps_actual_row {ctx : Context Cell Nat} {packed : Cell}
    {digits : List Cell} {base : Nat} {table : List Nat}
    (allowed : Nat -> Bool)
    (positive : 0 < base)
    (bounded : forall assignment, ctx assignment -> DigitsBounded base (digits.map assignment))
    (equation : forall assignment, ctx assignment ->
      packDigits base (digits.map assignment) = assignment packed)
    (member : forall assignment, ctx assignment -> assignment packed ∈ table)
    (compatible : forall assignment, ctx assignment -> allowed (assignment packed) = true) :
    forall assignment, ctx assignment ->
      assignment packed ∈ table.filter allowed /\
        unpackDigits base digits.length (assignment packed) = some (digits.map assignment) := by
  intro assignment valid
  refine ⟨List.mem_filter.mpr ⟨member assignment valid, compatible assignment valid⟩, ?_⟩
  have decoded := unpack_packed_digits positive (digits.map assignment) (bounded assignment valid)
  simpa only [List.length_map, equation assignment valid] using decoded

end Recovery
