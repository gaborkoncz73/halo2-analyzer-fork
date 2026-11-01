import Recovery.FiniteDomains

/-!
A rendezett n-esekre vonatkozo lookup-szabaly modellje, a `lookup.rs` `supported_rows` es `infer` logikaja szerint.
A sorszures megorzi az oszlopok kozotti korrelaciot; ismeretlen oszlopdomain nem zar ki sort.
A Rust-kod `value_inference.rs` fuggosegei miatt a rogzitett Aeneas-valtozat nem nyeri ki ezt a szabalyt.
-/

namespace Recovery

variable {Cell Value : Type}

def rowAllowed [DecidableEq Value] : List (Option (List Value)) -> List Value -> Bool
  | domain :: domains, value :: values =>
      (match domain with
        | none => true
        | some allowed => decide (value ∈ allowed)) && rowAllowed domains values
  | _, _ => true

def supportedRows [DecidableEq Value] (rows : List (List Value))
    (domains : List (Option (List Value))) : List (List Value) :=
  rows.filter (rowAllowed domains)

def columnValues (rows : List (List Value)) (index : Nat) : List Value :=
  rows.filterMap (fun row => row[index]?)

theorem row_allowed_of_covered [DecidableEq Value] (domains : List (Option (List Value))) (values : List Value)
    (covered : forall (index : Nat) (allowed : List Value) (value : Value), domains[index]? = some (some allowed) -> values[index]? = some value ->
      value ∈ allowed) : rowAllowed domains values = true := by
  induction domains generalizing values with
  | nil => cases values <;> rfl
  | cons domain rest ih =>
      cases values with
      | nil => rfl
      | cons value tail =>
          have tailAllowed := ih tail (fun index allowed entry inDomain inValues =>
            covered (index + 1) allowed entry (by simpa using inDomain) (by simpa using inValues))
          cases domain with
          | none => simp [rowAllowed, tailAllowed]
          | some allowed =>
              have member := covered 0 allowed value (by simp) (by simp)
              simp [rowAllowed, tailAllowed, member]

/-- Egy kielegito ertekadas tenyleges sora a szures utan is megmarad. -/
theorem actual_row_supported [DecidableEq Value] {ctx : Context Cell Value}
    {rows : List (List Value)} {domains : List (Option (List Value))}
    {inputs : Assignment Cell Value -> List Value}
    (table : forall assignment, ctx assignment -> inputs assignment ∈ rows)
    (domainsSound : forall assignment, ctx assignment -> forall (index : Nat) (allowed : List Value) (value : Value),
      domains[index]? = some (some allowed) -> (inputs assignment)[index]? = some value -> value ∈ allowed)
    (assignment : Assignment Cell Value) (valid : ctx assignment) :
    inputs assignment ∈ supportedRows rows domains := by
  exact List.mem_filter.mpr ⟨table assignment valid, row_allowed_of_covered _ _ (domainsSound assignment valid)⟩

/-- A megmaradt sorok oszlopvetulete lefedi az oszlop kifejezesenek erteket. -/
theorem lookup_column_covers [DecidableEq Value] {ctx : Context Cell Value}
    {rows : List (List Value)} {domains : List (Option (List Value))}
    {inputs : Assignment Cell Value -> List Value} {index : Nat} {column : Assignment Cell Value -> Value}
    (table : forall assignment, ctx assignment -> inputs assignment ∈ rows)
    (domainsSound : forall assignment, ctx assignment -> forall (index : Nat) (allowed : List Value) (value : Value),
      domains[index]? = some (some allowed) -> (inputs assignment)[index]? = some value -> value ∈ allowed)
    (columnValue : forall assignment, ctx assignment -> (inputs assignment)[index]? = some (column assignment)) :
    forall assignment, ctx assignment -> column assignment ∈ columnValues (supportedRows rows domains) index := by
  intro assignment valid
  exact List.mem_filterMap.mpr ⟨inputs assignment, actual_row_supported table domainsSound assignment valid,
    columnValue assignment valid⟩

theorem lookup_cell_covers [DecidableEq Value] {ctx : Context Cell Value}
    {rows : List (List Value)} {domains : List (Option (List Value))}
    {inputs : Assignment Cell Value -> List Value} {index : Nat} {cell : Cell}
    (table : forall assignment, ctx assignment -> inputs assignment ∈ rows)
    (domainsSound : forall assignment, ctx assignment -> forall (index : Nat) (allowed : List Value) (value : Value),
      domains[index]? = some (some allowed) -> (inputs assignment)[index]? = some value -> value ∈ allowed)
    (columnValue : forall assignment, ctx assignment -> (inputs assignment)[index]? = some (assignment cell)) :
    Covers ctx cell (ListDomain (columnValues (supportedRows rows domains) index)) :=
  lookup_column_covers table domainsSound columnValue

/-- Ha egyetlen tablasor sem maradt, a kontextus kielegithetetlen. -/
theorem lookup_empty_is_unsat [DecidableEq Value] {ctx : Context Cell Value}
    {rows : List (List Value)} {domains : List (Option (List Value))}
    {inputs : Assignment Cell Value -> List Value}
    (table : forall assignment, ctx assignment -> inputs assignment ∈ rows)
    (domainsSound : forall assignment, ctx assignment -> forall (index : Nat) (allowed : List Value) (value : Value),
      domains[index]? = some (some allowed) -> (inputs assignment)[index]? = some value -> value ∈ allowed)
    (empty : supportedRows rows domains = []) : Not (Satisfiable ctx) := by
  rintro ⟨assignment, valid⟩
  have member := actual_row_supported table domainsSound assignment valid
  rw [empty] at member
  cases member

-- A korrelacio megmarad: az elso oszlop ismerete a masodikat is szukiti.
example : columnValues (supportedRows [[0, 0], [1, 1]] [some [1], none]) 1 = [1] := by decide

-- Ismeretlen domain nem zar ki sort.
example : columnValues (supportedRows [[0, 0], [1, 1]] [none, none]) 1 = [0, 1] := by decide

end Recovery
