import Proofs.RecoveryKnowledge

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

-- A tarolo konkret lekerdezese az identitas-Borrow mellett a megfelelo cellat olvassa.
theorem rust_domain_lookup (values : domains.UcpValueFacts) (cell : cells.CellId) :
    std.collections.hash.map.HashMap.impl.get cells.CellId.Insts.CoreCmpEq
      cells.CellId.Insts.CoreHashHash
      std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
      (core.borrow.Borrow.Blanket cells.CellId) cells.CellId.Insts.CoreHashHash
      cells.CellId.Insts.CoreCmpEq values.domains cell = .ok (values.domains cell) := by
  classical
  unfold std.collections.hash.map.HashMap.impl.get
  have existsKey : ∃ key, (core.borrow.Borrow.Blanket cells.CellId).borrow key = .ok cell :=
    ⟨cell, rfl⟩
  rw [dite_eq_left existsKey]
  have same : Classical.choose existsKey = cell :=
    Result.ok_injective (Classical.choose_spec existsKey)
  rw [same]

def domainSingletonTag : domains.UcpValueDomain -> Bool
  | .Exact _ => true
  | .FiniteSet _ => false

def domainExactValue : domains.UcpValueDomain -> Option Int
  | .Exact value => some value
  | .FiniteSet _ => none

def completeDomainTag (values : domains.UcpValueFacts) (cell : cells.CellId) : Bool :=
  match values.domains cell with
  | none => false
  | some domain => domainSingletonTag domain || values.complete_domains cell

theorem rust_domain_singleton_matches (domain : domains.UcpValueDomain) :
    domains.UcpValueDomain.impl.is_singleton domain = .ok (domainSingletonTag domain) := by
  cases domain <;> rfl

theorem rust_domain_exact_matches (domain : domains.UcpValueDomain) :
    domains.UcpValueDomain.impl.exact_value domain = .ok (domainExactValue domain) := by
  cases domain <;> rfl

theorem rust_domain_clone_preserves_values (domain : domains.UcpValueDomain) :
    domains.UcpValueDomain.Insts.CoreCloneClone.clone domain = .ok domain := by
  cases domain <;>
    simp [domains.UcpValueDomain.Insts.CoreCloneClone.clone,
      num_bigint.bigint.BigInt.Insts.CoreCloneClone.clone,
      alloc.collections.btree.set.BTreeSet.Insts.CoreCloneClone.clone]

theorem rust_known_value_matches (values : domains.UcpValueFacts) (cell : cells.CellId) :
    domains.UcpValueFacts.impl.known_value values cell =
      .ok ((values.domains cell).bind domainExactValue) := by
  rw [domains.UcpValueFacts.impl.known_value, rust_domain_lookup]
  cases entry : values.domains cell <;>
    simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,
      rust_domain_exact_matches]

-- A true jeloleshez tarolt domain kell; Exact eseten automatikus, egyebkent explicit igazolas kell.
theorem rust_complete_domain_matches (values : domains.UcpValueFacts) (cell : cells.CellId) :
    domains.UcpValueFacts.impl.domain_is_complete values cell = .ok (completeDomainTag values cell) := by
  classical
  rw [domains.UcpValueFacts.impl.domain_is_complete, rust_domain_lookup]
  cases entry : values.domains cell with
  | none => simp [completeDomainTag, entry, core.option.Option.is_some_and]
  | some domain =>
      cases domain <;>
        simp [completeDomainTag, entry, domainSingletonTag, core.option.Option.is_some_and,
          domains.UcpValueFacts.domain_is_complete.closure.Insts.CoreOpsFunctionFnOnceTupleShared0UcpValueDomainBool.call_once,
          domains.UcpValueDomain.impl.is_singleton, std.collections.hash.set.HashSet.impl.contains,
          core.borrow.Borrow.Blanket.borrow]

theorem rust_missing_domain_is_not_complete (values : domains.UcpValueFacts) (cell : cells.CellId)
    (missing : values.domains cell = none) :
    domains.UcpValueFacts.impl.domain_is_complete values cell = .ok false := by
  rw [rust_complete_domain_matches]
  simp [completeDomainTag, missing]

theorem rust_finite_domain_requires_certificate (values : domains.UcpValueFacts)
    (cell : cells.CellId) (members : Finset Int)
    (recorded : values.domains cell = some (.FiniteSet members)) :
    domains.UcpValueFacts.impl.domain_is_complete values cell = .ok (values.complete_domains cell) := by
  rw [rust_complete_domain_matches]
  simp [completeDomainTag, recorded, domainSingletonTag]

-- Az ertelmezes testbeli reprezentansokra is alkalmazhato; nem azonositja a mintat a lefedessel.
def DomainContains {Value : Type} (interpret : Int -> Value)
    (domain : domains.UcpValueDomain) (value : Value) : Prop :=
  match domain with
  | .Exact representative => value = interpret representative
  | .FiniteSet members => ∃ representative, representative ∈ members ∧ interpret representative = value

def DomainsCover {Value : Type} (context : OriginalContext cells.CellId Value)
    (interpret : Int -> Value) (values : domains.UcpValueFacts) : Prop :=
  ∀ cell domain, values.domains cell = some domain ->
    ∀ assignment, context assignment -> DomainContains interpret domain (assignment cell)

def CompletionFlagsSound {Value : Type} (context : OriginalContext cells.CellId Value)
    (interpret : Int -> Value) (values : domains.UcpValueFacts) : Prop :=
  ∀ cell domain, values.domains cell = some domain -> values.complete_domains cell = true ->
    ∀ value, DomainContains interpret domain value -> Feasible context cell value

-- A tenyleges Rust-lekerdezes eredmenyet kotelezo erteknek csak lefedes es SAT mellett tekinti.
theorem rust_known_value_is_forced {Value : Type} (context : OriginalContext cells.CellId Value)
    (interpret : Int -> Value) (values : domains.UcpValueFacts) (cell : cells.CellId) (value : Int)
    (satisfiable : ∃ assignment, context assignment) (covers : DomainsCover context interpret values)
    (returned : domains.UcpValueFacts.impl.known_value values cell = .ok (some value)) :
    Feasible context cell (interpret value) ∧
      ∀ assignment, context assignment -> assignment cell = interpret value := by
  rw [rust_known_value_matches] at returned
  have result := Result.ok_injective returned
  cases entry : values.domains cell with
  | none => simp [entry] at result
  | some domain =>
      cases domain with
      | FiniteSet _ => simp [entry, domainExactValue] at result
      | Exact representative =>
          have equal : representative = value := by simpa [entry, domainExactValue] using result
          subst representative
          have fixed := covers cell (.Exact value) entry
          obtain ⟨assignment, valid⟩ := satisfiable
          exact ⟨⟨assignment, valid, fixed assignment valid⟩, fixed⟩

theorem rust_complete_domain_is_exact {Value : Type} (context : OriginalContext cells.CellId Value)
    (interpret : Int -> Value) (values : domains.UcpValueFacts) (cell : cells.CellId)
    (satisfiable : ∃ assignment, context assignment) (covers : DomainsCover context interpret values)
    (flags : CompletionFlagsSound context interpret values)
    (returned : domains.UcpValueFacts.impl.domain_is_complete values cell = .ok true) :
    ∃ domain, values.domains cell = some domain ∧
      ∀ value, DomainContains interpret domain value ↔ Feasible context cell value := by
  rw [rust_complete_domain_matches] at returned
  have result := Result.ok_injective returned
  cases entry : values.domains cell with
  | none => simp [completeDomainTag, entry] at result
  | some domain =>
      refine ⟨domain, rfl, fun value => ⟨?_, ?_⟩⟩
      · intro member
        cases domain with
        | Exact representative =>
            obtain ⟨assignment, valid⟩ := satisfiable
            exact ⟨assignment, valid, (covers cell _ entry assignment valid).trans member.symm⟩
        | FiniteSet members =>
            have certified : values.complete_domains cell = true := by
              simpa [completeDomainTag, entry, domainSingletonTag] using result
            exact flags cell _ entry certified value member
      · rintro ⟨assignment, valid, assigned⟩
        rw [← assigned]
        exact covers cell domain entry assignment valid

def hypotheticalDomains (values : domains.UcpValueFacts) : domains.UcpValueFacts :=
  ⟨values.domains, fun _ => false⟩

theorem rust_hypothetical_matches (values : domains.UcpValueFacts) :
    domains.UcpValueFacts.impl.for_hypothetical_reasoning values = .ok (hypotheticalDomains values) := by
  simp [domains.UcpValueFacts.impl.for_hypothetical_reasoning,
    std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone,
    std.collections.hash.set.HashSetTRandomStateGlobal.impl.new, hypotheticalDomains]

theorem rust_hypothetical_preserves_known_values
    (values next : domains.UcpValueFacts) (cell : cells.CellId)
    (returned : domains.UcpValueFacts.impl.for_hypothetical_reasoning values = .ok next) :
    domains.UcpValueFacts.impl.known_value next cell = domains.UcpValueFacts.impl.known_value values cell := by
  rw [rust_hypothetical_matches] at returned
  have same := Result.ok_injective returned
  rw [← same, rust_known_value_matches, rust_known_value_matches]
  rfl

-- Az uj felteves leszuki a megoldashalmazt, ezert a lefedes megmarad, a megvalosithatosag nem oroklodik.
theorem rust_hypothetical_preserves_covering {Value : Type}
    (context strengthened : OriginalContext cells.CellId Value) (interpret : Int -> Value)
    (values next : domains.UcpValueFacts) (covers : DomainsCover context interpret values)
    (stronger : ∀ assignment, strengthened assignment -> context assignment)
    (returned : domains.UcpValueFacts.impl.for_hypothetical_reasoning values = .ok next) :
    DomainsCover strengthened interpret next ∧ ∀ cell, next.complete_domains cell = false := by
  rw [rust_hypothetical_matches] at returned
  have same := Result.ok_injective returned
  rw [← same]
  refine ⟨?_, fun _ => rfl⟩
  intro cell domain recorded assignment valid
  exact covers cell domain recorded assignment (stronger assignment valid)

theorem rust_hypothetical_finite_domain_is_not_complete
    (values next : domains.UcpValueFacts) (cell : cells.CellId) (members : Finset Int)
    (recorded : values.domains cell = some (.FiniteSet members))
    (returned : domains.UcpValueFacts.impl.for_hypothetical_reasoning values = .ok next) :
    domains.UcpValueFacts.impl.domain_is_complete next cell = .ok false := by
  rw [rust_hypothetical_matches] at returned
  have same := Result.ok_injective returned
  rw [← same, rust_complete_domain_matches]
  simp [completeDomainTag, hypotheticalDomains, recorded, domainSingletonTag]

theorem rust_hypothetical_complete_is_sound {Value : Type}
    (context strengthened : OriginalContext cells.CellId Value) (interpret : Int -> Value)
    (values next : domains.UcpValueFacts) (cell : cells.CellId)
    (covers : DomainsCover context interpret values)
    (stronger : ∀ assignment, strengthened assignment -> context assignment)
    (satisfiable : ∃ assignment, strengthened assignment)
    (returned : domains.UcpValueFacts.impl.for_hypothetical_reasoning values = .ok next)
    (complete : domains.UcpValueFacts.impl.domain_is_complete next cell = .ok true) :
    ∃ domain, next.domains cell = some domain ∧
      ∀ value, DomainContains interpret domain value ↔ Feasible strengthened cell value := by
  obtain ⟨nextCovers, cleared⟩ :=
    rust_hypothetical_preserves_covering context strengthened interpret values next covers stronger returned
  apply rust_complete_domain_is_exact strengthened interpret next cell satisfiable nextCovers _ complete
  intro key domain recorded certified
  have impossible := (cleared key).symm.trans certified
  cases impossible

-- Az elutasitott nagy egeszt nem alakitja kisebb, de hamis recovery-ertekke.
theorem rust_bounded_value_matches (value : Int) :
    domains.bounded_value value =
      if value.natAbs.size < 2^64
      then .ok (if value.natAbs.size ≤ 4096 then some value else none)
      else .fail .panic := by
  unfold domains.bounded_value num_bigint.bigint.BigInt.impl.bits
  split <;> simp_all [domains.MAX_VALUE_BITS, UScalar.le_equiv]
  split <;> rfl

theorem rust_bounded_value_accepts_supported (value : Int) (supported : value.natAbs.size ≤ 4096) :
    domains.bounded_value value = .ok (some value) := by
  rw [rust_bounded_value_matches]
  have representable : value.natAbs.size < 2^64 := by omega
  simp only [ite_eq_left representable, ite_eq_left supported]

theorem rust_bounded_value_rejects_oversized (value : Int)
    (representable : value.natAbs.size < 2^64) (oversized : 4096 < value.natAbs.size) :
    domains.bounded_value value = .ok none := by
  rw [rust_bounded_value_matches]
  simp only [ite_eq_left representable, ite_eq_right (Nat.not_le_of_lt oversized)]

theorem rust_bounded_value_never_truncates (value returned : Int)
    (accepted : domains.bounded_value value = .ok (some returned)) :
    returned = value ∧ value.natAbs.size ≤ 4096 := by
  rw [rust_bounded_value_matches] at accepted
  split at accepted
  · split at accepted
    · simp only [Result.ok.injEq, Option.some.injEq] at accepted
      exact ⟨accepted.symm, by assumption⟩
    · simp at accepted
  · simp at accepted

end SourceProof
