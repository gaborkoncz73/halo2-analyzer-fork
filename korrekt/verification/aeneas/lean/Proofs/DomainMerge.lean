import Proofs.FiniteDomains

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000

-- A metszes egesz reprezentansokon tortenik. A testbeli hasznalathoz kozos
-- kanonikus reprezentansok szuksegesek; tetszoleges modulo-aliasok nem cserelhetok fel.
def RepresentativeCover (context : OriginalContext cells.CellId Int)
    (values : domains.UcpValueFacts) : Prop :=
  ∀ cell domain, values.domains cell = some domain ->
    ∀ assignment, context assignment -> assignment cell ∈ DomainMembers domain

def StoredDomainsFit (values : domains.UcpValueFacts) : Prop :=
  ∀ cell domain, values.domains cell = some domain -> DomainFits domain

def DomainMergePost (context : OriginalContext cells.CellId Int)
    (before : domains.UcpValueFacts) (cell : cells.CellId) : Bool × domains.UcpValueFacts -> Prop :=
  fun (changed, next) => RepresentativeCover context next ∧ StoredDomainsFit next ∧
    next.complete_domains = before.complete_domains ∧
    (∀ other, other ≠ cell -> next.domains other = before.domains other) ∧
    (changed = false -> next = before)

noncomputable def withDomain (before : domains.UcpValueFacts) (cell : cells.CellId)
    (domain : domains.UcpValueDomain) : domains.UcpValueFacts := by
  classical
  exact { before with domains := Function.update before.domains cell (some domain) }

theorem unchanged_domain_merge (context : OriginalContext cells.CellId Int)
    (before : domains.UcpValueFacts) (cell : cells.CellId)
    (covers : RepresentativeCover context before) (fits : StoredDomainsFit before) :
    DomainMergePost context before cell (false, before) :=
  ⟨covers, fits, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem stored_domain_merge (context : OriginalContext cells.CellId Int)
    (before : domains.UcpValueFacts) (cell : cells.CellId) (domain : domains.UcpValueDomain)
    (covers : RepresentativeCover context before) (fits : StoredDomainsFit before)
    (incoming : ∀ assignment, context assignment -> assignment cell ∈ DomainMembers domain)
    (domainFits : DomainFits domain) :
    DomainMergePost context before cell (true, withDomain before cell domain) := by
  classical
  refine ⟨?_, ?_, rfl, ?_, by simp⟩
  · intro other recorded entry assignment valid
    by_cases same : other = cell
    · subst other
      have equal : domain = recorded := by simpa [withDomain] using entry
      simpa [← equal] using incoming assignment valid
    · apply covers other recorded _ assignment valid
      simpa [withDomain, same] using entry
  · intro other recorded entry
    by_cases same : other = cell
    · subst other
      have equal : domain = recorded := by simpa [withDomain] using entry
      simpa [← equal] using domainFits
    · apply fits other recorded
      simpa [withDomain, same] using entry
  · intro other different
    simp [withDomain, different]

theorem rust_domain_eq_matches (left right : domains.UcpValueDomain) :
    domains.UcpValueDomain.Insts.CoreCmpPartialEqUcpValueDomain.eq left right =
      .ok (@decide (left = right) (Classical.propDecidable _)) := by
  classical
  cases left <;> cases right <;>
    simp [domains.UcpValueDomain.Insts.CoreCmpPartialEqUcpValueDomain.eq,
      domains.UcpValueDomain.read_discriminant,
      alloc.collections.btree.set.BTreeSet.Insts.CoreCmpPartialEqBTreeSet.eq,
      num_bigint.bigint.BigInt.Insts.CoreCmpPartialEqBigInt.eq]

-- Ez a bizonyitasbeli reszkifejezes a generalt mark_domain valtozatlan utolso blokkja.
-- A focel erre csak definicios egyenloseggel lep at, nem feltetelezett megfeleltetessel.
noncomputable def mergeDomainTail (before : domains.UcpValueFacts) (cell : cells.CellId)
    (domain : domains.UcpValueDomain) : Result (Bool × domains.UcpValueFacts) := do
  let previous ← std.collections.hash.map.HashMap.impl.get cells.CellId.Insts.CoreCmpEq
    cells.CellId.Insts.CoreHashHash
    std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
    (core.borrow.Borrow.Blanket cells.CellId) cells.CellId.Insts.CoreHashHash
    cells.CellId.Insts.CoreCmpEq before.domains cell
  match previous with
  | none =>
      let (_, updated) ← std.collections.hash.map.HashMap.impl.insert cells.CellId.Insts.CoreCmpEq
        cells.CellId.Insts.CoreHashHash
        std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher before.domains cell domain
      .ok (true, { before with domains := updated })
  | some existing =>
      let refined ← domains.UcpValueDomain.impl.intersect existing domain
      match refined with
      | none => .ok (false, before)
      | some intersection =>
          let equal ← domains.UcpValueDomain.Insts.CoreCmpPartialEqUcpValueDomain.eq intersection existing
          if equal then .ok (false, before) else
            let (_, updated) ← std.collections.hash.map.HashMap.impl.insert cells.CellId.Insts.CoreCmpEq
              cells.CellId.Insts.CoreHashHash
              std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
              before.domains cell intersection
            .ok (true, { before with domains := updated })

theorem rust_merge_domain_tail_sound (context : OriginalContext cells.CellId Int)
    (before : domains.UcpValueFacts) (cell : cells.CellId) (domain : domains.UcpValueDomain)
    (covers : RepresentativeCover context before) (fits : StoredDomainsFit before)
    (incoming : ∀ assignment, context assignment -> assignment cell ∈ DomainMembers domain)
    (domainFits : DomainFits domain) :
    mergeDomainTail before cell domain ⦃ DomainMergePost context before cell ⦄ := by
  classical
  unfold mergeDomainTail
  rw [rust_domain_lookup]
  simp only [bind_ok]
  cases entry : before.domains cell with
  | none =>
      simpa [std.collections.hash.map.HashMap.impl.insert, withDomain] using
        stored_domain_merge context before cell domain covers fits incoming domainFits
  | some existing =>
      apply WP.spec_bind (rust_intersection_sound existing domain (fits cell existing entry))
      intro refined checked
      cases refined with
      | none => simpa using unchanged_domain_merge context before cell covers fits
      | some intersection =>
          obtain ⟨members, nonempty⟩ := checked
          have intersectionCovers : ∀ assignment, context assignment ->
              assignment cell ∈ DomainMembers intersection := by
            intro assignment valid
            rw [members]
            exact Finset.mem_inter.mpr ⟨covers cell existing entry assignment valid, incoming assignment valid⟩
          have intersectionFits : DomainFits intersection := by
            intro value member
            rw [members] at member
            exact fits cell existing entry value (Finset.mem_inter.mp member).1
          simp only [rust_domain_eq_matches, bind_ok]
          split
          · simpa using unchanged_domain_merge context before cell covers fits
          · simpa [std.collections.hash.map.HashMap.impl.insert, withDomain] using
              stored_domain_merge context before cell intersection covers fits intersectionCovers intersectionFits

theorem rust_mark_domain_preserves_covering (context : OriginalContext cells.CellId Int)
    (before : domains.UcpValueFacts) (cell : cells.CellId) (domain : domains.UcpValueDomain)
    (covers : RepresentativeCover context before) (fits : StoredDomainsFit before)
    (incoming : ∀ assignment, context assignment -> assignment cell ∈ DomainMembers domain)
    (domainFits : DomainFits domain) :
    domains.UcpValueFacts.impl.mark_domain before cell domain
      ⦃ DomainMergePost context before cell ⦄ := by
  classical
  unfold domains.UcpValueFacts.impl.mark_domain
  rw [rust_complete_domain_matches]
  simp only [bind_ok]
  split
  · simpa using unchanged_domain_merge context before cell covers fits
  · cases domain with
    | Exact value =>
        change WP.spec (do
          let candidate ← domains.bounded_value value
          match candidate with
          | none => .ok (false, before)
          | some kept => mergeDomainTail before cell (.Exact kept)) _
        have representable : value.natAbs.size < 2^64 := domainFits value (by simp [DomainMembers])
        rw [rust_bounded_value_matches]
        simp only [ite_eq_left representable, bind_ok]
        by_cases supported : value.natAbs.size ≤ 4096
        · simp only [ite_eq_left supported]
          change WP.spec (mergeDomainTail before cell (.Exact value)) _
          exact rust_merge_domain_tail_sound context before cell _ covers fits incoming domainFits
        · simp only [ite_eq_right supported]
          simpa using unchanged_domain_merge context before cell covers fits
    | FiniteSet values =>
        apply WP.spec_bind (rust_finite_set_from_btree_sound values domainFits)
        intro normalized checked
        cases normalized with
        | none => simpa using unchanged_domain_merge context before cell covers fits
        | some normalized =>
            change WP.spec (mergeDomainTail before cell normalized) _
            have members := checked.1
            apply rust_merge_domain_tail_sound context before cell normalized covers fits
            · intro assignment valid
              rw [members]
              exact incoming assignment valid
            · intro value member
              rw [members] at member
              exact domainFits value member

theorem rust_complete_domain_is_immutable (before : domains.UcpValueFacts) (cell : cells.CellId)
    (domain : domains.UcpValueDomain) (complete : completeDomainTag before cell = true) :
    domains.UcpValueFacts.impl.mark_domain before cell domain = .ok (false, before) := by
  unfold domains.UcpValueFacts.impl.mark_domain
  rw [rust_complete_domain_matches]
  simp [complete]

def CertificatesStored (values : domains.UcpValueFacts) : Prop :=
  ∀ cell, values.complete_domains cell = true -> ∃ domain, values.domains cell = some domain

-- A beolvasztas nem keszit uj teljessegi igazolast, es a mar igazolt domaineket nem irja at.
theorem rust_mark_domain_preserves_certificates (context : OriginalContext cells.CellId Int)
    (before : domains.UcpValueFacts) (cell : cells.CellId) (domain : domains.UcpValueDomain)
    (covers : RepresentativeCover context before) (fits : StoredDomainsFit before)
    (incoming : ∀ assignment, context assignment -> assignment cell ∈ DomainMembers domain)
    (domainFits : DomainFits domain)
    (certificates : CertificatesStored before) (flags : CompletionFlagsSound context id before) :
    domains.UcpValueFacts.impl.mark_domain before cell domain ⦃ fun answer =>
      DomainMergePost context before cell answer ∧ CertificatesStored answer.2 ∧
      CompletionFlagsSound context id answer.2 ⦄ := by
  classical
  by_cases complete : completeDomainTag before cell = true
  · rw [rust_complete_domain_is_immutable before cell domain complete]
    simpa using And.intro (unchanged_domain_merge context before cell covers fits) ⟨certificates, flags⟩
  · have noFlag : before.complete_domains cell = false := by
      cases flag : before.complete_domains cell with
      | false => rfl
      | true =>
          obtain ⟨recorded, entry⟩ := certificates cell flag
          simp [completeDomainTag, entry, flag] at complete
    apply WP.spec_mono (rust_mark_domain_preserves_covering context before cell domain covers fits incoming domainFits)
    rintro ⟨changed, next⟩ post
    have originalPost := post
    obtain ⟨nextCovers, nextFits, sameFlags, frame, progress⟩ := post
    refine ⟨originalPost, ?_, ?_⟩
    · intro other flagged
      rw [sameFlags] at flagged
      have different : other ≠ cell := by
        intro same
        subst other
        rw [noFlag] at flagged
        cases flagged
      obtain ⟨recorded, entry⟩ := certificates other flagged
      exact ⟨recorded, (frame other different).trans entry⟩
    · intro other recorded entry flagged value member
      rw [sameFlags] at flagged
      have different : other ≠ cell := by
        intro same
        subst other
        rw [noFlag] at flagged
        cases flagged
      apply flags other recorded _ flagged value member
      exact (frame other different).symm.trans entry

end SourceProof
