import Proofs.FieldNormalization

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

def CanonicalDomain (modulus : Int) (domain : domains.UcpValueDomain) : Prop :=
  ∀ value ∈ DomainMembers domain, centeredRepresentative value modulus = value

def CanonicalStoredDomains (modulus : Int) (values : domains.UcpValueFacts) : Prop :=
  ∀ cell domain, values.domains cell = some domain -> CanonicalDomain modulus domain

def ModuloDomainContains (modulus : Int) (domain : domains.UcpValueDomain) (value : Int) : Prop :=
  ∃ representative ∈ DomainMembers domain, representative % modulus = value % modulus

def ModuloDomainsCover (context : OriginalContext cells.CellId Int) (modulus : Int)
    (values : domains.UcpValueFacts) : Prop :=
  ∀ cell domain, values.domains cell = some domain ->
    ∀ assignment, context assignment -> ModuloDomainContains modulus domain (assignment cell)

def CanonicalContext (context : OriginalContext cells.CellId Int) (modulus : Int) :
    OriginalContext cells.CellId Int :=
  fun assignment => ∃ original, context original ∧
    ∀ cell, assignment cell = centeredRepresentative (original cell) modulus

theorem canonical_domain_membership (modulus : Int) (positive : 0 < modulus)
    (domain : domains.UcpValueDomain) (canonical : CanonicalDomain modulus domain) (value : Int) :
    ModuloDomainContains modulus domain value ↔
      centeredRepresentative value modulus ∈ DomainMembers domain := by
  constructor
  · rintro ⟨representative, member, sameResidue⟩
    have same := (centered_eq_iff_same_residue positive).mpr sameResidue
    rw [canonical representative member] at same
    simpa [← same] using member
  · intro member
    exact ⟨_, member, centered_preserves_residue positive⟩

theorem canonical_context_covering (context : OriginalContext cells.CellId Int)
    (modulus : Int) (positive : 0 < modulus) (values : domains.UcpValueFacts)
    (covers : ModuloDomainsCover context modulus values)
    (canonical : CanonicalStoredDomains modulus values) :
    RepresentativeCover (CanonicalContext context modulus) values := by
  intro cell domain recorded assignment valid
  obtain ⟨original, originalValid, represented⟩ := valid
  rw [represented cell]
  exact (canonical_domain_membership modulus positive domain (canonical cell domain recorded) _).mp
    (covers cell domain recorded original originalValid)

theorem representative_covering_implies_modulo_covering
    (context : OriginalContext cells.CellId Int) (modulus : Int) (positive : 0 < modulus)
    (values : domains.UcpValueFacts)
    (covers : RepresentativeCover (CanonicalContext context modulus) values) :
    ModuloDomainsCover context modulus values := by
  intro cell domain recorded assignment valid
  let canonicalAssignment := fun cell => centeredRepresentative (assignment cell) modulus
  have member := covers cell domain recorded canonicalAssignment ⟨assignment, valid, fun _ => rfl⟩
  exact ⟨canonicalAssignment cell, member, centered_preserves_residue positive⟩

-- A kinyert normalizalo kod eredmenye bizonyitja a metszeshez szukseges kanonikussagot.
theorem rust_normalized_value_is_canonical (value modulus : Int) (valid : 1 < modulus)
    (fits : modulus.natAbs.size ≤ 4096) (result : Int)
    (returned : domains.normalize_field_value value modulus = .ok (some result)) :
    centeredRepresentative result modulus = result := by
  rw [rust_normalization_succeeds value modulus valid fits] at returned
  have same := Option.some.inj (Result.ok_injective returned)
  rw [← same]
  exact centered_idempotent (by omega)

theorem rust_mark_domain_preserves_modulo_coverage
    (context : OriginalContext cells.CellId Int) (modulus : Int) (positive : 0 < modulus)
    (before : domains.UcpValueFacts) (cell : cells.CellId) (domain : domains.UcpValueDomain)
    (covers : ModuloDomainsCover context modulus before)
    (canonical : CanonicalStoredDomains modulus before) (fits : StoredDomainsFit before)
    (incoming : ∀ assignment, context assignment -> ModuloDomainContains modulus domain (assignment cell))
    (incomingCanonical : CanonicalDomain modulus domain) (domainFits : DomainFits domain) :
    domains.UcpValueFacts.impl.mark_domain before cell domain ⦃ fun answer =>
      ModuloDomainsCover context modulus answer.2 ∧
      (∀ other, other ≠ cell -> answer.2.domains other = before.domains other) ∧
      (answer.1 = false -> answer.2 = before) ⦄ := by
  have representativeIncoming : ∀ assignment, CanonicalContext context modulus assignment ->
      assignment cell ∈ DomainMembers domain := by
    intro assignment valid
    obtain ⟨original, originalValid, represented⟩ := valid
    rw [represented cell]
    exact (canonical_domain_membership modulus positive domain incomingCanonical _).mp
      (incoming original originalValid)
  have checked := rust_mark_domain_preserves_covering (CanonicalContext context modulus)
    before cell domain (canonical_context_covering context modulus positive before covers canonical)
    fits representativeIncoming domainFits
  apply WP.spec_mono checked
  rintro ⟨changed, next⟩ ⟨nextCover, _, _, frame, progress⟩
  exact ⟨representative_covering_implies_modulo_covering context modulus positive next nextCover,
    frame, progress⟩

-- Ez a teljessegi kriterium specifikacioja, nem a mark_complete_from_samples torzsenek bizonyitasa.
-- A normalizalassal kepzett ket veges halmaz egyezesehez a reszhalmaz es elemszam elegendo.
theorem normalized_sample_cardinality_certifies_complete
    (context : OriginalContext cells.CellId Int) (cell : cells.CellId)
    (modulus : Int) (positive : 0 < modulus) (domain samples : Finset Int)
    (covers : ∀ assignment, context assignment ->
      ∃ value ∈ domain, value % modulus = assignment cell % modulus)
    (samplesSound : ∀ sample ∈ samples, ∃ assignment, context assignment ∧
      assignment cell % modulus = sample % modulus)
    (subset : samples.image (fun value => centeredRepresentative value modulus) ⊆
      domain.image (fun value => centeredRepresentative value modulus))
    (sameSize : (samples.image (fun value => centeredRepresentative value modulus)).card =
      (domain.image (fun value => centeredRepresentative value modulus)).card) :
    ∀ value, (∃ candidate ∈ domain, candidate % modulus = value % modulus) ↔
      ∃ assignment, context assignment ∧ assignment cell % modulus = value % modulus := by
  classical
  have equal := Finset.eq_of_subset_of_card_le subset (by omega)
  intro value
  constructor
  · rintro ⟨candidate, member, sameResidue⟩
    have normalizedMember : centeredRepresentative candidate modulus ∈
        samples.image (fun value => centeredRepresentative value modulus) := by
      rw [equal]
      exact Finset.mem_image.mpr ⟨candidate, member, rfl⟩
    obtain ⟨sample, sampleMember, sameCanonical⟩ := Finset.mem_image.mp normalizedMember
    obtain ⟨assignment, valid, sampleValue⟩ := samplesSound sample sampleMember
    have same := (centered_eq_iff_same_residue positive).mp sameCanonical
    exact ⟨assignment, valid, sampleValue.trans (same.trans sameResidue)⟩
  · rintro ⟨assignment, valid, assigned⟩
    obtain ⟨candidate, member, same⟩ := covers assignment valid
    exact ⟨candidate, member, same.trans assigned⟩

end SourceProof
