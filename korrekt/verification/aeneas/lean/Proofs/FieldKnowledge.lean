import Proofs.CanonicalMerge
import Proofs.KnowledgeUpdate
import Proofs.DomainMerge

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
A tarolt egesz reprezentansokat a kapcsolas testelemeihez koti.
A `surjective` feltetel minden prim testre teljesul, peldaul `ZMod p`-re es a Halo2-testekre.
-/

section Bridge

variable {F : Type} [Field F]

abbrev fieldValue (value : Int) : F := (value : F)

theorem domain_contains_iff (domain : domains.UcpValueDomain) (value : F) :
    DomainContains fieldValue domain value ↔ ∃ representative ∈ DomainMembers domain,
      fieldValue representative = value := by
  cases domain with
  | Exact representative =>
      simp only [DomainContains, DomainMembers, Finset.mem_singleton, exists_eq_left]
      exact eq_comm
  | FiniteSet members => simp only [DomainContains, DomainMembers]

variable (p : Nat) [CharP F p]

theorem field_eq_iff_residue (left right : Int) :
    fieldValue (F := F) left = fieldValue right ↔ left % (p : Int) = right % (p : Int) :=
  CharP.intCast_eq_intCast F p

variable (surjective : Function.Surjective (fun value : Int => (value : F)))

include surjective in
theorem lift_cast (value : F) : ((Function.surjInv surjective value : Int) : F) = value :=
  Function.surjInv_eq surjective value

noncomputable def canonicalOf (value : F) : Int :=
  centeredRepresentative (Function.surjInv surjective value) (p : Int)

theorem canonical_cast (positive : 1 < (p : Int)) (value : F) :
    fieldValue (F := F) (canonicalOf p surjective value) = value := by
  have residue := centered_preserves_residue (value := Function.surjInv surjective value)
    (modulus := (p : Int)) (by omega)
  have same := (field_eq_iff_residue (F := F) p _ _).mpr residue
  exact same.trans (lift_cast surjective value)

theorem canonical_of_is_canonical (positive : 1 < (p : Int)) (value : F) :
    centeredRepresentative (canonicalOf p surjective value) (p : Int) = canonicalOf p surjective value :=
  centered_idempotent (by omega)

theorem canonical_member_iff (positive : 1 < (p : Int)) (domain : domains.UcpValueDomain)
    (canonical : CanonicalDomain (p : Int) domain) (value : F) :
    DomainContains fieldValue domain value ↔ canonicalOf p surjective value ∈ DomainMembers domain := by
  rw [domain_contains_iff]
  constructor
  · rintro ⟨representative, member, same⟩
    have residue : representative % (p : Int) = Function.surjInv surjective value % (p : Int) :=
      (field_eq_iff_residue (F := F) p _ _).mp (same.trans (lift_cast surjective value).symm)
    have centered := (centered_eq_iff_same_residue (by omega : (0 : Int) < p)).mpr residue
    rw [canonical representative member] at centered
    rw [canonicalOf, ← centered]
    exact member
  · intro member
    exact ⟨_, member, canonical_cast p surjective positive value⟩

/-- A testbeli kontextus kanonikus reprezentansokra vetitve; ezen dolgozik a Rust-metszes. -/
def representedContext (context : OriginalContext cells.CellId F) : OriginalContext cells.CellId Int :=
  fun assignment => ∃ original, context original ∧
    ∀ cell, assignment cell = canonicalOf p surjective (original cell)

theorem field_cover_to_represented (context : OriginalContext cells.CellId F)
    (positive : 1 < (p : Int)) (values : domains.UcpValueFacts)
    (covers : DomainsCover context fieldValue values)
    (canonical : CanonicalStoredDomains (p : Int) values) :
    RepresentativeCover (representedContext p surjective context) values := by
  rintro cell domain recorded assignment ⟨original, valid, represented⟩
  rw [represented cell]
  exact (canonical_member_iff p surjective positive domain (canonical cell domain recorded) _).mp
    (covers cell domain recorded original valid)

theorem represented_to_field_cover (context : OriginalContext cells.CellId F)
    (positive : 1 < (p : Int)) (values : domains.UcpValueFacts)
    (covers : RepresentativeCover (representedContext p surjective context) values) :
    DomainsCover context fieldValue values := by
  intro cell domain recorded assignment valid
  rw [domain_contains_iff]
  exact ⟨_, covers cell domain recorded _ ⟨assignment, valid, fun _ => rfl⟩,
    canonical_cast p surjective positive _⟩

end Bridge

/-! A tarolt domainek reszhalmazra zart tulajdonsagai a beolvasztas alatt megmaradnak. -/

def StoredSatisfy (property : Finset Int -> Prop) (values : domains.UcpValueFacts) : Prop :=
  ∀ cell domain, values.domains cell = some domain -> property (DomainMembers domain)

def Antitone (property : Finset Int -> Prop) : Prop :=
  ∀ small large, small ⊆ large -> property large -> property small

theorem stored_after_insert (property : Finset Int -> Prop) (before : domains.UcpValueFacts)
    (cell : cells.CellId) (domain : domains.UcpValueDomain)
    (stored : StoredSatisfy property before) (incoming : property (DomainMembers domain)) :
    StoredSatisfy property (withDomain before cell domain) := by
  classical
  intro other recorded entry
  by_cases same : other = cell
  · subst other
    have equal : domain = recorded := by simpa [withDomain] using entry
    simpa [← equal] using incoming
  · exact stored other recorded (by simpa [withDomain, same] using entry)

theorem merge_tail_satisfies (property : Finset Int -> Prop) (antitone : Antitone property)
    (before : domains.UcpValueFacts) (cell : cells.CellId) (domain : domains.UcpValueDomain)
    (stored : StoredSatisfy property before) (fits : StoredDomainsFit before)
    (incoming : property (DomainMembers domain)) :
    mergeDomainTail before cell domain ⦃ fun answer => StoredSatisfy property answer.2 ⦄ := by
  classical
  unfold mergeDomainTail
  rw [rust_domain_lookup]
  simp only [bind_ok]
  cases entry : before.domains cell with
  | none =>
      simpa [std.collections.hash.map.HashMap.impl.insert, withDomain] using
        stored_after_insert property before cell domain stored incoming
  | some existing =>
      apply WP.spec_bind (rust_intersection_sound existing domain (fits cell existing entry))
      intro refined checked
      cases refined with
      | none => simpa using stored
      | some intersection =>
          obtain ⟨members, _⟩ := checked
          have smaller : property (DomainMembers intersection) := by
            rw [members]
            exact antitone _ _ Finset.inter_subset_left (stored cell existing entry)
          simp only [rust_domain_eq_matches, bind_ok]
          split
          · simpa using stored
          · simpa [std.collections.hash.map.HashMap.impl.insert, withDomain] using
              stored_after_insert property before cell intersection stored smaller

theorem rust_mark_domain_preserves_stored_property (property : Finset Int -> Prop)
    (antitone : Antitone property) (before : domains.UcpValueFacts) (cell : cells.CellId)
    (domain : domains.UcpValueDomain) (stored : StoredSatisfy property before)
    (fits : StoredDomainsFit before) (incoming : property (DomainMembers domain))
    (domainFits : DomainFits domain) :
    domains.UcpValueFacts.impl.mark_domain before cell domain
      ⦃ fun answer => StoredSatisfy property answer.2 ⦄ := by
  classical
  unfold domains.UcpValueFacts.impl.mark_domain
  rw [rust_complete_domain_matches]
  simp only [bind_ok]
  split
  · simpa using stored
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
          exact merge_tail_satisfies property antitone before cell _ stored fits incoming
        · simp only [ite_eq_right supported]
          simpa using stored
    | FiniteSet values =>
        apply WP.spec_bind (rust_finite_set_from_btree_sound values domainFits)
        intro normalized checked
        cases normalized with
        | none => simpa using stored
        | some normalized =>
            change WP.spec (mergeDomainTail before cell normalized) _
            apply merge_tail_satisfies property antitone before cell normalized stored fits
            rw [checked.1]
            exact incoming

/-- Testbeli K/Delta-tudas: minden tarolt allitas az eredeti, publikus adatokkal rogzitett kontextusra igaz. -/
structure KnowledgeSound {F : Type} [Field F] (p : Nat)
    (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (values : domains.UcpValueFacts) : Prop where
  known : KnownSound context facts
  covers : DomainsCover context fieldValue values
  canonical : CanonicalStoredDomains (p : Int) values
  small : StoredSatisfy (fun members => members.card ≤ 256) values
  fits : StoredDomainsFit values
  stored : CertificatesStored values
  flags : CompletionFlagsSound context fieldValue values

/-- A beolvasztando domainre vonatkozo bizonyitasi kotelezettseg. -/
structure DomainClaim {F : Type} [Field F] (p : Nat) (context : OriginalContext cells.CellId F)
    (cell : cells.CellId) (domain : domains.UcpValueDomain) : Prop where
  covers : ∀ assignment, context assignment -> DomainContains fieldValue domain (assignment cell)
  canonical : CanonicalDomain (p : Int) domain
  small : (DomainMembers domain).card ≤ 256
  fits : DomainFits domain

section Merge

variable {F : Type} [Field F] (p : Nat) [CharP F p]
  (surjective : Function.Surjective (fun value : Int => (value : F)))

include surjective in
-- A tenyleges mark_domain a teljes testbeli tudasinvarianst megorzi.
theorem rust_mark_domain_preserves_knowledge (positive : 1 < (p : Int))
    (context : OriginalContext cells.CellId F) (facts : knowledge.UcpFacts)
    (before : domains.UcpValueFacts) (sound : KnowledgeSound p context facts before)
    (cell : cells.CellId) (domain : domains.UcpValueDomain) (claim : DomainClaim p context cell domain) :
    domains.UcpValueFacts.impl.mark_domain before cell domain ⦃ fun answer =>
      KnowledgeSound p context facts answer.2 ∧ (answer.1 = false -> answer.2 = before) ⦄ := by
  classical
  by_cases complete : completeDomainTag before cell = true
  · rw [rust_complete_domain_is_immutable before cell domain complete]
    simpa using sound
  have representedBefore := field_cover_to_represented p surjective context positive before
    sound.covers sound.canonical
  have incoming : ∀ assignment, representedContext p surjective context assignment ->
      assignment cell ∈ DomainMembers domain := by
    rintro assignment ⟨original, valid, represented⟩
    rw [represented cell]
    exact (canonical_member_iff p surjective positive domain claim.canonical _).mp (claim.covers original valid)
  have merged := rust_mark_domain_preserves_covering (representedContext p surjective context)
    before cell domain representedBefore sound.fits incoming claim.fits
  have canonicalKept := rust_mark_domain_preserves_stored_property
    (fun members => ∀ value ∈ members, centeredRepresentative value (p : Int) = value)
    (fun _ _ subset large value member => large value (subset member))
    before cell domain sound.canonical sound.fits claim.canonical claim.fits
  have smallKept := rust_mark_domain_preserves_stored_property (fun members => members.card ≤ 256)
    (fun _ _ subset large => (Finset.card_le_card subset).trans large)
    before cell domain sound.small sound.fits claim.small claim.fits
  apply WP.spec_mono (WP.spec_and merged (WP.spec_and canonicalKept smallKept))
  rintro ⟨changed, next⟩ ⟨⟨nextCover, nextFits, sameFlags, frame, progress⟩, nextCanonical, nextSmall⟩
  have noFlag : before.complete_domains cell = false := by
    cases flag : before.complete_domains cell with
    | false => rfl
    | true =>
        obtain ⟨recorded, entry⟩ := sound.stored cell flag
        simp [completeDomainTag, entry, flag] at complete
  refine ⟨⟨sound.known, represented_to_field_cover p surjective context positive next nextCover,
    nextCanonical, nextSmall, nextFits, ?_, ?_⟩, progress⟩
  · intro other flagged
    rw [sameFlags] at flagged
    have different : other ≠ cell := by
      rintro rfl
      rw [noFlag] at flagged
      cases flagged
    obtain ⟨recorded, entry⟩ := sound.stored other flagged
    exact ⟨recorded, (frame other different).trans entry⟩
  · intro other recorded entry flagged value member
    rw [sameFlags] at flagged
    have different : other ≠ cell := by
      rintro rfl
      rw [noFlag] at flagged
      cases flagged
    exact sound.flags other recorded ((frame other different).symm.trans entry) flagged value member

end Merge

end SourceProof
