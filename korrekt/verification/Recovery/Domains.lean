import Recovery.Semantics

/-!
A lefedo domainek es a megvalosithato mintak kulonbozo iranyu kozelitesek.
Ezek a tetelek a halmazmuveletek szemantikajat, nem a BigInt-tarolast igazoljak.
-/

namespace Recovery

variable {Cell Value : Type} {ctx : Context Cell Value} {cell : Cell}

theorem intersect_preserves_coverage {left right : ValueSet Value}
    (leftCover : Covers ctx cell left) (rightCover : Covers ctx cell right) :
    Covers ctx cell (Intersection left right) := by
  intro assignment valid
  exact ⟨leftCover assignment valid, rightCover assignment valid⟩

theorem covering_intersection_nonempty {left right : ValueSet Value}
    (sat : Satisfiable ctx)
    (leftCover : Covers ctx cell left) (rightCover : Covers ctx cell right) :
    exists value, Intersection left right value := by
  obtain ⟨assignment, valid⟩ := sat
  exact ⟨assignment cell, leftCover assignment valid, rightCover assignment valid⟩

theorem remember_samples_preserves_soundness {old incoming : ValueSet Value}
    (oldSound : SamplesSound ctx cell old) (incomingSound : SamplesSound ctx cell incoming) :
    SamplesSound ctx cell (Union old incoming) := by
  intro value member
  rcases member with fromOld | fromIncoming
  · exact oldSound value fromOld
  · exact incomingSound value fromIncoming

theorem model_sample_is_sound (assignment : Assignment Cell Value) (valid : ctx assignment) :
    SamplesSound ctx cell (Singleton (assignment cell)) := by
  intro value same
  exact ⟨assignment, valid, same.symm⟩

theorem complete_from_samples {domain samples : ValueSet Value}
    (cover : Covers ctx cell domain) (sound : SamplesSound ctx cell samples)
    (allWitnessed : Included domain samples) : Complete ctx cell domain := by
  intro value
  constructor
  · intro member
    exact sound value (allWitnessed value member)
  · exact coverage_iff_feasible_included.mp cover value

theorem singleton_cover_is_unique {value : Value}
    (cover : Covers ctx cell (Singleton value)) : Unique ctx cell := by
  intro left right leftValid rightValid
  exact (cover left leftValid).trans (cover right rightValid).symm

-- A letezesfeltetel nelkul a singleton lefedese vacuusan igaz is lehetne.
theorem singleton_cover_is_complete {value : Value}
    (sat : Satisfiable ctx) (cover : Covers ctx cell (Singleton value)) :
    Complete ctx cell (Singleton value) := by
  intro other
  constructor
  · intro same
    obtain ⟨assignment, valid⟩ := sat
    exact ⟨assignment, valid, (cover assignment valid).trans same.symm⟩
  · intro feasible
    exact coverage_iff_feasible_included.mp cover other feasible

theorem two_samples_prove_non_unique {samples : ValueSet Value} {a b : Value}
    (sound : SamplesSound ctx cell samples)
    (hasA : samples a) (hasB : samples b) (distinct : Not (a = b)) : NonUnique ctx cell := by
  exact ⟨a, b, sound a hasA, sound b hasB, distinct⟩

-- Valtozatlan kontextusban egy teljes domainbol helyes kovetkeztetes mar nem torolhet erteket.
theorem complete_intersection_unchanged {domain incoming : ValueSet Value}
    (complete : Complete ctx cell domain) (cover : Covers ctx cell incoming) :
    SameValues (Intersection domain incoming) domain := by
  intro value
  constructor
  · exact fun member => member.1
  · intro member
    exact ⟨member, coverage_iff_feasible_included.mp cover value ((complete value).mp member)⟩

-- A solvernek adott igazolt domainmegszoritas nem valtoztatja meg a megoldashalmazt.
theorem covering_hint_is_redundant {domain : ValueSet Value}
    (cover : Covers ctx cell domain) (assignment : Assignment Cell Value) :
    ctx assignment <-> (ctx assignment /\ domain (assignment cell)) := by
  exact ⟨fun valid => ⟨valid, cover assignment valid⟩, fun restricted => restricted.1⟩

end Recovery
