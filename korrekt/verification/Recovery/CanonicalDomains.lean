import Recovery.Normalization

/-!
A jeloltek es mintak normalizalt, ismetlesmentes halmazat listakkal modellezi.
Az alapertekadasokhoz kepest csak modulo ekvivalenciat allit; nem azonosit
egymassal kulonbozo egesz ertekadasokat tetszoleges egesz kontextusban.
-/

namespace Recovery

variable {Value Cell : Type}

def distinctValues [DecidableEq Value] : List Value -> List Value
  | [] => []
  | first :: rest =>
      let tail := distinctValues rest
      if first ∈ tail then tail else first :: tail

theorem distinct_values_membership [DecidableEq Value] {value : Value} (values : List Value) :
    value ∈ distinctValues values <-> value ∈ values := by
  induction values with
  | nil => simp [distinctValues]
  | cons first rest tailSound =>
      simp only [distinctValues]
      split
      · rename_i firstInTail
        constructor
        · exact fun member => List.mem_cons_of_mem first (tailSound.mp member)
        · intro member
          rcases List.mem_cons.mp member with same | inRest
          · subst value
            exact firstInTail
          · exact tailSound.mpr inRest
      · simp [tailSound]

theorem distinct_values_nodup [DecidableEq Value] (values : List Value) :
    (distinctValues values).Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons first rest tailSound =>
      simp only [distinctValues]
      split
      · exact tailSound
      · rename_i absent
        exact List.nodup_cons.mpr ⟨absent, tailSound⟩

theorem nodup_subset_length_le [DecidableEq Value] {left right : List Value}
    (nodup : left.Nodup) (subset : forall value, value ∈ left -> value ∈ right) :
    left.length <= right.length := by
  induction left generalizing right with
  | nil => exact Nat.zero_le _
  | cons first rest tailBound =>
      obtain ⟨absent, restNodup⟩ := List.nodup_cons.mp nodup
      have firstMember := subset first (by simp)
      have tailSubset : forall value, value ∈ rest -> value ∈ right.erase first := by
        intro value member
        have different : Not (value = first) := by
          intro same
          exact absent (same ▸ member)
        exact (List.mem_erase_of_ne different).mpr (subset value (List.mem_cons_of_mem first member))
      have smaller := tailBound restNodup tailSubset
      have erasedLength := List.length_erase_of_mem firstMember
      have nonempty := List.length_pos_of_mem firstMember
      simp only [List.length_cons] at *
      omega

-- Veges halmaznal az egyenlo elemszam es az egyik iranyu tartalmazas egyenloseget ad.
theorem nodup_subset_equal_length_same [DecidableEq Value] {samples domain : List Value}
    (samplesNodup : samples.Nodup)
    (subset : forall value, value ∈ samples -> value ∈ domain)
    (sameSize : samples.length = domain.length) :
    forall value, value ∈ domain -> value ∈ samples := by
  intro value member
  by_cases witnessed : value ∈ samples
  · exact witnessed
  · have extendedNodup := List.nodup_cons.mpr ⟨witnessed, samplesNodup⟩
    have extendedSubset : forall other, other ∈ value :: samples -> other ∈ domain := by
      intro other included
      rcases List.mem_cons.mp included with same | old
      · exact same ▸ member
      · exact subset other old
    have impossible := nodup_subset_length_le extendedNodup extendedSubset
    simp only [List.length_cons] at impossible
    omega

def canonicalValues (modulus : Int) (values : List Int) : List Int :=
  distinctValues (values.map (fun value => normalizeRepresentative value modulus))

def canonicalFiniteDomain (limit : Nat) (modulus : Int) (values : List Int) : Option (List Int) :=
  let canonical := canonicalValues modulus values
  if canonical = [] then none else boundedList limit canonical

def EquivalentModulo (modulus left right : Int) : Prop := left % modulus = right % modulus

def Represents (modulus : Int) (values : List Int) (value : Int) : Prop :=
  exists representative, representative ∈ values /\ EquivalentModulo modulus representative value

def CoversModulo (ctx : Context Cell Int) (cell : Cell) (modulus : Int) (values : List Int) : Prop :=
  forall assignment, ctx assignment -> Represents modulus values (assignment cell)

def FeasibleModulo (ctx : Context Cell Int) (cell : Cell) (modulus value : Int) : Prop :=
  exists assignment, ctx assignment /\ EquivalentModulo modulus (assignment cell) value

def SamplesSoundModulo (ctx : Context Cell Int) (cell : Cell) (modulus : Int) (values : List Int) : Prop :=
  forall value, value ∈ values -> FeasibleModulo ctx cell modulus value

def CompleteModulo (ctx : Context Cell Int) (cell : Cell) (modulus : Int) (values : List Int) : Prop :=
  forall value, Represents modulus values value <-> FeasibleModulo ctx cell modulus value

theorem canonical_membership_iff {modulus value : Int} (positive : 0 < modulus) (values : List Int) :
    normalizeRepresentative value modulus ∈ canonicalValues modulus values <->
      Represents modulus values value := by
  rw [canonicalValues, distinct_values_membership, List.mem_map]
  constructor
  · intro member
    obtain ⟨representative, included, same⟩ := member
    exact ⟨representative, included, (normalization_eq_iff_same_residue positive).mp same⟩
  · intro represented
    obtain ⟨representative, included, same⟩ := represented
    exact ⟨representative, included, (normalization_eq_iff_same_residue positive).mpr same⟩

theorem canonical_values_preserve_representation {modulus : Int} (positive : 0 < modulus)
    (values : List Int) (value : Int) :
    Represents modulus (canonicalValues modulus values) value <-> Represents modulus values value := by
  constructor
  · intro represented
    obtain ⟨representative, member, same⟩ := represented
    have mapped := distinct_values_membership (values.map (fun v => normalizeRepresentative v modulus)) |>.mp member
    obtain ⟨original, included, normalized⟩ := List.mem_map.mp mapped
    refine ⟨original, included, ?_⟩
    unfold EquivalentModulo at *
    rw [<- normalized, normalization_preserves_residue positive] at same
    exact same
  · intro represented
    obtain ⟨representative, member, same⟩ := represented
    refine ⟨normalizeRepresentative representative modulus, ?_, ?_⟩
    · exact (canonical_membership_iff positive values).mpr ⟨representative, member, rfl⟩
    · unfold EquivalentModulo at *
      rw [normalization_preserves_residue positive]
      exact same

theorem canonical_coverage_sound {ctx : Context Cell Int} {cell : Cell} {modulus : Int}
    {values : List Int} (positive : 0 < modulus) (cover : CoversModulo ctx cell modulus values) :
    CoversModulo ctx cell modulus (canonicalValues modulus values) := by
  intro assignment valid
  exact (canonical_values_preserve_representation positive values (assignment cell)).mpr (cover assignment valid)

theorem canonical_samples_sound {ctx : Context Cell Int} {cell : Cell} {modulus : Int}
    {values : List Int} (positive : 0 < modulus) (sound : SamplesSoundModulo ctx cell modulus values) :
    SamplesSoundModulo ctx cell modulus (canonicalValues modulus values) := by
  intro value member
  have mapped := distinct_values_membership (values.map (fun v => normalizeRepresentative v modulus)) |>.mp member
  obtain ⟨original, included, normalized⟩ := List.mem_map.mp mapped
  obtain ⟨assignment, valid, same⟩ := sound original included
  refine ⟨assignment, valid, ?_⟩
  unfold EquivalentModulo at *
  rw [<- normalized, normalization_preserves_residue positive]
  exact same

theorem canonical_finite_success {modulus : Int} {limit : Nat} {input output : List Int}
    (success : canonicalFiniteDomain limit modulus input = some output) :
    output = canonicalValues modulus input := by
  unfold canonicalFiniteDomain at success
  dsimp only at success
  split at success
  · cases success
  · exact bounded_list_success success

theorem canonical_finite_preserves_coverage {ctx : Context Cell Int} {cell : Cell}
    {modulus : Int} {limit : Nat} {input output : List Int}
    (positive : 0 < modulus) (cover : CoversModulo ctx cell modulus input)
    (success : canonicalFiniteDomain limit modulus input = some output) :
    CoversModulo ctx cell modulus output := by
  rw [canonical_finite_success success]
  exact canonical_coverage_sound positive cover

theorem canonical_finite_overflow_rejected {modulus : Int} {limit : Nat} {input : List Int}
    (overflow : limit < (canonicalValues modulus input).length) :
    canonicalFiniteDomain limit modulus input = none := by
  unfold canonicalFiniteDomain
  dsimp only
  split
  · rfl
  · exact bounded_list_overflow overflow

theorem canonical_finite_empty_rejected (modulus : Int) (limit : Nat) :
    canonicalFiniteDomain limit modulus [] = none := by
  rfl

-- A Rustban hasznalt normalizalt reszhalmaz+elemszam ellenorzes matematikai lenyege.
theorem complete_modulo_from_normalized_cardinality
    {ctx : Context Cell Int} {cell : Cell} {modulus : Int} {domain samples : List Int}
    (positive : 0 < modulus) (cover : CoversModulo ctx cell modulus domain)
    (sound : SamplesSoundModulo ctx cell modulus samples)
    (subset : forall value, value ∈ canonicalValues modulus samples ->
      value ∈ canonicalValues modulus domain)
    (sameSize : (canonicalValues modulus samples).length = (canonicalValues modulus domain).length) :
    CompleteModulo ctx cell modulus domain := by
  have allWitnessed := nodup_subset_equal_length_same
    (distinct_values_nodup _) subset sameSize
  intro value
  constructor
  · intro represented
    have canonicalMember := (canonical_membership_iff positive domain).mpr represented
    have sampleMember := allWitnessed _ canonicalMember
    obtain ⟨sample, member, same⟩ := (canonical_membership_iff positive samples).mp sampleMember
    obtain ⟨assignment, valid, feasible⟩ := sound sample member
    exact ⟨assignment, valid, feasible.trans same⟩
  · intro feasible
    obtain ⟨assignment, valid, same⟩ := feasible
    obtain ⟨representative, member, represented⟩ := cover assignment valid
    exact ⟨representative, member, represented.trans same⟩

end Recovery
