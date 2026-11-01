import Recovery.Uniqueness

/-!
A Base-Conv szabaly nemnegativ egesz szamjegyeinek matematikai modellje.
A bizonyitas kulon kezeli a szamjegykorlatot, a fix hosszt es a no-wrap feltetelt.
A Rust parser, BigInt-tarolas es a field--Nat megfeleltetes meg kulon kotelezettseg.
-/

namespace Recovery

variable {Cell : Type}

def packDigits (base : Nat) : List Nat -> Nat
  | [] => 0
  | digit :: rest => digit + base * packDigits base rest

def DigitsBounded (base : Nat) (digits : List Nat) : Prop :=
  forall digit, digit ∈ digits -> digit < base

def unpackDigits (base : Nat) : Nat -> Nat -> Option (List Nat)
  | 0, value => if value = 0 then some [] else none
  | count + 1, value => do
      let tail <- unpackDigits base count (value / base)
      pure ((value % base) :: tail)

def projectDigitValues (base count index : Nat) (candidates : List Nat) : List Nat :=
  candidates.filterMap (fun value => do
    let digits <- unpackDigits base count value
    digits[index]?)

theorem packed_head_mod {base digit : Nat} {rest : List Nat} (bound : digit < base) :
    packDigits base (digit :: rest) % base = digit := by
  simp only [packDigits, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bound]

theorem packed_tail_div {base digit : Nat} {rest : List Nat} (positive : 0 < base)
    (bound : digit < base) : packDigits base (digit :: rest) / base = packDigits base rest := by
  simp only [packDigits, Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt bound, Nat.zero_add]

theorem packed_below_power {base : Nat} (digits : List Nat) (bounded : DigitsBounded base digits) :
    packDigits base digits < base ^ digits.length := by
  induction digits with
  | nil => simp [packDigits]
  | cons digit rest tailBound =>
      have headBound := bounded digit (by simp)
      have remainder := tailBound (fun value member => bounded value (List.mem_cons_of_mem digit member))
      have scaled := Nat.mul_le_mul_left base (show packDigits base rest + 1 <= base ^ rest.length by omega)
      simp only [Nat.mul_add, Nat.mul_one] at scaled
      simp only [packDigits, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (base ^ rest.length) base]
      omega

theorem unpack_packed_digits {base : Nat} (positive : 0 < base)
    (digits : List Nat) (bounded : DigitsBounded base digits) :
    unpackDigits base digits.length (packDigits base digits) = some digits := by
  induction digits with
  | nil => rfl
  | cons digit rest tailResult =>
      have headBound := bounded digit (by simp)
      have remainder := tailResult (fun value member => bounded value (List.mem_cons_of_mem digit member))
      simp only [List.length_cons, unpackDigits, packed_head_mod headBound,
        packed_tail_div positive headBound, remainder, pure]
      rfl

theorem pack_digits_injective {base : Nat} (positive : 0 < base)
    {left right : List Nat} (leftBounded : DigitsBounded base left)
    (rightBounded : DigitsBounded base right) (sameLength : left.length = right.length)
    (samePacked : packDigits base left = packDigits base right) : left = right := by
  have decodedLeft := unpack_packed_digits positive left leftBounded
  have decodedRight := unpack_packed_digits positive right rightBounded
  rw [sameLength, samePacked, decodedRight] at decodedLeft
  exact (Option.some.inj decodedLeft).symm

theorem failed_unpack_excludes_packing {base count value : Nat} (positive : 0 < base)
    (failure : unpackDigits base count value = none) (digits : List Nat)
    (bounded : DigitsBounded base digits) (length : digits.length = count) :
    Not (packDigits base digits = value) := by
  intro same
  have decoded := unpack_packed_digits positive digits bounded
  rw [length, same, failure] at decoded
  cases decoded

-- A packed domain csak lefedo kell legyen, nem kell minden jelolt megvalosithatosagat feltetelezni.
theorem projected_digit_contains_valid {base count index value : Nat} {candidates digits : List Nat}
    (positive : 0 < base) (bounded : DigitsBounded base digits) (length : digits.length = count)
    (packedMember : packDigits base digits ∈ candidates) (digitAt : digits[index]? = some value) :
    value ∈ projectDigitValues base count index candidates := by
  have decoded := unpack_packed_digits positive digits bounded
  rw [length] at decoded
  apply List.mem_filterMap.mpr
  refine ⟨packDigits base digits, packedMember, ?_⟩
  rw [decoded]
  exact digitAt

theorem finite_base_projection_sound {ctx : Context Cell Nat} {packed cell : Cell}
    {digits : List Cell} {base index limit : Nat} {candidates output : List Nat}
    (positive : 0 < base)
    (bounded : forall assignment, ctx assignment -> DigitsBounded base (digits.map assignment))
    (equation : forall assignment, ctx assignment -> packDigits base (digits.map assignment) = assignment packed)
    (cover : Covers ctx packed (ListDomain candidates)) (cellAt : digits[index]? = some cell)
    (success : boundedList limit (projectDigitValues base digits.length index candidates) = some output) :
    Covers ctx cell (ListDomain output) := by
  intro assignment valid
  have member : packDigits base (digits.map assignment) ∈ candidates := by
    rw [equation assignment valid]
    exact cover assignment valid
  have digitAt : (digits.map assignment)[index]? = some (assignment cell) := by
    simp only [List.getElem?_map, cellAt, Option.map_some]
  exact bounded_list_preserves_member success
    (projected_digit_contains_valid positive (bounded assignment valid) (by simp) member digitAt)

theorem pack_append (base : Nat) (left right : List Nat) :
    packDigits base (left ++ right) = packDigits base left + base ^ left.length * packDigits base right := by
  induction left with
  | nil => simp [packDigits]
  | cons digit rest tailResult =>
      simp only [List.cons_append, packDigits, tailResult, List.length_cons, Nat.pow_succ,
        Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
      rw [Nat.mul_left_comm base (base ^ rest.length)]

-- A tenyleges Rust-guardot hasznalja: base^n * (highest_max + 1) < modulus.
theorem highest_digit_bound_prevents_wrap {base modulus highest maximum : Nat} {lower : List Nat}
    (lowerBounded : DigitsBounded base lower) (highestBound : highest <= maximum)
    (guard : base ^ lower.length * (maximum + 1) < modulus) :
    packDigits base (lower ++ [highest]) < modulus := by
  have low := packed_below_power lower lowerBounded
  have scaled := Nat.mul_le_mul_left (base ^ lower.length) (Nat.succ_le_succ highestBound)
  calc
    packDigits base (lower ++ [highest]) = packDigits base lower + base ^ lower.length * highest := by
      simp [pack_append, packDigits]
    _ < base ^ lower.length + base ^ lower.length * highest := Nat.add_lt_add_right low _
    _ = base ^ lower.length * (highest + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    _ <= base ^ lower.length * (maximum + 1) := scaled
    _ < modulus := guard

theorem base_conversion_unique {ctx : Context Cell Nat} {packed : Cell} {digits : List Cell}
    {base modulus : Nat} (positive : 0 < base)
    (bounded : forall assignment, ctx assignment -> DigitsBounded base (digits.map assignment))
    (noWrap : forall assignment, ctx assignment -> packDigits base (digits.map assignment) < modulus)
    (equation : forall assignment, ctx assignment ->
      packDigits base (digits.map assignment) % modulus = assignment packed % modulus)
    (packedUnique : Unique ctx packed) {cell : Cell} (member : cell ∈ digits) : Unique ctx cell := by
  intro left right leftValid rightValid
  have samePacked : packDigits base (digits.map left) = packDigits base (digits.map right) := by
    have residues := (equation left leftValid).trans
      ((congrArg (fun value => value % modulus) (packedUnique left right leftValid rightValid)).trans
        (equation right rightValid).symm)
    simpa only [Nat.mod_eq_of_lt (noWrap left leftValid), Nat.mod_eq_of_lt (noWrap right rightValid)] using residues
  have sameDigits := pack_digits_injective positive (bounded left leftValid) (bounded right rightValid)
    (by simp) samePacked
  exact List.map_inj_left.mp sameDigits cell member

theorem base_conversion_exact_digits {ctx : Context Cell Nat} {packed : Cell} {digits : List Cell}
    {base modulus value : Nat} (positive : 0 < base)
    (bounded : forall assignment, ctx assignment -> DigitsBounded base (digits.map assignment))
    (noWrap : forall assignment, ctx assignment -> packDigits base (digits.map assignment) < modulus)
    (equation : forall assignment, ctx assignment ->
      packDigits base (digits.map assignment) % modulus = assignment packed % modulus)
    (packedKnown : forall assignment, ctx assignment -> assignment packed = value)
    (valueBound : value < modulus) :
    forall assignment, ctx assignment -> unpackDigits base digits.length value = some (digits.map assignment) := by
  intro assignment valid
  have same : packDigits base (digits.map assignment) = value := by
    have residues := equation assignment valid
    rw [packedKnown assignment valid] at residues
    simpa only [Nat.mod_eq_of_lt (noWrap assignment valid), Nat.mod_eq_of_lt valueBound] using residues
  have decoded := unpack_packed_digits positive (digits.map assignment) (bounded assignment valid)
  simpa only [List.length_map, same] using decoded

end Recovery
