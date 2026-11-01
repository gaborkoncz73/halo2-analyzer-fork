import Recovery.CanonicalDomains

/-!
Az elojeles maradekot, a kanonikus azonositast es a teljessegi feltetelek
hatarait konkret, kernel-altal ellenorzott esetekkel szemlelteti.
-/

namespace Recovery.Checks

-- A Lean % es a Rust-szeru maradek negativ osztandon nem egyezik meg.
example : Int.tmod (-1) 17 = -1 /\ ((-1 : Int) % 17) = 16 := by decide

example : normalizeRepresentative (-1) 17 = -1 := by decide
example : normalizeRepresentative 16 17 = -1 := by decide
example : normalizeRepresentative 33 17 = -1 := by decide
example : normalizeRepresentative (-18) 17 = -1 := by decide

-- Paros modulusnal a pozitiv felso felet tartja meg, a Rust feltetelenek megfeleloen.
example : normalizeRepresentative (-2) 4 = 2 := by decide

example : normalizeField 8 123 1 = none := by decide
example : normalizeField 4 123 17 = none := by decide
example : normalizeField 5 123 17 = some 4 := by decide

-- Azonos testelemek nem novelhetik a mintak elemszamat es nem bizonyitanak nemegyertelmuseget.
example : canonicalValues 17 [-1, 16, 33] = [-1] := by decide
example : canonicalFiniteDomain 1 17 [-1, 16, 33] = some [-1] := by decide
example : canonicalFiniteDomain 1 17 [0, 1] = none := by decide

-- Az elemszam egyezese reszhalmaz-feltetel nelkul nem igazol egyenloseget.
example : ([0] : List Int).length = [1].length /\ Not (Represents 17 [0] 1) := by
  constructor
  · rfl
  · intro represented
    obtain ⟨value, member, same⟩ := represented
    have zero : value = 0 := by simpa using member
    subst value
    have impossible : (0 : Int) = 1 := same
    cases impossible

-- A normalizalas i64-nel nagyobb ertekeket sem csonkit gepi szomeretre.
set_option maxRecDepth 8192 in
example : normalizeField 256 ((2 : Int) ^ 255 - 20) ((2 : Int) ^ 255 - 19) = some (-1) := by
  decide

end Recovery.Checks
