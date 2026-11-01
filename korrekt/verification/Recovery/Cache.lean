import Recovery.ExpressionDomains

/-!
A domain-kiertekelo cache-hez bizonyitja a fuggosegi szignatura elegendoseget.
A kifejezes, a muveletek es a meretkorlat rogzitett parameterek; ezeket valtoztato
ujrafelhasznalast a tetel nem enged. A Rust Memo tarolo megvalositasa kulon kotelezettseg.
-/

namespace Recovery

variable {Cell Value : Type}

def expressionCells : Expression Cell Value -> List Cell
  | .var cell => [cell]
  | .const _ => []
  | .add left right | .mul left right => expressionCells left ++ expressionCells right
  | .neg inner | .scale inner _ => expressionCells inner

def domainSignature (expr : Expression Cell Value) (facts : Cell -> Option (List Value))
    (complete : Cell -> Bool) : List (Cell × Option (List Value) × Bool) :=
  (expressionCells expr).map (fun cell => (cell, facts cell, complete cell))

structure DomainCacheEntry (Cell Value : Type) where
  signature : List (Cell × Option (List Value) × Bool)
  result : Option (List Value)

-- A some none tarolt sikertelen kiertekeles, a none pedig cache-miss.
def reuseDomainCache [DecidableEq Cell] [DecidableEq Value]
    (expr : Expression Cell Value) (facts : Cell -> Option (List Value)) (complete : Cell -> Bool)
    (entry : DomainCacheEntry Cell Value) : Option (Option (List Value)) :=
  if entry.signature = domainSignature expr facts complete then some entry.result else none

theorem expression_domain_agrees_on_dependencies
    {limit : Nat} {ops : Arithmetic Value} {left right : Cell -> Option (List Value)}
    (expr : Expression Cell Value)
    (agreement : forall cell, cell ∈ expressionCells expr -> left cell = right cell) :
    expressionDomain limit ops left expr = expressionDomain limit ops right expr := by
  induction expr with
  | var cell => exact agreement cell (by simp [expressionCells])
  | const value => rfl
  | neg inner innerSame => simp only [expressionDomain, innerSame agreement]
  | scale inner scalar innerSame => simp only [expressionDomain, innerSame agreement]
  | add first second firstSame secondSame =>
      have firstEqual := firstSame (fun cell member => agreement cell (List.mem_append_left _ member))
      have secondEqual := secondSame (fun cell member => agreement cell (List.mem_append_right _ member))
      simp only [expressionDomain, firstEqual, secondEqual]
  | mul first second firstSame secondSame =>
      have firstEqual := firstSame (fun cell member => agreement cell (List.mem_append_left _ member))
      have secondEqual := secondSame (fun cell member => agreement cell (List.mem_append_right _ member))
      simp only [expressionDomain, firstEqual, secondEqual]

theorem equal_signatures_agree_on_domains
    {expr : Expression Cell Value} {left right : Cell -> Option (List Value)}
    {leftComplete rightComplete : Cell -> Bool}
    (same : domainSignature expr left leftComplete = domainSignature expr right rightComplete) :
    forall cell, cell ∈ expressionCells expr -> left cell = right cell := by
  intro cell member
  have entrySame := List.map_inj_left.mp same cell member
  exact congrArg (fun entry => entry.2.1) entrySame

theorem cache_hit_matches_recomputation [DecidableEq Cell] [DecidableEq Value]
    {limit : Nat} {ops : Arithmetic Value} {expr : Expression Cell Value}
    {old current : Cell -> Option (List Value)} {oldComplete currentComplete : Cell -> Bool}
    {entry : DomainCacheEntry Cell Value} {result : Option (List Value)}
    (recorded : entry.signature = domainSignature expr old oldComplete)
    (computed : entry.result = expressionDomain limit ops old expr)
    (hit : reuseDomainCache expr current currentComplete entry = some result) :
    result = expressionDomain limit ops current expr := by
  unfold reuseDomainCache at hit
  split at hit
  · rename_i currentSignature
    have same := equal_signatures_agree_on_domains (recorded.symm.trans currentSignature)
    exact (Option.some.inj hit).symm.trans
      (computed.trans (expression_domain_agrees_on_dependencies expr same))
  · cases hit

theorem cached_expression_domain_sound [DecidableEq Cell] [DecidableEq Value]
    {ctx : Context Cell Value} {limit : Nat} {ops : Arithmetic Value} {expr : Expression Cell Value}
    {old current : Cell -> Option (List Value)} {oldComplete currentComplete : Cell -> Bool}
    {entry : DomainCacheEntry Cell Value} {output : List Value}
    (recorded : entry.signature = domainSignature expr old oldComplete)
    (computed : entry.result = expressionDomain limit ops old expr)
    (factsSound : FactsCover ctx current)
    (hit : reuseDomainCache expr current currentComplete entry = some (some output)) :
    forall assignment, ctx assignment -> evaluate ops assignment expr ∈ output := by
  have same := cache_hit_matches_recomputation recorded computed hit
  exact expression_domain_sound factsSound expr same.symm

end Recovery
