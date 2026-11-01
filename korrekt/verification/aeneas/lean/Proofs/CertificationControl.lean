import Proofs.CanonicalMerge

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

-- A teljessegjelolo tenyleges belepopontja hianyzo domainbol nem keszit uj tudast.
theorem rust_certification_missing_domain_keeps_state (values : domains.UcpValueFacts)
    (cell : cells.CellId) (samples : Finset Int) (modulus : Int)
    (missing : values.domains cell = none) :
    domains.UcpValueFacts.impl.try_mark_complete_from_samples values cell samples modulus =
      .ok (.Ok false, values) := by
  unfold domains.UcpValueFacts.impl.try_mark_complete_from_samples
  rw [rust_domain_lookup]
  simp [missing]

-- A hibas normalizalas nem alakithato sikeres vagy teljesnek jelolt allapotta.
theorem rust_certification_domain_value_failure_keeps_state (values : domains.UcpValueFacts)
    (cell : cells.CellId) (samples : Finset Int) (modulus value : Int)
    (iter next : alloc.vec.into_iter.IntoIter Int) (candidates : List (Int × Int))
    (read : alloc.vec.into_iter.IteratorIntoIter.next iter = .ok (some value, next))
    (failed : domains.normalize_field_value value modulus = .ok none) :
    domains.UcpValueFacts.impl.try_mark_complete_from_samples_loop.body values.domains values.complete_domains
      cell samples modulus iter candidates =
        .ok (.done (.Err .DomainValue, values.domains, values.complete_domains)) := by
  unfold domains.UcpValueFacts.impl.try_mark_complete_from_samples_loop.body
  rw [read]
  simp [num_bigint.bigint.BigInt.Insts.CoreCloneClone.clone, failed,
    core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

noncomputable def rememberRepresentative (entries : List (Int × Int)) (key value : Int) : List (Int × Int) :=
  let selected := (entries.find? (fun pair => @decide (pair.1 = key) (Classical.propDecidable _))).map Prod.snd |>.getD value
  (key, selected) :: entries.filter (fun pair => @decide (pair.1 ≠ key) (Classical.propDecidable _))

-- A jelolt kulcsa a Rust-normalizalas eredmenye, az erteke egy eredeti reprezentans.
-- Azonos kulcsnal a korabbi reprezentanst tartja meg, nem kepez uj lehetseges erteket.
theorem rust_certification_records_normalized_candidate (values : domains.UcpValueFacts)
    (cell : cells.CellId) (samples : Finset Int) (modulus value normalized : Int)
    (iter next : alloc.vec.into_iter.IntoIter Int) (candidates : List (Int × Int))
    (read : alloc.vec.into_iter.IteratorIntoIter.next iter = .ok (some value, next))
    (normalizedValue : domains.normalize_field_value value modulus = .ok (some normalized)) :
    domains.UcpValueFacts.impl.try_mark_complete_from_samples_loop.body values.domains values.complete_domains
      cell samples modulus iter candidates =
        .ok (.cont (next, rememberRepresentative candidates normalized value)) := by
  classical
  unfold domains.UcpValueFacts.impl.try_mark_complete_from_samples_loop.body
  rw [read]
  simp only [num_bigint.bigint.BigInt.Insts.CoreCloneClone.clone, bind_ok,
    core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch]
  simp only [bind_ok, alloc.collections.btree.map.BTreeMap.impl.entry]
  cases entry : candidates.find? (fun pair => @decide (pair.1 = normalized) (Classical.propDecidable _)) <;>
    simp [entry, normalizedValue, alloc.collections.btree.map.entry.Entry.impl.or_insert_with,
      domains.UcpValueFacts.try_mark_complete_from_samples.closure.Insts.CoreOpsFunctionFnOnceTupleBigInt.call_once,
      num_bigint.bigint.BigInt.Insts.CoreCloneClone.clone, mapEntryBack, rememberRepresentative]

theorem rust_certification_step_uses_canonical_key (values : domains.UcpValueFacts)
    (cell : cells.CellId) (samples : Finset Int) (modulus value : Int)
    (valid : 1 < modulus) (fits : modulus.natAbs.size ≤ 4096)
    (iter next : alloc.vec.into_iter.IntoIter Int) (candidates : List (Int × Int))
    (read : alloc.vec.into_iter.IteratorIntoIter.next iter = .ok (some value, next)) :
    domains.UcpValueFacts.impl.try_mark_complete_from_samples_loop.body values.domains values.complete_domains
      cell samples modulus iter candidates =
        .ok (.cont (next, rememberRepresentative candidates (centeredRepresentative value modulus) value)) :=
  rust_certification_records_normalized_candidate values cell samples modulus value _ iter next candidates
    read (rust_normalization_succeeds value modulus valid fits)

end SourceProof
