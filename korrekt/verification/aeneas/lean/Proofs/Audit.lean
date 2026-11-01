import Proofs.Regression
import Proofs.RecoveryKnowledge
import Proofs.RecoveryControl
import Proofs.KnowledgeUpdate
import Proofs.DomainState
import Proofs.FiniteDomains
import Proofs.DomainMerge
import Proofs.FieldNormalization
import Proofs.CanonicalMerge
import Proofs.CertificationControl
import Lean

/- A gepi ellenorzes a tetelfuggosegekben sem enged hianyzo bizonyitast vagy sajat axiomat. -/
open Lean Elab Command in
run_cmd do
  let environment <- getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for entry in environment.constants.toList do
    let declName := entry.1
    let declInfo := entry.2
    if (`SourceProof).isPrefixOf declName then
      match declInfo with
      | .thmInfo _ =>
          let axioms <- collectAxioms declName
          for dependency in axioms do
            unless allowed.contains dependency do
              throwError "Tiltott axiomafuggoseg: {declName}: {dependency}"
          checked := checked + 1
      | .axiomInfo _ => throwError "Sajat axioma nem megengedett: {declName}"
      | _ => pure ()
  if checked == 0 then throwError "Nem talalt forraskodhoz kotott tetelt."
  logInfo m!"Aeneas axiomaaudit: {checked} tetel ellenorizve."

#print axioms SourceProof.rust_uniqueness_sound
#print axioms SourceProof.rust_assign_sound
#print axioms SourceProof.rust_recovery_success_is_sound
#print axioms SourceProof.rust_recovery_preserves_knowledge
#print axioms SourceProof.rust_assign_then_insert_is_sound
#print axioms SourceProof.rust_recovery_exact_value_is_forced
#print axioms SourceProof.rust_known_value_is_forced
#print axioms SourceProof.rust_complete_domain_is_exact
#print axioms SourceProof.rust_hypothetical_preserves_covering
#print axioms SourceProof.rust_bounded_value_never_truncates
#print axioms SourceProof.rust_finite_set_loop_sound
#print axioms SourceProof.rust_intersection_sound
#print axioms SourceProof.rust_mark_domain_preserves_covering
#print axioms SourceProof.rust_mark_domain_preserves_certificates
#print axioms SourceProof.rust_normalization_succeeds
#print axioms SourceProof.rust_normalization_identifies_aliases
#print axioms SourceProof.rust_mark_domain_preserves_modulo_coverage
#print axioms SourceProof.rust_certification_missing_domain_keeps_state
#print axioms SourceProof.rust_certification_domain_value_failure_keeps_state
#print axioms SourceProof.rust_certification_records_normalized_candidate
