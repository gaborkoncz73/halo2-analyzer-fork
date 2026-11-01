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
import Proofs.Certification
import Proofs.RecoveryCore
import Proofs.EngineFixpoint
import Proofs.RecoveryDriver
import Proofs.RuleLink
import Proofs.PrivateRecovery
import Proofs.Examples
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
#print axioms SourceProof.rust_certification_preserves_knowledge
#print axioms SourceProof.rust_merge_evidence_sound
#print axioms SourceProof.rust_finish_merge_sound
#print axioms SourceProof.engine_execution_sound
#print axioms SourceProof.core_machine_contracts
#print axioms SourceProof.rust_private_recovery_sound
#print axioms SourceProof.rust_recovered_value_is_forced
#print axioms SourceProof.core_refines_model
#print axioms SourceProof.all_but_one_rule_evidence
#print axioms SourceProof.linear_system_rule_evidence
#print axioms SourceProof.base_conversion_rule_evidence
#print axioms SourceProof.fast_probe_evidence
#print axioms SourceProof.refinement_evidence
#print axioms SourceProof.qed2_fixpoint_soundness
#print axioms SourceProof.private_cells_determined_by_public
#print axioms SourceProof.rust_recovery_reveals_secret
#print axioms SourceProof.rust_recovery_proves_overconstrained
#print axioms SourceProof.recovery_is_witness_independent
#print axioms SourceProof.rust_rules_reject_cube_equation
#print axioms SourceProof.cube_is_determined_without_rule
#print axioms SourceProof.example_run
#print axioms SourceProof.example_recovers_secret
#print axioms SourceProof.example_is_overconstrained
#print axioms SourceProof.public_value_claim
