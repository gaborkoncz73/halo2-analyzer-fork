import Recovery.Execution
import Recovery.SolverSteps
import Recovery.Checks
import Recovery.ExpressionDomains
import Recovery.Algebra
import Recovery.AffineProjection
import Recovery.AffineSplit
import Recovery.PropagationChecks
import Recovery.Normalization
import Recovery.CanonicalDomains
import Recovery.RepresentationChecks
import Recovery.Uniqueness
import Recovery.Root
import Recovery.AllButOne
import Recovery.BaseConversion
import Recovery.RuleChecks
import Recovery.GlobalKnowledge
import Recovery.GlobalExecution
import Recovery.ContextReasoning
import Recovery.ConditionalReasoning
import Recovery.Cache
import Recovery.PropagationView
import Recovery.GlobalChecks
import Lean

/-!
A Recovery-nevter minden tetelenek tranzitiv axiomafuggoseget ellenorzi.
A standard logikai axiomakon kivul sem sajat axiomat, sem hianyzo bizonyitast nem enged.
-/

open Lean Elab Command in
run_cmd do
  let environment <- getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in environment.constants.toList do
    if (`Recovery).isPrefixOf name then
      match info with
      | .thmInfo _ =>
          let axioms <- collectAxioms name
          for dependency in axioms do
            unless allowed.contains dependency do
              throwError "Tiltott axiomafuggoseg: {name}: {dependency}"
          checked := checked + 1
      | .axiomInfo _ =>
          throwError "Sajat Recovery-axioma nem megengedett: {name}"
      | _ => pure ()
  if checked == 0 then
    throwError "Nem talalt ellenorizheto Recovery-tetelt."
  logInfo m!"Axiomaaudit: {checked} Recovery-tetel ellenorizve."

#print axioms Recovery.recovery_from_empty_is_sound
#print axioms Recovery.complete_from_samples
#print axioms Recovery.fast_probe_unsat_proves_exact
#print axioms Recovery.expression_domain_sound
#print axioms Recovery.split_then_project_sound
#print axioms Recovery.zero_equation_projection_sound
#print axioms Recovery.normalization_preserves_residue
#print axioms Recovery.complete_modulo_from_normalized_cardinality
#print axioms Recovery.root_candidates_sound
#print axioms Recovery.all_but_one_unique
#print axioms Recovery.base_conversion_unique
#print axioms Recovery.global_recovery_reports_sound
#print axioms Recovery.hinted_exclusion_proves_original_coverage
#print axioms Recovery.cached_expression_domain_sound
