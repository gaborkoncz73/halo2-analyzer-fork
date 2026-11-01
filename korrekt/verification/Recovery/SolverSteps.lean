import Recovery.Domains

/-!
A solver eredmenyeinek szemantikai kovetkezmenyeit bizonyitja.
Az UNSAT-premissza valodi kielegithetetlenseget jelent, nem feldolgozatlan solvercimket.
A solver, a parser es a Halo2-SMT-forditas helyesseget nem bizonyitja.
-/

namespace Recovery

variable {Cell Value : Type} {ctx : Context Cell Value} {cell : Cell}

theorem exclusion_unsat_proves_coverage {domain : ValueSet Value}
    (unsat : Not (Satisfiable (fun assignment =>
      ctx assignment /\ Not (domain (assignment cell))))) : Covers ctx cell domain := by
  intro assignment valid
  apply Classical.byContradiction
  intro outside
  exact unsat ⟨assignment, valid, outside⟩

theorem candidate_unsat_allows_removal {domain : ValueSet Value} {candidate : Value}
    (cover : Covers ctx cell domain)
    (unsat : Not (Feasible ctx cell candidate)) :
    Covers ctx cell (fun value => domain value /\ Not (value = candidate)) := by
  intro assignment valid
  exact ⟨cover assignment valid, fun same => unsat ⟨assignment, valid, same⟩⟩

theorem discovery_exclusion_proves_complete {samples : ValueSet Value}
    (sound : SamplesSound ctx cell samples)
    (unsat : Not (Satisfiable (fun assignment =>
      ctx assignment /\ Not (samples (assignment cell))))) : Complete ctx cell samples := by
  exact complete_from_samples (exclusion_unsat_proves_coverage unsat) sound (fun _ h => h)

theorem fast_probe_unsat_proves_exact {value : Value}
    (feasible : Feasible ctx cell value)
    (unsat : Not (Satisfiable (fun assignment =>
      ctx assignment /\ Not (assignment cell = value)))) :
    Unique ctx cell /\ Complete ctx cell (Singleton value) := by
  have cover : Covers ctx cell (Singleton value) := exclusion_unsat_proves_coverage unsat
  obtain ⟨assignment, valid, _⟩ := feasible
  exact ⟨singleton_cover_is_unique cover, singleton_cover_is_complete ⟨assignment, valid⟩ cover⟩

end Recovery
