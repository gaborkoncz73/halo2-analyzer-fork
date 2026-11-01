import Proofs.RecoveryLoop

open Aeneas Aeneas.Std ucp_verified

namespace SourceProof

variable {M Action Pending Stop Error : Type}

-- Ezek a vezerlesi tetelek nem felteteleznek szemantikai RecoveryContracts szerzodest.
theorem rust_query_result_is_merged
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (state selected queried merged : M) (action : Action) (pending : Pending) (changed : Bool)
    (selection : driver.select state = .ok (.Ok (selected, .Run action)))
    (query : driver.query selected action = .ok (.Ok (queried, pending)))
    (merge : driver.merge queried pending = .ok (.Ok (merged, changed))) :
    recovery_loop.run_recovery_loop.body driver state false = .ok (.cont (merged, changed)) := by
  simp [recovery_loop.run_recovery_loop.body, selection, query, merge,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem rust_stop_does_not_query
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (state selected : M) (status : Stop)
    (selection : driver.select state = .ok (.Ok (selected, .Stop status))) :
    recovery_loop.run_recovery_loop.body driver state false = .ok (.done (.Ok (status, selected))) := by
  simp [recovery_loop.run_recovery_loop.body, selection,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem rust_query_error_is_not_success
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (state selected : M) (action : Action) (error : Error)
    (selection : driver.select state = .ok (.Ok (selected, .Run action)))
    (query : driver.query selected action = .ok (.Err error)) :
    recovery_loop.run_recovery_loop.body driver state false = .ok (.done (.Err error)) := by
  simp [recovery_loop.run_recovery_loop.body, selection, query,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

theorem rust_merge_error_is_not_success
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error)
    (state selected queried : M) (action : Action) (pending : Pending) (error : Error)
    (selection : driver.select state = .ok (.Ok (selected, .Run action)))
    (query : driver.query selected action = .ok (.Ok (queried, pending)))
    (merge : driver.merge queried pending = .ok (.Err error)) :
    recovery_loop.run_recovery_loop.body driver state false = .ok (.done (.Err error)) := by
  simp [recovery_loop.run_recovery_loop.body, selection, query, merge,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

theorem rust_propagation_repeat_does_not_refresh
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error) (state next : M)
    (propagated : driver.propagate state = .ok (.Ok (next, true))) :
    recovery_loop.propagate_until_stable_loop.body driver state = .ok (.cont next) := by
  simp [recovery_loop.propagate_until_stable_loop.body, propagated,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem rust_propagation_error_is_not_success
    (driver : recovery_loop.RecoveryMachine M Action Pending Stop Error) (state : M) (error : Error)
    (propagated : driver.propagate state = .ok (.Err error)) :
    recovery_loop.propagate_until_stable_loop.body driver state = .ok (.done (.Err error)) := by
  simp [recovery_loop.propagate_until_stable_loop.body, propagated,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]

end SourceProof
