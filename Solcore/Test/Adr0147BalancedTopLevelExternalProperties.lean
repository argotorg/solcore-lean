import Solcore.Semantics.BalancedTopLevelExecutionProperties

/-! External compile consumers for balance-aware top-level execution laws. -/

set_option autoImplicit false

namespace Tests.Adr0147BalancedTopLevelExternalProperties

open Solcore.Semantics
open BalancedTopLevelExecution

example := @RejectedResult.ofFailure_failure
example := @RejectedResult.ofFailure_finalWorld
example := @RejectedResult.ofFailure_committedDelta
example := @RejectedResult.committedDelta_accountEndpoints_identity
example := @RejectedResult.committedDelta_storageEndpoints_identity
example := @RejectedResult.committedDelta_balanceEndpoints_identity
example := @RejectedResult.committedDelta_balanceChange?_identity

example := @Result.eq_of_view_eq
example := @Result.finalWorld?_rejected
example := @Result.terminalStatus?_rejected
example := @Result.committedWorld?_rejected
example := @Result.finalWorld?_completed
example := @Result.terminalStatus?_completed
example := @Result.committedWorld?_completed
example := @Result.observations_outOfFuel

example := @run_of_zero_value
example := @run_of_transfer_failure
example := @run_of_transfer_success
example := @runWithEnvironment_of_zero_value
example := @runWithEnvironment_of_transfer_failure
example := @runWithEnvironment_of_transfer_success
example := @resumeWithFuel_rejected
example := @resumeWithFuel_execution
example := @resumeWithFuel_run
example := @resumeWithFuel_runWithEnvironment
example := @resumeWithFuel_run_zero

end Tests.Adr0147BalancedTopLevelExternalProperties
