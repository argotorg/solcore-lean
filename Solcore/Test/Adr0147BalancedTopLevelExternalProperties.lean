import Solcore.Semantics.BalancedTopLevelExecutionProperties

/-! External compile consumers for balance-aware top-level execution laws. -/

set_option autoImplicit false

namespace Tests.Adr0147BalancedTopLevelExternalProperties

open Solcore.Semantics
open BalancedTopLevelExecution

example := @RejectedResult.ofFailure_failure
example := @RejectedResult.ofFailure_finalWorld
example := @RejectedResult.ofFailure_committedDelta

example := @Result.eq_of_view_eq
example := @Result.ofExecution_view

example := @run_of_zero_value
example := @run_of_transfer_failure
example := @run_of_transfer_success
example := @resumeWithFuel_rejected
example := @resumeWithFuel_execution
example := @resumeWithFuel_run
example := @resumeWithFuel_run_zero

end Tests.Adr0147BalancedTopLevelExternalProperties
