import Solcore.ContractRuntime.OneLevelNestedExecutionBalancedRootProperties
import Solcore.ContractRuntime.OneLevelNestedExecutionReachability

/-! External compile consumers for post-transfer root initialization laws. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime
open OneLevelNestedExecution

variable {checkpointWorld workingWorld : WorldState}
variable {rootContract : CheckedCoreContract}
variable {rootInvocation : TopLevelInvocation}
variable
  (installed :
    InstalledCheckedCoreContract workingWorld rootInvocation.target
      rootContract)

example :
    (RootFrame.prepared (checkpointWorld := checkpointWorld) rootContract
      rootInvocation installed).context.context.storageAddress =
        rootInvocation.target :=
  RootFrame.prepared_storageAddress installed

example :
    (RootFrame.prepared (checkpointWorld := checkpointWorld) rootContract
      rootInvocation installed).context.context.values.checkpoint.state =
        checkpointWorld :=
  RootFrame.prepared_checkpointState installed

example :
    (RootFrame.prepared (checkpointWorld := checkpointWorld) rootContract
      rootInvocation installed).context.context.values.working.1 =
        workingWorld :=
  RootFrame.prepared_workingState installed

example :
    (RootFrame.prepared (checkpointWorld := checkpointWorld) rootContract
      rootInvocation installed).context.storageAccount = installed.account :=
  RootFrame.prepared_storageAccount installed

example :
    (RootFrame.prepared (checkpointWorld := checkpointWorld) rootContract
      rootInvocation installed).state =
        Core.State.initial rootContract.code.program.body Core.hostEnvironment :=
  RootFrame.prepared_state installed

example (registry : ExecutionEnvironment)
    (transferred :
      checkpointWorld.transferBalance rootInvocation.caller
          rootInvocation.target rootInvocation.callValue =
        .ok workingWorld)
    (initialInstalled :
      InstalledCheckedCoreContract checkpointWorld rootInvocation.target
        rootContract) :
    Reachable registry
      (Mode.preparedRoot (checkpointWorld := checkpointWorld)
        rootContract rootInvocation
        (WorldState.transferBalance_preserves_installed transferred
          initialInstalled)) :=
  .balancedInitial initialInstalled transferred

end Tests
