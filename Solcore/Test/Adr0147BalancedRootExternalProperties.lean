import Solcore.Semantics.OneLevelNestedExecutionBalancedRootProperties

/-! External compile consumers for post-transfer root initialization laws. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics
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

end Tests
