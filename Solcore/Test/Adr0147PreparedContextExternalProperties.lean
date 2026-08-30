import Solcore.Semantics.TopLevelExecutionContextProperties

/-! External compile consumers for prepared root checkpoint projections. -/

set_option autoImplicit false

namespace Tests

open Solcore.Semantics

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).context.storageAddress =
        target :=
  TopLevelExecution.preparedContext_storageAddress installed

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).storageAccount =
        installed.account :=
  TopLevelExecution.preparedContext_storageAccount installed

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).context.values.checkpoint.state =
        checkpointWorld :=
  TopLevelExecution.preparedContext_checkpointState installed

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).context.values.working.1 =
        workingWorld :=
  TopLevelExecution.preparedContext_workingState installed

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).context.values.checkpoint.effects =
        TopLevelExecution.initialEffects :=
  TopLevelExecution.preparedContext_checkpointEffects installed

example {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (TopLevelExecution.preparedContext
      (checkpointWorld := checkpointWorld) installed).context.values.working.2 =
        TopLevelExecution.initialEffects :=
  TopLevelExecution.preparedContext_workingEffects installed

end Tests
