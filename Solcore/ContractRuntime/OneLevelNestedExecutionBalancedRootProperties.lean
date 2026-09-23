import Solcore.ContractRuntime.OneLevelNestedExecutionState
import Solcore.ContractRuntime.TopLevelExecutionContextProperties

/-! Exact projections of a root prepared after top-level value transfer. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.OneLevelNestedExecution.RootFrame

@[simp] theorem prepared_storageAddress
    {checkpointWorld workingWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    (prepared (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed).context.context.storageAddress = rootInvocation.target := by
  rfl

@[simp] theorem prepared_checkpointState
    {checkpointWorld workingWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    (prepared (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed).context.context.values.checkpoint.state =
        checkpointWorld := by
  rfl

@[simp] theorem prepared_workingState
    {checkpointWorld workingWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    (prepared (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed).context.context.values.working.1 = workingWorld := by
  rfl

@[simp] theorem prepared_storageAccount
    {checkpointWorld workingWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    (prepared (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed).context.storageAccount = installed.account := by
  rfl

@[simp] theorem prepared_state
    {checkpointWorld workingWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (installed :
      InstalledCheckedCoreContract workingWorld rootInvocation.target
        rootContract) :
    (prepared (checkpointWorld := checkpointWorld) rootContract rootInvocation
      installed).state =
        Core.State.initial rootContract.code.program.body
          Core.hostEnvironment := by
  rfl

end Solcore.ContractRuntime.OneLevelNestedExecution.RootFrame
