import Solcore.Semantics.TopLevelExecutionContext
import Solcore.Semantics.WorldStateCode

/-! Exact projections from the root top-level context and direct-call input. -/

set_option autoImplicit false

namespace Solcore.Semantics

namespace TopLevelExecution

@[simp] theorem initialContext_storageAddress
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).context.storageAddress = target := by
  rfl

@[simp] theorem initialContext_storageAccount
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).storageAccount = installed.account := by
  rfl

@[simp] theorem initialContext_checkpointState
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).context.values.checkpoint.state =
      initialWorld := by
  rfl

@[simp] theorem initialContext_workingState
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).context.values.working.1 = initialWorld := by
  rfl

@[simp] theorem initialContext_checkpointEffects
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).context.values.checkpoint.effects =
      initialEffects := by
  rfl

@[simp] theorem initialContext_workingEffects
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    (initialContext installed).context.values.working.2 = initialEffects := by
  rfl

theorem initialWorld_code?
    {initialWorld : WorldState} {target : Address}
    {contract : CheckedCoreContract}
    (installed : InstalledCheckedCoreContract initialWorld target contract) :
    initialWorld.code? target = some contract.code := by
  simp [WorldState.code?, installed.account_present, installed.code_present]

@[simp] theorem preparedContext_storageAddress
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).context.storageAddress =
      target := by
  rfl

@[simp] theorem preparedContext_storageAccount
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).storageAccount =
      installed.account := by
  rfl

@[simp] theorem preparedContext_checkpointState
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).context.values.checkpoint.state =
      checkpointWorld := by
  rfl

@[simp] theorem preparedContext_workingState
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).context.values.working.1 =
      workingWorld := by
  rfl

@[simp] theorem preparedContext_checkpointEffects
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).context.values.checkpoint.effects =
      initialEffects := by
  rfl

@[simp] theorem preparedContext_workingEffects
    {checkpointWorld workingWorld : WorldState}
    {target : Address} {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    (preparedContext (checkpointWorld := checkpointWorld) installed).context.values.working.2 =
      initialEffects := by
  rfl

end TopLevelExecution

namespace TopLevelInvocation

@[simp] theorem executionInputs_codeAddress
    (invocation : TopLevelInvocation) :
    invocation.executionInputs.codeAddress = invocation.target := by
  rfl

@[simp] theorem executionInputs_currentAddress
    (invocation : TopLevelInvocation) :
    invocation.executionInputs.currentAddress = invocation.target := by
  rfl

@[simp] theorem executionInputs_callValue
    (invocation : TopLevelInvocation) :
    invocation.executionInputs.callValue = invocation.callValue := by
  rfl

@[simp] theorem executionInputs_callerAddress
    (invocation : TopLevelInvocation) :
    invocation.executionInputs.callerAddress = invocation.caller := by
  rfl

@[simp] theorem executionInputs_inputData
    (invocation : TopLevelInvocation) :
    invocation.executionInputs.inputData = invocation.inputData := by
  rfl

end TopLevelInvocation

end Solcore.Semantics
