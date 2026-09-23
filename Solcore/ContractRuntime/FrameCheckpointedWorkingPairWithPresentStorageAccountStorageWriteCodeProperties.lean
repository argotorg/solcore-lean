import Solcore.ContractRuntime.AccountCodeProperties
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite
import Solcore.ContractRuntime.WorldStateCode
import Solcore.ContractRuntime.WorldStateProperties

/-! Checked-code preservation across total working-storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A storage write preserves checked code at every working-state address. -/
@[simp] theorem workingCode?_writeStorage
    {RollbackState : Type u}
    {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (codeAddress : Address) :
    (context.writeStorage slot value).context.values.working.1.code?
        codeAddress =
      context.context.values.working.1.code? codeAddress := by
  change
    ((context.context.values.working.1.putAccount
        context.context.storageAddress
        (context.storageAccount.storageWrite slot value)).account?
      codeAddress).bind (fun account => account.code?) =
    (context.context.values.working.1.account? codeAddress).bind
      (fun account => account.code?)
  by_cases same : codeAddress = context.context.storageAddress
  · subst codeAddress
    rw [WorldState.account?_putAccount_same]
    rw [context.storageAccount_present]
    simp
  · rw [WorldState.account?_putAccount_other _ _ _ _ same]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
