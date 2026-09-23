import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageRead
import Solcore.ContractRuntime.WorldStateStorageReadProperties

/-! Branch laws for address-bound working storage reads. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- An absent addressed working Account makes the read unavailable. -/
@[simp] theorem readStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot : Core.Word)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.readStorage? slot = none := by
  exact WorldState.readStorage?_of_absent context.values.working.1
    context.storageAddress slot absent

/-- A present addressed working Account supplies its zero-default slot read. -/
@[simp] theorem readStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account)
    (slot : Core.Word)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.readStorage? slot = some (account.storageRead slot) := by
  exact WorldState.readStorage?_of_present context.values.working.1
    context.storageAddress account slot present

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress
