import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite
import Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddressProperties

/-! Coherence between proven-present total and address-bound optional writes. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- The underlying optional write returns the total write's updated context. -/
@[simp] theorem context_writeStorage?_eq_some_writeStorage_context
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    context.context.writeStorage? slot value =
      some (context.writeStorage slot value).context := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.writeStorage?_of_present
      context.context context.storageAccount slot value
      context.storageAccount_present

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
