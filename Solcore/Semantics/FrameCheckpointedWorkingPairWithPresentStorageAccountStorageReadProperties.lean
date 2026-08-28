import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead
import Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddressStorageReadProperties

/-! Coherence between proven-present total reads and address-bound optional reads. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- The underlying optional context read returns the total refined read. -/
@[simp] theorem context_readStorage?_eq_some_readStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) :
    context.context.readStorage? slot = some (context.readStorage slot) := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.readStorage?_of_present
      context.context context.storageAccount slot context.storageAccount_present

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
