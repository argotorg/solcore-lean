import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress
import Solcore.ContractRuntime.WorldStateStorageRead

/-! Working-storage reads through a retained frame storage address. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- Read one slot from the stored address in the working WorldState. -/
def readStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot : Core.Word) : Option Core.Word :=
  context.values.working.1.readStorage? context.storageAddress slot

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress
