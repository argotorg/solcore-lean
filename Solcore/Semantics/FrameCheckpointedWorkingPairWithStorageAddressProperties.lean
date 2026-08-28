import Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
import Solcore.Semantics.FrameCheckpointedWorkingPairStorageWriteProperties

/-! Branch laws for address-bound checkpointed working storage writes. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- An absent working account makes the address-bound write unavailable. -/
@[simp] theorem writeStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.writeStorage? slot value = none := by
  simp [writeStorage?,
    FrameCheckpointedWorkingPair.writeWorkingStorage?_of_absent,
    absent]

/-- A present working account updates only the addressed working storage. -/
@[simp] theorem writeStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account) (slot value : Core.Word)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.writeStorage? slot value =
      some
        ⟨context.storageAddress,
          ⟨context.values.checkpoint,
            (context.values.working.1.putAccount context.storageAddress
              (account.storageWrite slot value),
              context.values.working.2)⟩⟩ := by
  simp [writeStorage?,
    FrameCheckpointedWorkingPair.writeWorkingStorage?_of_present,
    present]

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
