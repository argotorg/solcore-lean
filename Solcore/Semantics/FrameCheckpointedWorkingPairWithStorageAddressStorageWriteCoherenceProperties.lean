import Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

/-! Values coherence for retained-address and address-parameterized writes. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- Forgetting the retained selector recovers the underlying values write. -/
@[simp] theorem values_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map (fun next => next.values) =
      context.values.writeWorkingStorage?
        context.storageAddress slot value := by
  cases result : context.values.writeWorkingStorage?
      context.storageAddress slot value <;>
    simp [writeStorage?, result]

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
