import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-! Total storage writes through a proven-present selected working Account. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Update the selected Account and its working-state entry in lockstep. -/
def writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    FrameCheckpointedWorkingPairWithPresentStorageAccount
      RollbackState TraceState :=
  let storageAccount := context.storageAccount.storageWrite slot value
  let nextContext :
      FrameCheckpointedWorkingPairWithStorageAddress
        RollbackState TraceState :=
    ⟨context.context.storageAddress,
      ⟨context.context.values.checkpoint,
        (context.context.values.working.1.putAccount
          context.context.storageAddress storageAccount,
          context.context.values.working.2)⟩⟩
  ⟨nextContext, storageAccount, by
    simp [nextContext, WorldState.putAccount, WorldState.account?]⟩

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
