import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountProperties

/-! Canonical refinement coherence for proven-present optional storage writes. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Optional write followed by refinement recovers the total write result. -/
theorem context_writeStorage?_bind_withPresentStorageAccount?_eq_some_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.context.writeStorage? slot value).bind
        FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount? =
      some (context.writeStorage slot value) := by
  rw [context_writeStorage?_eq_some_writeStorage_context]
  simp only [Option.bind_some]
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_present
      (context.writeStorage slot value).context
      (context.writeStorage slot value).storageAccount
      (context.writeStorage slot value).storageAccount_present

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
