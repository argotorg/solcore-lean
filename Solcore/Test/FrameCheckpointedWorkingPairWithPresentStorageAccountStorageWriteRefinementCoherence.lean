import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteRefinementCoherenceProperties

/-! Compile-only regressions for optional/total write re-refinement coherence. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word) :
    (context.context.writeStorage? slot value).bind
        Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount? =
      some (context.writeStorage slot value) := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_bind_withPresentStorageAccount?_eq_some_writeStorage
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (firstSlot firstValue secondSlot secondValue : Solcore.Core.Word) :
    ((context.context.writeStorage? firstSlot firstValue).bind
        Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?).bind
        (fun next =>
          (next.context.writeStorage? secondSlot secondValue).bind
            Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?) =
      some
        ((context.writeStorage firstSlot firstValue).writeStorage
          secondSlot secondValue) := by
  rw [
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_bind_withPresentStorageAccount?_eq_some_writeStorage
      context firstSlot firstValue]
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_bind_withPresentStorageAccount?_eq_some_writeStorage
      (context.writeStorage firstSlot firstValue) secondSlot secondValue

end Tests
