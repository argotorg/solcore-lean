import Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuation
import Solcore.ContractRuntime.ParentIndexedFrameInitializationSelectedExecution
import Solcore.ContractRuntime.ParentIndexedSelectedExecutionCompatibility

/-! Exact compatibility with the existing nested-option parent entry point. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

open ParentIndexedSelectedExecutionResult

/-- Erasing a branch-complete run gives the unchanged legacy result exactly. -/
theorem runCodeWithStorageParentIndexedResult_toLegacy
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).toLegacy =
      initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs fuel doneOutcome := by
  unfold runCodeWithStorageParentIndexedResult
  unfold runCodeWithStorageParentIndexedContinuationContext?
  cases initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress with
  | none => rfl
  | some context =>
      simp only [Option.map_some]
      unfold FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?
      cases context.runCodeWithStorage? inputs fuel with
      | none => rfl
      | some result =>
          cases result with
          | mk finalContext outcome => cases outcome <;> rfl

end Solcore.ContractRuntime.ParentIndexedFrameInitialization
