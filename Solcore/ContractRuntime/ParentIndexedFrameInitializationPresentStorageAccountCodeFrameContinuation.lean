import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuation
import Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccount
import Solcore.ContractRuntime.ParentIndexedFrameContinuationConstruction

/-! Parent-indexed continuation construction with immutable execution input. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

/-- Lift the same input through storage selection, execution, and completion. -/
def runCodeWithStorageParentIndexedContinuationContext?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option
      (Option
        (Option
          (ParentIndexedFrameContinuationContext
            RollbackState Event TrapReason parentWorking))) :=
  (initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress).map fun context =>
    (context.runCodeWithStorageContinuationContext?
      inputs fuel doneOutcome).map fun completed =>
        completed.map fun continuation =>
          ParentIndexedFrameContinuationContext.fromTraceExtension
            parentWorking initialization.workingRollback
            initialization.initialTraceExtension continuation.result

end Solcore.ContractRuntime.ParentIndexedFrameInitialization
