import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuationWithInputs
import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccount
import Solcore.Semantics.ParentIndexedFrameContinuationConstruction

/-! Parent-indexed continuation construction with immutable execution input. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v w

/-- Lift the same input through storage selection, execution, and completion. -/
def runCodeWithStorageParentIndexedContinuationContextWithInputs?
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
    (context.runCodeWithStorageContinuationContextWithInputs?
      inputs fuel doneOutcome).map fun completed =>
        completed.map fun continuation =>
          ParentIndexedFrameContinuationContext.fromTraceExtension
            parentWorking initialization.workingRollback
            initialization.initialTraceExtension continuation.result

end Solcore.Semantics.ParentIndexedFrameInitialization
