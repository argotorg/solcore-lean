import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuation
import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccount
import Solcore.Semantics.ParentIndexedFrameContinuationConstruction

/-! Parent-indexed continuation construction after selected handled execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v w

/--
Lift parent-indexed initialization through present storage, selected code, and
completed handled execution without merging any optional boundary.
-/
def runCodeWithStorageParentIndexedContinuationContext?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress codeAddress : Address)
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
      codeAddress fuel doneOutcome).map fun completed =>
        completed.map fun continuation =>
          ParentIndexedFrameContinuationContext.fromTraceExtension
            parentWorking initialization.workingRollback
            initialization.initialTraceExtension continuation.result

end Solcore.Semantics.ParentIndexedFrameInitialization
