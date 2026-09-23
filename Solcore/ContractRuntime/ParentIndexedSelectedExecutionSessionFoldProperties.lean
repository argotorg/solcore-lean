import Solcore.ContractRuntime.ParentIndexedSelectedExecutionFoldCoherenceProperties
import Solcore.ContractRuntime.ParentIndexedSelectedExecutionSessionCompatibilityProperties

/-! Existing return, revert, and trap folds for completed certified sessions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession

universe u v w x

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {Next : Type x}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- A completed session feeds the existing fold with its exact final values. -/
theorem completed_fold
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      match session.doneOutcome finalContext value store with
      | .returned data =>
          onReturned finalContext.context.values.working data
      | .reverted data =>
          onReverted
            (parentWorking.1,
              ⟨parentWorking.2.rollback,
                finalContext.context.values.working.2.trace⟩)
            data
      | .trapped reason =>
          onTrapped
            (parentWorking.1,
              ⟨parentWorking.2.rollback,
                finalContext.context.values.working.2.trace⟩)
            reason := by
  rw [session.result_eq_run] at completed
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_fold
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext value store
      continuation completed onReturned onReverted onTrapped

theorem completed_fold_returned
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation)
    (data : Bytes)
    (policy : session.doneOutcome finalContext value store = .returned data)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReturned finalContext.context.values.working data := by
  rw [completed_fold session finalContext value store continuation completed
    onReturned onReverted onTrapped, policy]

theorem completed_fold_reverted
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation)
    (data : Bytes)
    (policy : session.doneOutcome finalContext value store = .reverted data)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReverted
        (parentWorking.1,
          ⟨parentWorking.2.rollback,
            finalContext.context.values.working.2.trace⟩)
        data := by
  rw [completed_fold session finalContext value store continuation completed
    onReturned onReverted onTrapped, policy]

theorem completed_fold_trapped
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation)
    (reason : TrapReason)
    (policy : session.doneOutcome finalContext value store = .trapped reason)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onTrapped
        (parentWorking.1,
          ⟨parentWorking.2.rollback,
            finalContext.context.values.working.2.trace⟩)
        reason := by
  rw [completed_fold session finalContext value store continuation completed
    onReturned onReverted onTrapped, policy]

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession
