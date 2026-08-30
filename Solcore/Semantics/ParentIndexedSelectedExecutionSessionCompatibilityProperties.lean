import Solcore.Semantics.ParentIndexedSelectedExecutionCompatibilityProperties
import Solcore.Semantics.ParentIndexedSelectedExecutionContinuationCoherenceProperties
import Solcore.Semantics.ParentIndexedSelectedExecutionSessionBranchProperties

/-! Legacy and completed-continuation coherence for certified sessions. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedExecutionSession

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Erasing a session result reproduces the unchanged nested-option API. -/
theorem result_toLegacy
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking) :
    session.result.toLegacy =
      session.initialization.runCodeWithStorageParentIndexedContinuationContext?
        session.storageAddress session.inputs session.providedFuel
        session.doneOutcome := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_toLegacy
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome

/-- A completed session carries the exact existing plain continuation. -/
theorem completed_toFrameContinuationContext
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation) :
    continuation.toFrameContinuationContext =
      FrameContinuationContext.fromCheckpointedWorkingPair
        finalContext.context.values
        (session.doneOutcome finalContext value store) := by
  rw [session.result_eq_run] at completed
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_toFrameContinuationContext
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext value store
      continuation completed

/-- The legacy entry point exposes the same completed indexed continuation. -/
theorem completed_toLegacy
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      session.result = .completed finalContext value store continuation) :
    session.initialization.runCodeWithStorageParentIndexedContinuationContext?
        session.storageAddress session.inputs session.providedFuel
        session.doneOutcome =
      some (some (some continuation)) := by
  rw [session.result_eq_run] at completed
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_toLegacy
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext value store
      continuation completed

end Solcore.Semantics.ParentIndexedSelectedExecutionSession
