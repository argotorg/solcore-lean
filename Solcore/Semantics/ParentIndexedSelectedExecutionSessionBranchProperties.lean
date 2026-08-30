import Solcore.Semantics.ParentIndexedFrameInitializationSelectedExecutionProperties
import Solcore.Semantics.ParentIndexedSelectedExecutionSessionProperties

/-! Exact branch laws inherited by every certified selected session. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedExecutionSession

universe u v w

open ParentIndexedSelectedExecutionResult

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

theorem result_eq_storageAbsent_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking) :
    session.result = .storageAbsent ↔
      session.initialization.initialWorld.account? session.storageAddress =
        none := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_storageAbsent_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome

theorem result_eq_codeAbsent_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking) :
    session.result = .codeAbsent ↔
      ∃ context,
        session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            session.storageAddress = some context ∧
        context.context.values.working.1.code? session.inputs.codeAddress =
          none := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_codeAbsent_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome

theorem result_eq_outOfFuel_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State) :
    session.result = .outOfFuel finalContext state ↔
      ∃ context,
        session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            session.storageAddress = some context ∧
        context.runCodeWithStorage? session.inputs session.providedFuel =
          some ⟨finalContext, .outOfFuel state⟩ := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_outOfFuel_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext state

theorem result_eq_fault_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    session.result = .fault finalContext error state ↔
      ∃ context,
        session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            session.storageAddress = some context ∧
        context.runCodeWithStorage? session.inputs session.providedFuel =
          some ⟨finalContext, .fault error state⟩ := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_fault_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext error state

theorem result_eq_unsupported_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    session.result = .unsupported finalContext suspension remainingFuel ↔
      ∃ context,
        session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            session.storageAddress = some context ∧
        context.runCodeWithStorage? session.inputs session.providedFuel =
          some ⟨finalContext, .unsupported suspension remainingFuel⟩ := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_unsupported_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext suspension
      remainingFuel

theorem result_eq_completed_iff
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    session.result = .completed finalContext value store continuation ↔
      ∃ context,
        session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            session.storageAddress = some context ∧
        context.runCodeWithStorage? session.inputs session.providedFuel =
          some ⟨finalContext, .done value store⟩ ∧
        continuation = completedContinuation session.initialization
          session.doneOutcome finalContext value store := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_completed_iff
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext value store
      continuation

/-- Checked selected sessions cannot contain a raw Core machine fault. -/
theorem result_ne_fault
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    session.result ≠ .fault finalContext error state := by
  rw [session.result_eq_run]
  exact
    ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_ne_fault
      session.initialization session.storageAddress session.inputs
      session.providedFuel session.doneOutcome finalContext error state

end Solcore.Semantics.ParentIndexedSelectedExecutionSession
