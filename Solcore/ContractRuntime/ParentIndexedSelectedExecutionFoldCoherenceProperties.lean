import Solcore.ContractRuntime.ParentIndexedFrameResolutionFold
import Solcore.ContractRuntime.ParentIndexedSelectedExecutionContinuationCoherenceProperties
import Solcore.ContractRuntime.ParentIndexedSelectedExecutionResumption

/-! Existing return, revert, and trap folds for branch-complete completion. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w x

open ParentIndexedSelectedExecutionResult

/--
An actual completed carrier feeds the existing fold with its exact final
working values and its exact indexed parent checkpoint.
-/
theorem runCodeWithStorageParentIndexedResult_completed_fold
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      match doneOutcome finalContext value store with
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
  have plainEq :=
    runCodeWithStorageParentIndexedResult_completed_toFrameContinuationContext
      initialization storageAddress inputs fuel doneOutcome finalContext
      value store continuation completed
  have effectWorkingEq := congrArg
    (fun current : FrameContinuationContext
        RollbackState (FrameTrace Event) TrapReason => current.effectWorking)
    plainEq
  have resultEq := congrArg
    (fun current : FrameContinuationContext
        RollbackState (FrameTrace Event) TrapReason => current.result)
    plainEq
  have stateCheckpointEq :
      continuation.stateCheckpoint = parentWorking.1 :=
    congrArg Prod.fst continuation.checkpoint_eq_parentWorking
  have effectCheckpointEq :
      continuation.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd continuation.checkpoint_eq_parentWorking
  unfold ParentIndexedFrameContinuationContext.foldResolutionWithTrapRollback
  rw [stateCheckpointEq, effectCheckpointEq, effectWorkingEq, resultEq]
  cases outcomeEq : doneOutcome finalContext value store <;>
    simp [FrameContinuationContext.fromCheckpointedWorkingPair]

theorem runCodeWithStorageParentIndexedResult_completed_fold_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation)
    (data : Bytes)
    (policy : doneOutcome finalContext value store = .returned data)
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
  rw [runCodeWithStorageParentIndexedResult_completed_fold
    initialization storageAddress inputs fuel doneOutcome finalContext
    value store continuation completed onReturned onReverted onTrapped,
    policy]

theorem runCodeWithStorageParentIndexedResult_completed_fold_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation)
    (data : Bytes)
    (policy : doneOutcome finalContext value store = .reverted data)
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
  rw [runCodeWithStorageParentIndexedResult_completed_fold
    initialization storageAddress inputs fuel doneOutcome finalContext
    value store continuation completed onReturned onReverted onTrapped,
    policy]

theorem runCodeWithStorageParentIndexedResult_completed_fold_trapped
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value) (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .completed finalContext value store continuation)
    (reason : TrapReason)
    (policy : doneOutcome finalContext value store = .trapped reason)
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
  rw [runCodeWithStorageParentIndexedResult_completed_fold
    initialization storageAddress inputs fuel doneOutcome finalContext
    value store continuation completed onReturned onReverted onTrapped,
    policy]

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult

universe u v w x

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {Next : Type x}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Exact terminal identity also preserves every existing fold observation. -/
theorem resumeWithFuel_completed_fold
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation resumedContinuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat)
    (resumed :
      resumeWithFuel (.completed context value store continuation)
          initialization inputs doneOutcome additional =
        .completed context value store resumedContinuation)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Bytes → Next)
    (onTrapped :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          TrapReason → Next) :
    resumedContinuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped := by
  rw [resumeWithFuel_completed] at resumed
  cases resumed
  rfl

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult
