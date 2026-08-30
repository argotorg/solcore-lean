import Solcore.Semantics.ParentIndexedFrameInitializationSelectedExecutionResumptionProperties
import Solcore.Semantics.ParentIndexedSelectedExecutionFoldCoherenceProperties

/-! Compile-only consumers for branch-complete selected execution laws. -/

set_option autoImplicit false

namespace Solcore.Test.ParentIndexedSelectedExecutionProperties

open Semantics
open Semantics.ParentIndexedSelectedExecutionResult

universe u v w x

variable {RollbackState : Type u} {Event : Type v}
variable {TrapReason : Type w} {Next : Type x}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

abbrev Context :=
  HostStorageDriver.Context RollbackState (FrameTrace Event)

abbrev Result := ParentIndexedSelectedExecutionResult
  RollbackState Event TrapReason parentWorking

variable (initialization : ParentIndexedFrameInitialization
  RollbackState Event parentWorking)
variable (storageAddress : Address)
variable (inputs : HostStorageDriver.ExecutionInputs)
variable (fuel additional first second : Nat)
variable (doneOutcome : Context →
  Core.Value → Core.Store → FrameOutcome TrapReason)
variable (context finalContext : Context)
variable (state faultState : Core.State)
variable (error : Core.MachineFault)
variable (value : Core.Value) (store : Core.Store)
variable (continuation resumedContinuation :
  ParentIndexedFrameContinuationContext
    RollbackState Event TrapReason parentWorking)
variable (driverResult : HostDriverResult Context)
variable (onReturned onReverted :
  (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
    Bytes → Next)
variable (onTrapped :
  (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
    TrapReason → Next)
variable (data : Bytes) (reason : TrapReason)

example :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome = .storageAbsent ↔
      initialization.initialWorld.account? storageAddress = none := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_storageAbsent_iff
      initialization storageAddress inputs fuel doneOutcome

example :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome = .codeAbsent ↔
      ∃ selected,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some selected ∧
        selected.context.values.working.1.code? inputs.codeAddress = none := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_codeAbsent_iff
      initialization storageAddress inputs fuel doneOutcome

example :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome =
      .outOfFuel finalContext state ↔
    ∃ selected,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some selected ∧
      selected.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .outOfFuel state⟩ := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_outOfFuel_iff
      initialization storageAddress inputs fuel doneOutcome finalContext state

example :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome =
      .fault finalContext error faultState ↔
    ∃ selected,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some selected ∧
      selected.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .fault error faultState⟩ := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_fault_iff
      initialization storageAddress inputs fuel doneOutcome
      finalContext error faultState

example :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome =
      .completed finalContext value store continuation ↔
    ∃ selected,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some selected ∧
      selected.runCodeWithStorage? inputs fuel =
          some ⟨finalContext, .done value store⟩ ∧
        continuation = completedContinuation
          initialization doneOutcome finalContext value store := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_completed_iff
      initialization storageAddress inputs fuel doneOutcome
      finalContext value store continuation

example : initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome ≠
    .fault finalContext error faultState := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_ne_fault
      initialization storageAddress inputs fuel doneOutcome
      finalContext error faultState

example :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).toLegacy =
      initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs fuel doneOutcome := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_toLegacy
      initialization storageAddress inputs fuel doneOutcome

example : resumeWithFuel (.storageAbsent : Result)
    initialization inputs doneOutcome additional = .storageAbsent := by
  exact resumeWithFuel_storageAbsent initialization inputs doneOutcome additional

example : resumeWithFuel (.codeAbsent : Result)
    initialization inputs doneOutcome additional = .codeAbsent := by
  exact resumeWithFuel_codeAbsent initialization inputs doneOutcome additional

example : resumeWithFuel (.outOfFuel context state : Result)
      initialization inputs doneOutcome additional =
    classify initialization doneOutcome
      (HostStorageDriver.run context inputs additional state) := by
  exact resumeWithFuel_outOfFuel context state initialization inputs
    doneOutcome additional

example : resumeWithFuel (.fault context error faultState : Result)
      initialization inputs doneOutcome additional =
    .fault context error faultState := by
  exact resumeWithFuel_fault context error faultState initialization inputs
    doneOutcome additional

example : resumeWithFuel
      (.completed context value store continuation : Result)
      initialization inputs doneOutcome additional =
    .completed context value store continuation := by
  exact resumeWithFuel_completed context value store continuation
    initialization inputs doneOutcome additional

example : resumeWithFuel (classify initialization doneOutcome driverResult)
      initialization inputs doneOutcome additional =
    classify initialization doneOutcome
      (driverResult.resumeWithFuel
        (@HostStorageDriver.handler RollbackState (FrameTrace Event) inputs)
        additional) := by
  exact resumeWithFuel_classify initialization inputs doneOutcome
    driverResult additional

example (result : Result) :
    resumeWithFuel
        (resumeWithFuel result initialization inputs doneOutcome first)
        initialization inputs doneOutcome second =
      resumeWithFuel result initialization inputs doneOutcome
        (first + second) := by
  exact resumeWithFuel_add result initialization inputs doneOutcome first second

example : resumeWithFuel (.outOfFuel context state : Result)
      initialization inputs doneOutcome additional =
      .completed finalContext value store continuation ↔
    HostStorageDriver.run context inputs additional state =
        ⟨finalContext, .done value store⟩ ∧
      continuation = completedContinuation
        initialization doneOutcome finalContext value store := by
  exact resumeWithFuel_outOfFuel_eq_completed_iff context state
    initialization inputs doneOutcome additional finalContext value store
    continuation

example :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome additional =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs (fuel + additional) doneOutcome := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_resumeWithFuel
      initialization storageAddress inputs fuel additional doneOutcome

example :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome 0 =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_resumeWithFuel_zero
      initialization storageAddress inputs fuel doneOutcome

example :
    ((initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome first).resumeWithFuel
          initialization inputs doneOutcome second =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs (fuel + (first + second)) doneOutcome := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_resumeWithFuel_add
      initialization storageAddress inputs fuel first second doneOutcome

example :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome additional ≠
      .fault finalContext error faultState := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_resumeWithFuel_ne_fault
      initialization storageAddress inputs fuel additional doneOutcome
      finalContext error faultState

variable (completed : initialization.runCodeWithStorageParentIndexedResult
  storageAddress inputs fuel doneOutcome =
    .completed finalContext value store continuation)

example : continuation.toFrameContinuationContext =
    FrameContinuationContext.fromCheckpointedWorkingPair
      finalContext.context.values
      (doneOutcome finalContext value store) := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_toFrameContinuationContext
      initialization storageAddress inputs fuel doneOutcome finalContext
      value store continuation completed

example : initialization.runCodeWithStorageParentIndexedContinuationContext?
      storageAddress inputs fuel doneOutcome =
    some (some (some continuation)) := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_toLegacy
      initialization storageAddress inputs fuel doneOutcome finalContext
      value store continuation completed

example : continuation.foldResolutionWithTrapRollback
      onReturned onReverted onTrapped =
    match doneOutcome finalContext value store with
    | .returned bytes =>
        onReturned finalContext.context.values.working bytes
    | .reverted bytes =>
        onReverted (parentWorking.1,
          ⟨parentWorking.2.rollback,
            finalContext.context.values.working.2.trace⟩) bytes
    | .trapped trap =>
        onTrapped (parentWorking.1,
          ⟨parentWorking.2.rollback,
            finalContext.context.values.working.2.trace⟩) trap := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_fold
      initialization storageAddress inputs fuel doneOutcome finalContext
      value store continuation completed onReturned onReverted onTrapped

example (policy : doneOutcome finalContext value store = .returned data) :
    continuation.foldResolutionWithTrapRollback
      onReturned onReverted onTrapped =
        onReturned finalContext.context.values.working data := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_fold_returned
      initialization storageAddress inputs fuel doneOutcome finalContext
      value store continuation completed data policy
      onReturned onReverted onTrapped

example (policy : doneOutcome finalContext value store = .reverted data) :
    continuation.foldResolutionWithTrapRollback
      onReturned onReverted onTrapped =
    onReverted (parentWorking.1,
      ⟨parentWorking.2.rollback,
        finalContext.context.values.working.2.trace⟩) data := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_fold_reverted
      initialization storageAddress inputs fuel doneOutcome finalContext
      value store continuation completed data policy
      onReturned onReverted onTrapped

example (policy : doneOutcome finalContext value store = .trapped reason) :
    continuation.foldResolutionWithTrapRollback
      onReturned onReverted onTrapped =
    onTrapped (parentWorking.1,
      ⟨parentWorking.2.rollback,
        finalContext.context.values.working.2.trace⟩) reason := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_completed_fold_trapped
      initialization storageAddress inputs fuel doneOutcome finalContext
      value store continuation completed reason policy
      onReturned onReverted onTrapped

example (resumed : resumeWithFuel
    (.completed context value store continuation : Result)
      initialization inputs doneOutcome additional =
    .completed context value store resumedContinuation) :
    resumedContinuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped := by
  exact resumeWithFuel_completed_fold context value store continuation
    resumedContinuation initialization inputs doneOutcome additional resumed
    onReturned onReverted onTrapped

end Solcore.Test.ParentIndexedSelectedExecutionProperties
