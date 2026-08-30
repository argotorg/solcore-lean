import Solcore.Semantics.ParentIndexedSelectedExecutionSessionFoldProperties

/-! Compile-only consumers for certified selected-session proof contracts. -/

set_option autoImplicit false

namespace Solcore.Test.ParentIndexedSelectedExecutionSessionProperties

open Semantics
open Semantics.ParentIndexedSelectedExecutionResult

universe u v w x

variable {RollbackState : Type u} {Event : Type v}
variable {TrapReason : Type w} {Next : Type x}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

abbrev Context :=
  HostStorageDriver.Context RollbackState (FrameTrace Event)

variable (initialization : ParentIndexedFrameInitialization
  RollbackState Event parentWorking)
variable (storageAddress : Address)
variable (inputs : HostStorageDriver.ExecutionInputs)
variable (doneOutcome : Context →
  Core.Value → Core.Store → FrameOutcome TrapReason)
variable (providedFuel additional first second : Nat)

example :
    (ParentIndexedSelectedExecutionSession.start initialization storageAddress
      inputs doneOutcome providedFuel).initialization = initialization :=
  ParentIndexedSelectedExecutionSession.start_initialization
    initialization storageAddress inputs doneOutcome providedFuel

example :
    (ParentIndexedSelectedExecutionSession.start initialization storageAddress
      inputs doneOutcome providedFuel).storageAddress = storageAddress :=
  ParentIndexedSelectedExecutionSession.start_storageAddress
    initialization storageAddress inputs doneOutcome providedFuel

example :
    (ParentIndexedSelectedExecutionSession.start initialization storageAddress
      inputs doneOutcome providedFuel).inputs = inputs :=
  ParentIndexedSelectedExecutionSession.start_inputs
    initialization storageAddress inputs doneOutcome providedFuel

example :
    (ParentIndexedSelectedExecutionSession.start initialization storageAddress
      inputs doneOutcome providedFuel).doneOutcome = doneOutcome :=
  ParentIndexedSelectedExecutionSession.start_doneOutcome
    initialization storageAddress inputs doneOutcome providedFuel

example :
    (ParentIndexedSelectedExecutionSession.start initialization storageAddress
      inputs doneOutcome providedFuel).providedFuel = providedFuel :=
  ParentIndexedSelectedExecutionSession.start_providedFuel
    initialization storageAddress inputs doneOutcome providedFuel

example :
    (ParentIndexedSelectedExecutionSession.start initialization storageAddress
      inputs doneOutcome providedFuel).result =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs providedFuel doneOutcome :=
  ParentIndexedSelectedExecutionSession.start_result
    initialization storageAddress inputs doneOutcome providedFuel

variable (session : ParentIndexedSelectedExecutionSession
  RollbackState Event TrapReason parentWorking)

example : (session.resumeWithFuel additional).initialization =
    session.initialization :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_initialization
    session additional

example : (session.resumeWithFuel additional).storageAddress =
    session.storageAddress :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_storageAddress
    session additional

example : (session.resumeWithFuel additional).inputs = session.inputs :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_inputs
    session additional

example : (session.resumeWithFuel additional).doneOutcome =
    session.doneOutcome :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_doneOutcome
    session additional

example : (session.resumeWithFuel additional).providedFuel =
    session.providedFuel + additional :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_providedFuel
    session additional

example : (session.resumeWithFuel additional).result =
    session.result.resumeWithFuel session.initialization session.inputs
      session.doneOutcome additional :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_result
    session additional

example : (session.resumeWithFuel additional).result =
    session.initialization.runCodeWithStorageParentIndexedResult
      session.storageAddress session.inputs
      (session.providedFuel + additional) session.doneOutcome :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_result_eq_run
    session additional

example : session = ParentIndexedSelectedExecutionSession.start
    session.initialization session.storageAddress session.inputs
    session.doneOutcome session.providedFuel :=
  ParentIndexedSelectedExecutionSession.eq_start session

example : session.resumeWithFuel additional =
    ParentIndexedSelectedExecutionSession.start session.initialization
      session.storageAddress session.inputs session.doneOutcome
      (session.providedFuel + additional) :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_eq_start
    session additional

example :
    (ParentIndexedSelectedExecutionSession.start initialization storageAddress
      inputs doneOutcome providedFuel).resumeWithFuel additional =
      ParentIndexedSelectedExecutionSession.start initialization storageAddress
        inputs doneOutcome (providedFuel + additional) :=
  ParentIndexedSelectedExecutionSession.start_resumeWithFuel
    initialization storageAddress inputs doneOutcome providedFuel additional

example : session.resumeWithFuel 0 = session :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_zero session

example : (session.resumeWithFuel first).resumeWithFuel second =
    session.resumeWithFuel (first + second) :=
  ParentIndexedSelectedExecutionSession.resumeWithFuel_add
    session first second

variable (finalContext : Context) (state faultState : Core.State)
variable (error : Core.MachineFault)
variable (suspension : Core.HostSuspension) (remainingFuel : Nat)
variable (value : Core.Value) (store : Core.Store)
variable (continuation : ParentIndexedFrameContinuationContext
  RollbackState Event TrapReason parentWorking)

example : session.result = .storageAbsent ↔
    session.initialization.initialWorld.account? session.storageAddress = none :=
  ParentIndexedSelectedExecutionSession.result_eq_storageAbsent_iff session

example : session.result = .codeAbsent ↔
    ∃ context,
      session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          session.storageAddress = some context ∧
      context.context.values.working.1.code? session.inputs.codeAddress = none :=
  ParentIndexedSelectedExecutionSession.result_eq_codeAbsent_iff session

example : session.result = .outOfFuel finalContext state ↔
    ∃ context,
      session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          session.storageAddress = some context ∧
      context.runCodeWithStorage? session.inputs session.providedFuel =
        some ⟨finalContext, .outOfFuel state⟩ :=
  ParentIndexedSelectedExecutionSession.result_eq_outOfFuel_iff
    session finalContext state

example : session.result = .fault finalContext error faultState ↔
    ∃ context,
      session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          session.storageAddress = some context ∧
      context.runCodeWithStorage? session.inputs session.providedFuel =
        some ⟨finalContext, .fault error faultState⟩ :=
  ParentIndexedSelectedExecutionSession.result_eq_fault_iff
    session finalContext error faultState

example : session.result =
      .unsupported finalContext suspension remainingFuel ↔
    ∃ context,
      session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          session.storageAddress = some context ∧
      context.runCodeWithStorage? session.inputs session.providedFuel =
        some ⟨finalContext, .unsupported suspension remainingFuel⟩ :=
  ParentIndexedSelectedExecutionSession.result_eq_unsupported_iff
    session finalContext suspension remainingFuel

example : session.result =
      .completed finalContext value store continuation ↔
    ∃ context,
      session.initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          session.storageAddress = some context ∧
      context.runCodeWithStorage? session.inputs session.providedFuel =
          some ⟨finalContext, .done value store⟩ ∧
        continuation = completedContinuation session.initialization
          session.doneOutcome finalContext value store :=
  ParentIndexedSelectedExecutionSession.result_eq_completed_iff
    session finalContext value store continuation

example : session.result ≠ .fault finalContext error faultState :=
  ParentIndexedSelectedExecutionSession.result_ne_fault
    session finalContext error faultState

example : session.result.toLegacy =
    session.initialization.runCodeWithStorageParentIndexedContinuationContext?
      session.storageAddress session.inputs session.providedFuel
      session.doneOutcome :=
  ParentIndexedSelectedExecutionSession.result_toLegacy session

variable (completed : session.result =
  .completed finalContext value store continuation)

example : continuation.toFrameContinuationContext =
    FrameContinuationContext.fromCheckpointedWorkingPair
      finalContext.context.values
      (session.doneOutcome finalContext value store) :=
  ParentIndexedSelectedExecutionSession.completed_toFrameContinuationContext
    session finalContext value store continuation completed

example :
    session.initialization.runCodeWithStorageParentIndexedContinuationContext?
      session.storageAddress session.inputs session.providedFuel
        session.doneOutcome = some (some (some continuation)) :=
  ParentIndexedSelectedExecutionSession.completed_toLegacy
    session finalContext value store continuation completed

variable (onReturned onReverted :
  (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
    Bytes → Next)
variable (onTrapped :
  (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
    TrapReason → Next)
variable (data : Bytes) (reason : TrapReason)

example : continuation.foldResolutionWithTrapRollback
      onReturned onReverted onTrapped =
    match session.doneOutcome finalContext value store with
    | .returned bytes =>
        onReturned finalContext.context.values.working bytes
    | .reverted bytes =>
        onReverted (parentWorking.1,
          ⟨parentWorking.2.rollback,
            finalContext.context.values.working.2.trace⟩) bytes
    | .trapped trap =>
        onTrapped (parentWorking.1,
          ⟨parentWorking.2.rollback,
            finalContext.context.values.working.2.trace⟩) trap :=
  ParentIndexedSelectedExecutionSession.completed_fold session finalContext
    value store continuation completed onReturned onReverted onTrapped

example (policy :
    session.doneOutcome finalContext value store = .returned data) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReturned finalContext.context.values.working data :=
  ParentIndexedSelectedExecutionSession.completed_fold_returned
    session finalContext value store continuation completed data policy
    onReturned onReverted onTrapped

example (policy :
    session.doneOutcome finalContext value store = .reverted data) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReverted (parentWorking.1,
        ⟨parentWorking.2.rollback,
          finalContext.context.values.working.2.trace⟩) data :=
  ParentIndexedSelectedExecutionSession.completed_fold_reverted
    session finalContext value store continuation completed data policy
    onReturned onReverted onTrapped

example (policy :
    session.doneOutcome finalContext value store = .trapped reason) :
    continuation.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onTrapped (parentWorking.1,
        ⟨parentWorking.2.rollback,
          finalContext.context.values.working.2.trace⟩) reason :=
  ParentIndexedSelectedExecutionSession.completed_fold_trapped
    session finalContext value store continuation completed reason policy
    onReturned onReverted onTrapped

end Solcore.Test.ParentIndexedSelectedExecutionSessionProperties
