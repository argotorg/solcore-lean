import Solcore.ContractRuntime.ParentIndexedSelectedCheckedWordExecution

/-! Compile-only consumers for ADR-0144 return and compatibility laws. -/

set_option autoImplicit false

namespace Solcore.Test.ParentIndexedSelectedCheckedWordExecutionContinuationProperties

open ContractRuntime
open ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v w

variable {RollbackState : Type u} {Event : Type v}
variable {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
variable (initialization : ParentIndexedFrameInitialization
  RollbackState Event parentWorking)
variable (storageAddress : Address)
variable (inputs : HostStorageDriver.ExecutionInputs)
variable (fuel additional : Nat)

abbrev Entry := ParentIndexedSelectedCheckedWordExecution
  initialization storageAddress inputs

variable (entry : Entry initialization storageAddress inputs)
variable (completion :
  WordReturnedFrameCompletion RollbackState (FrameTrace Event))
variable (completed : entry.execution.completion? = some completion)

abbrev Continuation := ParentIndexedFrameContinuationContext
  RollbackState Event TrapReason parentWorking

example : entry.returnedCompletion? (TrapReason := TrapReason) = none ↔
    entry.execution.completion? = none :=
  returnedCompletion?_eq_none_iff entry

example : entry.returnedCompletion? (TrapReason := TrapReason) =
    some (completion, entry.toReturnedContinuation completion completed) :=
  returnedCompletion?_of_completion entry completion completed

example :
    (entry.returnedCompletion? (TrapReason := TrapReason)).map Prod.fst =
      entry.execution.completion? :=
  returnedCompletion?_map_fst entry

example : entry.returnedContinuation? (TrapReason := TrapReason) =
    (entry.returnedCompletion? (TrapReason := TrapReason)).map Prod.snd :=
  returnedContinuation?_eq_map_snd entry

example : entry.returnedContinuation? (TrapReason := TrapReason) =
    some (entry.toReturnedContinuation completion completed) :=
  returnedContinuation?_of_completion entry completion completed

example : (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).result =
    ⟨completion.context.context.values.working.1,
      .returned completion.returnData⟩ :=
  result_toReturnedContinuation entry completion completed

example : (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).resolve =
    .returned completion.context.context.values.working.1
      ⟨initialization.workingRollback, parentWorking.2.trace⟩
      completion.returnData :=
  resolve_toReturnedContinuation entry completion completed

example : FrameTrace.IsPrefixOf parentWorking.2.trace
    (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).effectWorking.trace :=
  parentWorking_tracePrefix_toReturnedContinuation entry completion completed

example : (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).stateCheckpoint =
    parentWorking.1 :=
  stateCheckpoint_toReturnedContinuation entry completion completed

example : (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).effectCheckpoint =
    parentWorking.2 :=
  effectCheckpoint_toReturnedContinuation entry completion completed

example : (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).effectWorking =
    ⟨initialization.workingRollback, parentWorking.2.trace⟩ :=
  effectWorking_toReturnedContinuation entry completion completed

example : completion.context.context.values.checkpoint =
    FrameCheckpointSnapshot.fromWorkingPair parentWorking :=
  completion_context_checkpoint entry completion completed

example : completion.context.context.values.working.2 =
    ⟨initialization.workingRollback, parentWorking.2.trace⟩ :=
  completion_context_workingEffects entry completion completed

example : (entry.toReturnedContinuation
      (TrapReason := TrapReason) completion completed).toFrameContinuationContext =
    (completion.toFrameContinuationContext :
      FrameContinuationContext
        RollbackState (FrameTrace Event) TrapReason) :=
  toFrameContinuationContext_toReturnedContinuation entry completion completed

variable (continuation : Continuation (TrapReason := TrapReason))

example : entry.returnedCompletion? (TrapReason := TrapReason) =
      some (completion, continuation) ↔
    ∃ exactCompletion : entry.execution.completion? = some completion,
      continuation = entry.toReturnedContinuation completion exactCompletion :=
  returnedCompletion?_eq_some_iff entry completion continuation

example : (entry.resumeWithFuel additional).toReturnedContinuation
      (TrapReason := TrapReason) completion
      (entry.completion?_resumeWithFuel_of_some
        additional completion completed) =
    entry.toReturnedContinuation completion completed :=
  toReturnedContinuation_resumeWithFuel entry additional completion completed

example : (entry.resumeWithFuel additional).returnedCompletion?
      (TrapReason := TrapReason) =
    some (completion, entry.toReturnedContinuation completion completed) :=
  returnedCompletion?_resumeWithFuel_of_completion
    entry additional completion completed

example : (entry.resumeWithFuel additional).returnedCompletion?
      (TrapReason := TrapReason) =
    entry.returnedCompletion? (TrapReason := TrapReason) :=
  returnedCompletion?_resumeWithFuel_stable entry additional completion completed

example : (entry.resumeWithFuel additional).returnedContinuation?
      (TrapReason := TrapReason) =
    entry.returnedContinuation? (TrapReason := TrapReason) :=
  returnedContinuation?_resumeWithFuel_stable
    entry additional completion completed

variable (doneOutcome :
  HostStorageDriver.Context RollbackState (FrameTrace Event) →
    Core.Value → Core.Store → FrameOutcome TrapReason)

example : start? initialization storageAddress inputs fuel = none ↔
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome = .storageAbsent :=
  start?_eq_none_iff_legacy_storageAbsent
    initialization storageAddress inputs fuel doneOutcome

example : entry.initialContext.runCodeWithStorage? inputs fuel = none ↔
    entry.execution.selection = .codeAbsent :=
  legacy_runCodeWithStorage?_eq_none_iff_codeAbsent entry fuel

variable (wordCode : CheckedHostCoreWordProgram)
variable (selectedWord : entry.execution.selection = .word wordCode)

example : entry.execution.execution?.map Prod.snd =
    entry.initialContext.runCodeWithStorage?
      inputs entry.execution.providedFuel :=
  execution?_map_snd_eq_legacy_runCodeWithStorage?_of_word
    entry wordCode selectedWord

variable (canonical :
  doneOutcome completion.context (.word completion.word) completion.store =
    .returned completion.returnData)

example : initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs entry.execution.providedFuel doneOutcome =
    .completed completion.context (.word completion.word) completion.store
      (entry.toReturnedContinuation completion completed) :=
  legacy_parent_result_eq_completed_of_canonical_word
    entry completion completed doneOutcome canonical

end Solcore.Test.ParentIndexedSelectedCheckedWordExecutionContinuationProperties
