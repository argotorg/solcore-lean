import Solcore.ContractRuntime.Internal.CheckedCoreProgram
import Solcore.ContractRuntime.Internal.SelectedWordExecution
import Solcore.ContractRuntime.Internal.ParentIndexedFrames
import Solcore.ContractRuntime.Internal.FrameLaws
import Solcore.ContractRuntime.Internal.ParentIndexedExecution
import Solcore.ContractRuntime.Internal.ContractLaws

/-!
# Selected execution tests

Selected and parent-indexed checked execution of Word programs: sessions, resumption, code selection
and their proof contracts.
-/

section
-- leanmerge: from Solcore.Test.CheckedCoreProgram
/-! Admission, stateful execution, and safety regressions for checked code. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def cellProgram : Program := {
  resultType := .cell .bool
  body := .newCell .bool (.bool true)
}

private def rejectedProgram : Program := {
  resultType := .unit
  body := .var 0
}

private theorem cellProgram_checked : cellProgram.check = true := by
  decide

private theorem rejectedProgram_rejected : rejectedProgram.check = false := by
  decide

private def checkedCellProgram : CheckedCoreProgram :=
  ⟨cellProgram, cellProgram_checked⟩

private theorem compileTimeAdmissionRegression :
    CheckedCoreProgram.ofProgram? cellProgram = some checkedCellProgram := by
  exact CheckedCoreProgram.ofProgram?_of_checked
    cellProgram cellProgram_checked

private theorem compileTimeRejectionRegression :
    CheckedCoreProgram.ofProgram? rejectedProgram = none := by
  exact CheckedCoreProgram.ofProgram?_of_rejected
    rejectedProgram rejectedProgram_rejected

private theorem compileTimeCompletionRegression :
    ∃ fuel value store,
      checkedCellProgram.runStateful fuel = .done value store := by
  obtain ⟨required, _, store, value, _, _, completes⟩ :=
    checkedCellProgram.runStateful_has_sufficient_fuel (Evaluates.newCell .bool)
  exact ⟨required, value, store, completes required (Nat.le_refl required)⟩

private theorem compileTimeNoFaultRegression
    (fuel : Nat)
    (error : MachineFault)
    (faultState : State) :
    checkedCellProgram.runStateful fuel ≠ .fault error faultState :=
  checkedCellProgram.runStateful_ne_fault fuel error faultState

private theorem compileTimeBoundedSafetyRegression (fuel : Nat) :
    (checkedCellProgram.runStateful fuel).HasType (.cell .bool) :=
  checkedCellProgram.runStateful_has_type fuel

/-- Exhaustion preserves the pending allocation rather than resetting entry. -/
private theorem compileTimeCheckpointRegression :
    StateHasType ⟨.ret (.bool true), [.newCellApply .bool], []⟩ (.cell .bool) := by
  exact well_typed_runStateful_preserves_checkpoint_type
    (initial_state_has_type (Program.check_full_sound cellProgram_checked).bodyHasType)
    (fuel := 2) rfl

private theorem compileTimeTypedResumeRegression (additional : Nat) :
    (runStateful additional
      ⟨.ret (.bool true), [.newCellApply .bool], []⟩).HasType (.cell .bool) ∧
      runStateful additional ⟨.ret (.bool true), [.newCellApply .bool], []⟩ =
        cellProgram.runStateful (2 + additional) :=
  well_typed_runStateful_resume_has_type
    (initial_state_has_type (Program.check_full_sound cellProgram_checked).bodyHasType)
    (spent := 2) rfl additional

def testCheckedCoreProgram : IO Unit := do
  match CheckedCoreProgram.ofProgram? cellProgram with
  | none =>
      throw (IO.userError "a checker-accepted program was rejected")
  | some code =>
      assertTrue (code.program == cellProgram)
        "admission must retain the exact checked program"
      assertTrue
        (code.runStateful 3 == .done (.cellRef .bool 0) [.bool true])
        "checked execution must retain a cell result and its final local store"
      match code.runStateful 2 with
      | .outOfFuel _ => pure ()
      | result =>
          throw (IO.userError
            s!"insufficient fuel returned an unexpected result: {reprStr result}")
  match CheckedCoreProgram.ofProgram? rejectedProgram with
  | none => pure ()
  | some _ =>
      throw (IO.userError "an ill-typed program entered checked code")

end Tests
end

section
-- leanmerge: from Solcore.Test.CheckedHostCoreWordCodeSelectionProperties
/-! Compile-only consumers for branch-complete selected Word-code classification. -/

set_option autoImplicit false

namespace Solcore.Test.CheckedHostCoreWordCodeSelectionProperties

open ContractRuntime
open CheckedHostCoreWordCodeSelection

variable (checkedCode : CheckedHostCoreProgram)
variable (resultTypeEq : checkedCode.program.resultType = .word)
variable (resultTypeNe : checkedCode.program.resultType ≠ .word)
variable (wordCode : CheckedHostCoreWordProgram)
variable (selected : Option CheckedHostCoreProgram)
variable (selection left right : CheckedHostCoreWordCodeSelection)

example : classify none = .codeAbsent :=
  classify_none

example : classify (some checkedCode) =
    .word ⟨checkedCode, resultTypeEq⟩ :=
  classify_some_word checkedCode resultTypeEq

example : classify (some checkedCode) =
    .nonWord checkedCode resultTypeNe :=
  classify_some_nonWord checkedCode resultTypeNe

example : toCheckedCode? .codeAbsent = none :=
  toCheckedCode?_codeAbsent

example : toCheckedCode? (.nonWord checkedCode resultTypeNe) =
    some checkedCode :=
  toCheckedCode?_nonWord checkedCode resultTypeNe

example : toCheckedCode? (.word wordCode) = some wordCode.code :=
  toCheckedCode?_word wordCode

example : toWordCode? .codeAbsent = none :=
  toWordCode?_codeAbsent

example : toWordCode? (.nonWord checkedCode resultTypeNe) = none :=
  toWordCode?_nonWord checkedCode resultTypeNe

example : toWordCode? (.word wordCode) = some wordCode :=
  toWordCode?_word wordCode

example : toCheckedCode? (classify selected) = selected :=
  toCheckedCode?_classify selected

example : classify selection.toCheckedCode? = selection :=
  classify_toCheckedCode? selection

example (erased : left.toCheckedCode? = right.toCheckedCode?) :
    left = right :=
  toCheckedCode?_injective erased

example : toWordCode? (classify selected) =
    selected.bind CheckedHostCoreWordProgram.ofChecked? :=
  toWordCode?_classify selected

example : classify selected = .codeAbsent ↔ selected = none :=
  classify_eq_codeAbsent_iff selected

example : classify selected = .nonWord checkedCode resultTypeNe ↔
    selected = some checkedCode :=
  classify_eq_nonWord_iff selected checkedCode resultTypeNe

example : classify selected = .word wordCode ↔
    selected = some wordCode.code :=
  classify_eq_word_iff selected wordCode

example : CheckedHostCoreWordCodeSelection.codeAbsent ≠
    .nonWord checkedCode resultTypeNe :=
  codeAbsent_ne_nonWord checkedCode resultTypeNe

example : CheckedHostCoreWordCodeSelection.codeAbsent ≠ .word wordCode :=
  codeAbsent_ne_word wordCode

example : CheckedHostCoreWordCodeSelection.nonWord
      checkedCode resultTypeNe ≠ .word wordCode :=
  nonWord_ne_word checkedCode resultTypeNe wordCode

example : classify selected = .codeAbsent ∨
    (∃ code resultTypeNe,
      classify selected = .nonWord code resultTypeNe) ∨
    ∃ code, classify selected = .word code :=
  classify_exhaustive selected

variable (state : WorldState) (codeAddress : Address)

example : (state.selectWordCode codeAddress).toCheckedCode? =
    state.code? codeAddress :=
  WorldState.toCheckedCode?_selectWordCode state codeAddress

example : (state.selectWordCode codeAddress).toWordCode? =
    (state.code? codeAddress).bind
      CheckedHostCoreWordProgram.ofChecked? :=
  WorldState.toWordCode?_selectWordCode state codeAddress

example : state.selectWordCode codeAddress = .codeAbsent ↔
    state.code? codeAddress = none :=
  WorldState.selectWordCode_eq_codeAbsent_iff state codeAddress

example : state.selectWordCode codeAddress =
      .nonWord checkedCode resultTypeNe ↔
    state.code? codeAddress = some checkedCode :=
  WorldState.selectWordCode_eq_nonWord_iff
    state codeAddress checkedCode resultTypeNe

example : state.selectWordCode codeAddress = .word wordCode ↔
    state.code? codeAddress = some wordCode.code :=
  WorldState.selectWordCode_eq_word_iff state codeAddress wordCode

variable (account : Account)
variable (accountAbsent : state.account? codeAddress = none)
variable (accountPresent : state.account? codeAddress = some account)
variable (accountWithoutCode : account.code? = none)
variable (checkedCodePresent : account.code? = some checkedCode)
variable (wordCodePresent : account.code? = some wordCode.code)

example : state.selectWordCode codeAddress = .codeAbsent :=
  WorldState.selectWordCode_of_absent state codeAddress accountAbsent

example : state.selectWordCode codeAddress = .codeAbsent :=
  WorldState.selectWordCode_of_account_without_code
    state codeAddress account accountPresent accountWithoutCode

example : state.selectWordCode codeAddress =
    .nonWord checkedCode resultTypeNe :=
  WorldState.selectWordCode_of_present_nonWord
    state codeAddress account checkedCode resultTypeNe
      accountPresent checkedCodePresent

example : state.selectWordCode codeAddress = .word wordCode :=
  WorldState.selectWordCode_of_present_word
    state codeAddress account wordCode accountPresent wordCodePresent

example : (state.putAccount codeAddress account).selectWordCode codeAddress =
    classify account.code? :=
  WorldState.selectWordCode_putAccount_same state codeAddress account

variable (slot value : Core.Word)

example :
    (state.putAccount codeAddress
        (account.storageWrite slot value)).selectWordCode codeAddress =
      (state.putAccount codeAddress account).selectWordCode codeAddress :=
  WorldState.selectWordCode_putAccount_storageWrite_same
    state codeAddress account slot value

end Solcore.Test.CheckedHostCoreWordCodeSelectionProperties
end

section
-- leanmerge: from Solcore.Test.ParentIndexedSelectedCheckedWordExecutionContinuationProperties
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
end

section
-- leanmerge: from Solcore.Test.ParentIndexedSelectedCheckedWordExecutionProperties
/-! Compile-only consumers for ADR-0144 provenance and resumption laws. -/

set_option autoImplicit false

namespace Solcore.Test.ParentIndexedSelectedCheckedWordExecutionProperties

open ContractRuntime
open ContractRuntime.ParentIndexedSelectedCheckedWordExecution

universe u v

variable {RollbackState : Type u} {Event : Type v}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
variable (initialization : ParentIndexedFrameInitialization
  RollbackState Event parentWorking)
variable (storageAddress : Address)
variable (inputs : HostStorageDriver.ExecutionInputs)
variable (fuel additional first second : Nat)

abbrev Entry := ParentIndexedSelectedCheckedWordExecution
  initialization storageAddress inputs

variable (entry left right : Entry initialization storageAddress inputs)
variable (context : HostStorageDriver.Context
  RollbackState (FrameTrace Event))
variable (refined :
  initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress = some context)

example : start? initialization storageAddress inputs fuel = none ↔
    initialization.initialWorld.account? storageAddress = none :=
  start?_eq_none_iff initialization storageAddress inputs fuel

example : start? initialization storageAddress inputs fuel =
    some
      (ParentIndexedSelectedCheckedWordExecution.mk context refined
        (SelectedCheckedWordExecution.start context inputs fuel)) :=
  start?_of_present initialization storageAddress inputs fuel context refined

example :
    (start? initialization storageAddress inputs fuel).map toExecutionSigma =
      (initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress).map fun selected =>
          ⟨selected,
            SelectedCheckedWordExecution.start selected inputs fuel⟩ :=
  toExecutionSigma_start? initialization storageAddress inputs fuel

variable (initialContextEq : left.initialContext = right.initialContext)
variable (executionHeq : HEq left.execution right.execution)

example : left = right :=
  ext initialContextEq executionHeq

example : start? initialization storageAddress inputs fuel = some entry ↔
    entry.execution =
      SelectedCheckedWordExecution.start entry.initialContext inputs fuel :=
  start?_eq_some_iff initialization storageAddress inputs fuel entry

example : start? initialization storageAddress inputs
      entry.execution.providedFuel = some entry :=
  start?_canonical entry

example : entry.initialContext.context.values =
    initialization.toCheckpointedWorkingPair :=
  initialContext_values entry

example : entry.initialContext.context.storageAddress = storageAddress :=
  initialContext_storageAddress entry

example : entry.execution.selection =
    initialization.initialWorld.selectWordCode inputs.codeAddress :=
  selection_eq_initialWorld entry

example : entry.initialContext.context.values.checkpoint =
    FrameCheckpointSnapshot.fromWorkingPair parentWorking :=
  initialContext_checkpoint entry

example : entry.initialContext.context.values.working.2 =
    ⟨initialization.workingRollback, parentWorking.2.trace⟩ :=
  initialContext_workingEffects entry

example : entry.initialContext.context.values.working.2.rollback =
    initialization.workingRollback :=
  initialContext_workingRollback entry

example : entry.initialContext.context.values.working.2.trace =
    parentWorking.2.trace :=
  initialContext_parentTrace entry

example : (entry.resumeWithFuel additional).initialContext =
    entry.initialContext :=
  resumeWithFuel_initialContext entry additional

example : (entry.resumeWithFuel additional).execution =
    entry.execution.resumeWithFuel additional :=
  resumeWithFuel_execution entry additional

example : (entry.resumeWithFuel additional).execution.providedFuel =
    entry.execution.providedFuel + additional :=
  resumeWithFuel_providedFuel entry additional

example : (entry.resumeWithFuel additional).execution.selection =
    entry.execution.selection :=
  resumeWithFuel_selection entry additional

example : some (entry.resumeWithFuel additional) =
    start? initialization storageAddress inputs
      (entry.execution.providedFuel + additional) :=
  some_resumeWithFuel_eq_start? entry additional

example : (start? initialization storageAddress inputs fuel).map
      (fun selected => selected.resumeWithFuel additional) =
    start? initialization storageAddress inputs (fuel + additional) :=
  start?_map_resumeWithFuel initialization storageAddress inputs
    fuel additional

example : entry.resumeWithFuel 0 = entry :=
  resumeWithFuel_zero entry

example : (entry.resumeWithFuel first).resumeWithFuel second =
    entry.resumeWithFuel (first + second) :=
  resumeWithFuel_add entry first second

example : (entry.resumeWithFuel additional).execution.completion? =
    (SelectedCheckedWordExecution.start entry.initialContext inputs
      (entry.execution.providedFuel + additional)).completion? :=
  completion?_resumeWithFuel entry additional

variable (completion :
  WordReturnedFrameCompletion RollbackState (FrameTrace Event))
variable (completed : entry.execution.completion? = some completion)

example : (entry.resumeWithFuel additional).execution.completion? =
    some completion :=
  completion?_resumeWithFuel_of_some entry additional completion completed

example : entry.execution.execution? = none ↔
    entry.execution.selection = .codeAbsent ∨
      ∃ code resultTypeNe,
        entry.execution.selection = .nonWord code resultTypeNe :=
  execution?_eq_none_iff_branches entry

example : entry.execution.completion? = some completion ↔
    ∃ code,
      entry.execution.execution? =
        some (code, completion.toHostDriverResult) :=
  completion?_eq_some_iff entry completion

example : entry.execution.completion? = none ↔
    entry.execution.execution? = none ∨
      (∃ code finalContext exhausted,
        entry.execution.execution? =
          some (code, ⟨finalContext, .outOfFuel exhausted⟩)) ∨
      ∃ code finalContext suspension remainingFuel,
        entry.execution.execution? =
          some (code,
            ⟨finalContext, .unsupported suspension remainingFuel⟩) :=
  completion?_eq_none_iff entry

end Solcore.Test.ParentIndexedSelectedCheckedWordExecutionProperties
end

section
-- leanmerge: from Solcore.Test.ParentIndexedSelectedExecutionContinuation
/-! Compile-only consumers of parent-indexed selected execution continuation. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x

/-- All four partial boundaries remain distinguishable through the public laws. -/
private example
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
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking) :
    (initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome = none ↔
        initialization.initialWorld.account? storageAddress = none) ∧
      (initialization.runCodeWithStorageParentIndexedContinuationContext?
            storageAddress inputs fuel doneOutcome = some none ↔
        ∃ context,
          initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
              storageAddress = some context ∧
          context.context.values.working.1.code? inputs.codeAddress = none) ∧
      (initialization.runCodeWithStorageParentIndexedContinuationContext?
            storageAddress inputs fuel doneOutcome = some (some none) ↔
        (∃ context resultContext exhausted,
          initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
              storageAddress = some context ∧
          context.runCodeWithStorage? inputs fuel =
            some ⟨resultContext, .outOfFuel exhausted⟩) ∨
        ∃ context resultContext suspension remainingFuel,
          initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
              storageAddress = some context ∧
          context.runCodeWithStorage? inputs fuel =
            some ⟨resultContext,
              .unsupported suspension remainingFuel⟩) ∧
      (initialization.runCodeWithStorageParentIndexedContinuationContext?
            storageAddress inputs fuel doneOutcome =
          some (some (some parentContinuation)) ↔
        ∃ context continuation,
          initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
              storageAddress = some context ∧
          context.runCodeWithStorageContinuationContext?
              inputs fuel doneOutcome = some (some continuation) ∧
          parentContinuation =
            ParentIndexedFrameContinuationContext.fromTraceExtension
              parentWorking initialization.workingRollback
              initialization.initialTraceExtension continuation.result) := by
  exact
    ⟨initialization.runCodeWithStorageParentIndexedContinuationContext?_eq_none_iff
        storageAddress inputs fuel doneOutcome,
      initialization.runCodeWithStorageParentIndexedContinuationContext?_eq_some_none_iff
        storageAddress inputs fuel doneOutcome,
      initialization.runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_none_iff
        storageAddress inputs fuel doneOutcome,
      initialization.runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_some_iff
        storageAddress inputs fuel doneOutcome parentContinuation⟩

/-- Whole-context equality transports resolution and continuation unchanged. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)))
    (next :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Option Next)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          Bytes → Option Next) :
    ∃ context continuation,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some (some continuation) ∧
      parentContinuation.toFrameContinuationContext = continuation ∧
      parentContinuation.toFrameContinuationContext.resolve =
        continuation.resolve ∧
      parentContinuation.toFrameContinuationContext.continue? next =
        continuation.continue? next ∧
      parentContinuation.toFrameContinuationContext.resolve.continue?
          onReturned onReverted =
        continuation.resolve.continue? onReturned onReverted := by
  obtain ⟨context, continuation, refined, lowerCompleted, coherent⟩ :=
    initialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_toFrameContinuationContext
      storageAddress inputs fuel doneOutcome parentContinuation completed
  exact ⟨context, continuation, refined, lowerCompleted, coherent,
    congrArg FrameContinuationContext.resolve coherent,
    congrArg (fun current => current.continue? next) coherent,
    congrArg
      (fun current => current.resolve.continue? onReturned onReverted)
      coherent⟩

/-- A completed parent-indexed return uses the terminal working pair. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : parentContinuation.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    parentContinuation.resolve = FrameResolutionResult.returned
        parentContinuation.result.working parentContinuation.effectWorking data ∧
      FrameTrace.IsPrefixOf parentWorking.2.trace
        parentContinuation.effectWorking.trace := by
  exact parentContinuation.resolve_returned data outcomeEq

/-- A completed parent-indexed revert restores the indexed parent pair. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : parentContinuation.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    parentContinuation.resolve = FrameResolutionResult.reverted parentWorking.1
        ⟨parentWorking.2.rollback, parentContinuation.effectWorking.trace⟩ data ∧
      FrameTrace.IsPrefixOf parentWorking.2.trace
        parentContinuation.effectWorking.trace := by
  exact parentContinuation.resolve_reverted data outcomeEq

/-- A completed parent-indexed trap feeds both existing parent selectors. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq :
      parentContinuation.result.outcome = FrameOutcome.trapped reason) :
    parentContinuation.trapRollback? =
        some
          (parentWorking.1,
            ⟨parentWorking.2.rollback,
              parentContinuation.effectWorking.trace⟩) ∧
      parentContinuation.trapPropagationPayload? =
        some
          (⟨parentWorking.1, FrameOutcome.trapped reason⟩,
            ⟨parentWorking.2.rollback,
              parentContinuation.effectWorking.trace⟩) := by
  exact
    ⟨parentContinuation.trapRollback?_trapped reason outcomeEq,
      parentContinuation.trapPropagationPayload?_trapped reason outcomeEq⟩

/-- Additional fuel preserves the exact completed parent-indexed context. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking}
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)))
    (more : fuel ≤ largerFuel) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs largerFuel doneOutcome =
      some (some (some parentContinuation)) := by
  exact
    initialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
      storageAddress inputs doneOutcome completed more

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedSelectedExecutionFixture
/-! Shared measured fixture for branch-complete parent execution tests. -/

set_option autoImplicit false

namespace Tests.ParentIndexedSelectedExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime

def codeAddress : Address := ⟨0x10, by decide⟩
def storageAddress : Address := ⟨0x20, by decide⟩
def callerAddress : Address := ⟨0x40, by decide⟩

def targetSlot : Word := ⟨0x51, by decide⟩
def oldValue : Word := ⟨0x52, by decide⟩
def writtenValue : Word := ⟨0x53, by decide⟩

def inputData : HostStorageDriver.InputData := {
  bytes := [0x11, 0x22, 0x33].toByteArray
  size_lt_wordModulus := by decide
}

def executionInputs : HostStorageDriver.ExecutionInputs := {
  codeAddress := codeAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := inputData
  currentAddress := codeAddress
}

/-- Write working storage, then observe the immutable input size. -/
def program : Program := {
  resultType := .word
  body :=
    .letE
      (.apply
        (.var HostFunction.storageWrite.index)
        (.pair (.word targetSlot) (.word writtenValue)))
      (.apply (.var (HostFunction.inputDataSize.index + 1)) .unit)
}

theorem program_host_checked : program.checkHost = true := by
  decide

def code : CheckedHostCoreProgram := ⟨program, program_host_checked⟩

def storageAccount : Account :=
  Account.empty.storageWrite targetSlot oldValue

def checkpointWorld : WorldState :=
  WorldState.empty.putAccount storageAddress storageAccount

def workingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress (Account.empty.withCode code)
    |>.putAccount storageAddress storageAccount

def parentWorking :
    WorldState × FrameEffectJournal Nat (FrameTrace Nat) :=
  (checkpointWorld, ⟨101, FrameTrace.empty⟩)

def initialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := workingWorld
  workingRollback := 201
}

def missingStorageInitialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld :=
    WorldState.empty.putAccount codeAddress (Account.empty.withCode code)
  workingRollback := 201
}

def missingCodeInitialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := WorldState.empty.putAccount storageAddress storageAccount
  workingRollback := 201
}

inductive TrapReason where
  | policyTrap
  deriving Repr, BEq, DecidableEq

def returnData : Bytes := [0xa1, 0xb2].toByteArray
def revertData : Bytes := [0xc1, 0xd2].toByteArray

def returnedDoneOutcome
    (_ : HostStorageDriver.Context Nat (FrameTrace Nat))
    (_ : Value) (_ : Store) : FrameOutcome TrapReason :=
  .returned returnData

def revertedDoneOutcome
    (_ : HostStorageDriver.Context Nat (FrameTrace Nat))
    (_ : Value) (_ : Store) : FrameOutcome TrapReason :=
  .reverted revertData

def trappedDoneOutcome
    (_ : HostStorageDriver.Context Nat (FrameTrace Nat))
    (_ : Value) (_ : Store) : FrameOutcome TrapReason :=
  .trapped .policyTrap

abbrev Result := ParentIndexedSelectedExecutionResult
  Nat Nat TrapReason parentWorking

def runWith
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome TrapReason)
    (fuel : Nat) : Result :=
  initialization.runCodeWithStorageParentIndexedResult
    storageAddress executionInputs fuel doneOutcome

def storageValueAt?
    (state : WorldState) (address : Address) (slot : Word) : Option Word :=
  (state.account? address).bind fun account => account.storageValue? slot

def contextHasTarget
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (expected : Word) : Bool :=
  context.readStorage targetSlot == expected &&
    storageValueAt? context.context.values.working.1
      storageAddress targetSlot == some expected

def contextPreserved
    (context : HostStorageDriver.Context Nat (FrameTrace Nat)) : Bool :=
  storageValueAt? context.context.values.checkpoint.state
      storageAddress targetSlot == some oldValue &&
    context.context.values.checkpoint.effects.rollback == 101 &&
    context.context.values.checkpoint.effects.trace.toList == [] &&
    context.context.values.working.2.rollback == 201 &&
    context.context.values.working.2.trace.toList == []

def writeRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension =>
      suspension.request == .storageWrite targetSlot writtenValue
  | _ => false

def beforeInputSuffix (state : State) : Bool :=
  state.control == .ret .unit &&
    match state.continuation with
    | [.letBody body _] =>
        body == .apply
          (.var (HostFunction.inputDataSize.index + 1)) .unit
    | _ => false

def inputSizeRequestReady (state : State) : Bool :=
  match hostAdvance state with
  | .suspended suspension => suspension.request == .inputDataSize
  | _ => false

def exactCompletion (value : Value) (store : Store) : Bool :=
  value == .word inputData.sizeWord && store == []

def syntheticFault : MachineFault :=
  .invalidHostArgument .storageRead .unit

inductive FoldMarker where
  | returned
  | reverted
  | trapped
  | mismatch
  deriving Repr, BEq, DecidableEq

def foldValuesMatch
    (expectedRollback : Nat) (expectedValue : Word)
    (values :
      WorldState × FrameEffectJournal Nat (FrameTrace Nat)) : Bool :=
  storageValueAt? values.1 storageAddress targetSlot == some expectedValue &&
    values.2.rollback == expectedRollback &&
    values.2.trace.toList == []

def onReturned
    (values : WorldState × FrameEffectJournal Nat (FrameTrace Nat))
    (data : Bytes) : FoldMarker :=
  if foldValuesMatch 201 writtenValue values && data == returnData then
    .returned
  else .mismatch

def onReverted
    (values : WorldState × FrameEffectJournal Nat (FrameTrace Nat))
    (data : Bytes) : FoldMarker :=
  if foldValuesMatch 101 oldValue values && data == revertData then
    .reverted
  else .mismatch

def onTrapped
    (values : WorldState × FrameEffectJournal Nat (FrameTrace Nat))
    (reason : TrapReason) : FoldMarker :=
  if foldValuesMatch 101 oldValue values && reason == .policyTrap then
    .trapped
  else .mismatch

def foldResult
    (continuation : ParentIndexedFrameContinuationContext
      Nat Nat TrapReason parentWorking) : FoldMarker :=
  continuation.foldResolutionWithTrapRollback
    onReturned onReverted onTrapped

def writeRequestFuel : Nat := 9
def postWriteFuel : Nat := 10
def inputRequestFuel : Nat := 15
def completionFuel : Nat := 16

end Tests.ParentIndexedSelectedExecutionFixture
end

section
-- leanmerge: from Solcore.Test.CheckedHostCoreWordProgramExecutionFixture
/-! Shared direct-execution fixtures for checked Word return tests. -/

set_option autoImplicit false

namespace Tests.CheckedHostCoreWordProgramExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture

def wordCode : CheckedHostCoreWordProgram := ⟨code, rfl⟩

def context : HostStorageDriver.Context Nat (FrameTrace Nat) :=
  ⟨initialization.toCheckpointedWorkingPairWithStorageAddress storageAddress,
    storageAccount,
    by rfl⟩

def cellWord : Word := ⟨0x1234, by decide⟩

/-- Allocate one Core-local cell, then return an unrelated Word. -/
def cellProgram : Program := {
  resultType := .word
  body :=
    .letE (.newCell .bool (.bool true))
      (.word cellWord)
}

theorem cellProgram_host_checked : cellProgram.checkHost = true := by
  decide

def cellCode : CheckedHostCoreWordProgram :=
  ⟨⟨cellProgram, cellProgram_host_checked⟩, rfl⟩

def canonicalInputSizeReturnData : Bytes :=
  (List.replicate 31 (0 : UInt8) ++ [3]).toByteArray

end Tests.CheckedHostCoreWordProgramExecutionFixture
end

section
-- leanmerge: from Solcore.Test.ParentIndexedSelectedExecutionFold
/-! Runtime fold observations for branch-complete selected execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture

namespace ParentIndexedSelectedExecutionFold

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def failBranch (label phase : String) : IO Unit :=
  throw (IO.userError s!"{label}: expected completed {phase}")

/-- Check one completion policy before and after terminal resumption. -/
private def checkPolicy
    (label : String)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome TrapReason)
    (expected : FoldMarker) : IO Unit := do
  let completed := runWith doneOutcome completionFuel
  match completed with
  | .completed context value store continuation =>
      assertTrue (exactCompletion value store)
        s!"{label}: completion payload changed"
      assertTrue (contextHasTarget context writtenValue)
        s!"{label}: completed working storage did not keep the write"
      assertTrue (contextPreserved context)
        s!"{label}: completed checkpoint or effects changed"
      assertTrue (foldResult continuation == expected)
        s!"{label}: existing fold selected the wrong branch or payload"

      let resumed :=
        ParentIndexedSelectedExecutionResult.resumeWithFuel
          (.completed context value store continuation : Result)
          initialization executionInputs doneOutcome 100
      match resumedEq : resumed with
      | .completed resumedContext resumedValue resumedStore
          resumedContinuation =>
          have exactResume :
              resumed = (.completed context value store continuation :
                Result) := by
            exact ParentIndexedSelectedExecutionResult.resumeWithFuel_completed
              context value store continuation
              initialization executionInputs doneOutcome 100
          have payloadEq :
              (.completed resumedContext resumedValue resumedStore
                  resumedContinuation : Result) =
                .completed context value store continuation :=
            resumedEq.symm.trans exactResume
          have _samePayload :
              resumedContext = context ∧ resumedValue = value ∧
                resumedStore = store ∧
                  resumedContinuation = continuation := by
            cases payloadEq
            exact ⟨rfl, rfl, rfl, rfl⟩
          assertTrue (exactCompletion resumedValue resumedStore)
            s!"{label}: resumed completion payload changed"
          assertTrue (resumedValue == value && resumedStore == store)
            s!"{label}: terminal resumption changed value or local store"
          assertTrue
            (contextHasTarget resumedContext writtenValue)
            s!"{label}: resumed working storage changed"
          assertTrue (contextPreserved resumedContext)
            s!"{label}: resumed checkpoint or effects changed"
          assertTrue (foldResult resumedContinuation == expected)
            s!"{label}: terminal resumption changed the fold observation"
      | _ => failBranch label "resumption"
  | _ => failBranch label "execution"

/-- Return, revert, and trap policies retain exact fold observations. -/
def testParentIndexedSelectedExecutionFold : IO Unit := do
  checkPolicy "returned" returnedDoneOutcome .returned
  checkPolicy "reverted" revertedDoneOutcome .reverted
  checkPolicy "trapped" trappedDoneOutcome .trapped

end ParentIndexedSelectedExecutionFold

export ParentIndexedSelectedExecutionFold
  (testParentIndexedSelectedExecutionFold)

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedSelectedExecutionProperties
/-! Compile-only consumers for branch-complete selected execution laws. -/

set_option autoImplicit false

namespace Solcore.Test.ParentIndexedSelectedExecutionProperties

open ContractRuntime
open ContractRuntime.ParentIndexedSelectedExecutionResult

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
variable (suspension : Core.HostSuspension) (remainingFuel : Nat)
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
      .unsupported finalContext suspension remainingFuel ↔
    ∃ selected,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some selected ∧
      selected.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .unsupported suspension remainingFuel⟩ := by
  exact ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_unsupported_iff
      initialization storageAddress inputs fuel doneOutcome
      finalContext suspension remainingFuel

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
      (.unsupported context suspension remainingFuel : Result)
      initialization inputs doneOutcome additional =
    .unsupported context suspension (remainingFuel + additional) := by
  exact resumeWithFuel_unsupported context suspension remainingFuel
    initialization inputs doneOutcome additional

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
end

section
-- leanmerge: from Solcore.Test.ParentIndexedSelectedExecutionResumption
/-! Executable regressions for branch-complete parent resumption. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture

private def resume
    (result : Result) (additional : Nat) : Result :=
  result.resumeWithFuel
    initialization executionInputs returnedDoneOutcome additional

private theorem resume_fault_exact
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (state : State) :
    resume (.fault context syntheticFault state) 100 =
      .fault context syntheticFault state := by
  rfl

private theorem resume_completed_exact
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value) (store : Store)
    (continuation : ParentIndexedFrameContinuationContext
      Nat Nat TrapReason parentWorking) :
    resume (.completed context value store continuation) 100 =
      .completed context value store continuation := by
  rfl

private def firstResult : Result :=
  runWith returnedDoneOutcome writeRequestFuel

private def postWriteSplit : Result := resume firstResult 1
private def inputRequestSplit : Result := resume firstResult 6
private def completionSplit : Result := resume firstResult 7
private def sequentialSplit : Result := resume postWriteSplit 6
private def zeroSplit : Result := resume firstResult 0
private def completedResumed : Result := resume completionSplit 100

private def postWriteOneShot : Result :=
  runWith returnedDoneOutcome postWriteFuel

private def inputRequestOneShot : Result :=
  runWith returnedDoneOutcome inputRequestFuel

private def completionOneShot : Result :=
  runWith returnedDoneOutcome completionFuel

private def sameExhausted
    (left right : Result) (expectedValue : Word)
    (stateCheck : State → Bool) : Bool :=
  match left, right with
  | .outOfFuel leftContext leftState,
      .outOfFuel rightContext rightState =>
      contextHasTarget leftContext expectedValue &&
        contextHasTarget rightContext expectedValue &&
        contextPreserved leftContext && contextPreserved rightContext &&
        leftState == rightState && stateCheck leftState && stateCheck rightState
  | _, _ => false

private def sameCompletion (left right : Result) : Bool :=
  match left, right with
  | .completed leftContext leftValue leftStore leftContinuation,
      .completed rightContext rightValue rightStore rightContinuation =>
      contextHasTarget leftContext writtenValue &&
        contextHasTarget rightContext writtenValue &&
        contextPreserved leftContext && contextPreserved rightContext &&
        leftValue == rightValue && leftStore == rightStore &&
        exactCompletion leftValue leftStore &&
        exactCompletion rightValue rightStore &&
        foldResult leftContinuation == foldResult rightContinuation
  | _, _ => false

private def missingStorageResult : Result :=
  missingStorageInitialization.runCodeWithStorageParentIndexedResult
    storageAddress executionInputs completionFuel returnedDoneOutcome

private def missingCodeResult : Result :=
  missingCodeInitialization.runCodeWithStorageParentIndexedResult
    storageAddress executionInputs completionFuel returnedDoneOutcome

private def legacyIsStorageAbsent (result : Result) : Bool :=
  match result.toLegacy with
  | none => true
  | _ => false

private def legacyIsCodeAbsent (result : Result) : Bool :=
  match result.toLegacy with
  | some none => true
  | _ => false

private def exactInitialExhaustion (result : Result) : Bool :=
  match result with
  | .outOfFuel context state =>
      contextHasTarget context oldValue && contextPreserved context &&
        writeRequestReady state
  | _ => false

private def exactPostWriteExhaustion (result : Result) : Bool :=
  match result with
  | .outOfFuel context state =>
      contextHasTarget context writtenValue && contextPreserved context &&
        beforeInputSuffix state && !writeRequestReady state
  | _ => false

private def exactInputRequestExhaustion (result : Result) : Bool :=
  match result with
  | .outOfFuel context state =>
      contextHasTarget context writtenValue && contextPreserved context &&
        inputSizeRequestReady state
  | _ => false

private def exactReturnedCompletion (result : Result) : Bool :=
  match result with
  | .completed context value store continuation =>
      contextHasTarget context writtenValue && contextPreserved context &&
        exactCompletion value store && foldResult continuation == .returned
  | _ => false

private def syntheticFaultIdentity (context :
    HostStorageDriver.Context Nat (FrameTrace Nat)) (state : State) : Bool :=
  let faulted : Result := .fault context syntheticFault state
  match resume faulted 100 with
  | .fault resumedContext error resumedState =>
      error == syntheticFault && resumedState == state &&
        contextHasTarget resumedContext oldValue &&
        contextPreserved resumedContext
  | _ => false

def testParentIndexedSelectedExecutionResumption : IO Unit := do
  assertTrue program.checkHost
    "the host checker rejected the shared resumption fixture"

  match missingStorageResult, missingCodeResult with
  | .storageAbsent, .codeAbsent =>
      assertTrue
        (legacyIsStorageAbsent missingStorageResult &&
          legacyIsCodeAbsent missingCodeResult)
        "absence branches did not preserve their distinct legacy layers"
      match resume missingStorageResult 100, resume missingCodeResult 100 with
      | .storageAbsent, .codeAbsent => pure ()
      | _, _ =>
          throw (IO.userError "resumption changed an absence branch")
  | _, _ =>
      throw (IO.userError "storage and code absence were not distinct")

  assertTrue (exactInitialExhaustion firstResult)
    "fuel 9 did not retain the exact pre-write request and old context"

  assertTrue
    (exactPostWriteExhaustion postWriteSplit &&
      sameExhausted postWriteSplit postWriteOneShot
        writtenValue beforeInputSuffix)
    "9+1 did not match fuel 10 after handling the write exactly once"

  assertTrue
    (exactInputRequestExhaustion inputRequestSplit &&
      sameExhausted inputRequestSplit inputRequestOneShot
        writtenValue inputSizeRequestReady)
    "9+6 did not match fuel 15 at the retained input-size request"

  assertTrue
    (exactReturnedCompletion completionSplit &&
      sameCompletion completionSplit completionOneShot)
    "9+7 did not match the observable one-shot fuel-16 completion"

  match firstResult with
  | .outOfFuel context state =>
      assertTrue (syntheticFaultIdentity context state)
        "a synthetic raw fault was not an exact terminal identity"
  | _ =>
      throw (IO.userError "the fault identity fixture was not exhausted")

  assertTrue
    (sameExhausted zeroSplit firstResult oldValue writeRequestReady)
    "zero additional fuel changed an actual run result"

  assertTrue
    (exactReturnedCompletion sequentialSplit &&
      sameCompletion sequentialSplit completionSplit)
    "sequential additions +1 then +6 differed from the summed +7"

  assertTrue
    (exactReturnedCompletion completedResumed &&
      sameCompletion completedResumed completionSplit)
    "resuming an actual completed carrier changed its terminal observations"

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedSelectedExecutionSession
/-! Executable regressions for proof-refined selected execution sessions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture

namespace ParentIndexedSelectedExecutionSessionTest

private abbrev Session := ParentIndexedSelectedExecutionSession
  Nat Nat TrapReason parentWorking

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def startWith
    (selectedInitialization :
      ParentIndexedFrameInitialization Nat Nat parentWorking)
    (doneOutcome : HostStorageDriver.Context Nat (FrameTrace Nat) →
      Value → Store → FrameOutcome TrapReason)
    (fuel : Nat) : Session :=
  ParentIndexedSelectedExecutionSession.start selectedInitialization
    storageAddress executionInputs doneOutcome fuel

private def startReturned (fuel : Nat) : Session :=
  startWith initialization returnedDoneOutcome fuel

private theorem wholeSessionZero :
    (startReturned writeRequestFuel).resumeWithFuel 0 =
      startReturned writeRequestFuel := by
  exact ParentIndexedSelectedExecutionSession.resumeWithFuel_zero _

private theorem postWriteWholeExact :
    (startReturned writeRequestFuel).resumeWithFuel 1 =
      startReturned postWriteFuel := by
  simpa [startReturned, startWith, writeRequestFuel, postWriteFuel] using
    (ParentIndexedSelectedExecutionSession.start_resumeWithFuel
      initialization storageAddress executionInputs returnedDoneOutcome 9 1)

private theorem inputRequestWholeExact :
    ((startReturned writeRequestFuel).resumeWithFuel 1).resumeWithFuel 5 =
      startReturned inputRequestFuel := by
  rw [ParentIndexedSelectedExecutionSession.resumeWithFuel_add]
  simpa [startReturned, startWith, writeRequestFuel, inputRequestFuel] using
    (ParentIndexedSelectedExecutionSession.start_resumeWithFuel
      initialization storageAddress executionInputs returnedDoneOutcome 9 6)

private theorem directCompletionWholeExact :
    (startReturned writeRequestFuel).resumeWithFuel 7 =
      startReturned completionFuel := by
  simpa [startReturned, startWith, writeRequestFuel, completionFuel] using
    (ParentIndexedSelectedExecutionSession.start_resumeWithFuel
      initialization storageAddress executionInputs returnedDoneOutcome 9 7)

private theorem sequentialCompletionWholeExact :
    ((startReturned writeRequestFuel).resumeWithFuel 1).resumeWithFuel 6 =
      startReturned completionFuel := by
  rw [ParentIndexedSelectedExecutionSession.resumeWithFuel_add]
  exact directCompletionWholeExact

private theorem completedResultIdentity
    (session : Session)
    (context : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value) (store : Store)
    (continuation : ParentIndexedFrameContinuationContext
      Nat Nat TrapReason parentWorking)
    (completed :
      session.result = .completed context value store continuation)
    (additional : Nat) :
    (session.resumeWithFuel additional).result = session.result := by
  rw [ParentIndexedSelectedExecutionSession.resumeWithFuel_result, completed]
  rfl

private def exactExhaustion
    (session : Session) (expected : Word)
    (stateCheck : State → Bool) : Bool :=
  match session.result with
  | .outOfFuel context state =>
      contextHasTarget context expected && contextPreserved context &&
        stateCheck state
  | _ => false

private def postWriteWithoutReplay (state : State) : Bool :=
  beforeInputSuffix state && !writeRequestReady state

private def sameExhaustion
    (left right : Session) (expected : Word)
    (stateCheck : State → Bool) : Bool :=
  match left.result, right.result with
  | .outOfFuel leftContext leftState,
      .outOfFuel rightContext rightState =>
      contextHasTarget leftContext expected &&
        contextHasTarget rightContext expected &&
        contextPreserved leftContext && contextPreserved rightContext &&
        leftState == rightState && stateCheck leftState && stateCheck rightState
  | _, _ => false

private def exactCompletion
    (session : Session) (expected : FoldMarker) : Bool :=
  match session.result with
  | .completed context value store continuation =>
      contextHasTarget context writtenValue && contextPreserved context &&
        ParentIndexedSelectedExecutionFixture.exactCompletion value store &&
        foldResult continuation == expected
  | _ => false

private def sameCompletion
    (left right : Session) (expected : FoldMarker) : Bool :=
  match left.result, right.result with
  | .completed leftContext leftValue leftStore leftContinuation,
      .completed rightContext rightValue rightStore rightContinuation =>
      contextHasTarget leftContext writtenValue &&
        contextHasTarget rightContext writtenValue &&
        contextPreserved leftContext && contextPreserved rightContext &&
        leftValue == rightValue && leftStore == rightStore &&
        ParentIndexedSelectedExecutionFixture.exactCompletion
          leftValue leftStore &&
        ParentIndexedSelectedExecutionFixture.exactCompletion
          rightValue rightStore &&
        foldResult leftContinuation == expected &&
        foldResult rightContinuation == expected
  | _, _ => false

private def resultIsStorageAbsent (session : Session) : Bool :=
  match session.result with
  | .storageAbsent => true
  | _ => false

private def resultIsCodeAbsent (session : Session) : Bool :=
  match session.result with
  | .codeAbsent => true
  | _ => false

def testParentIndexedSelectedExecutionSession : IO Unit := do
  assertTrue program.checkHost
    "the host checker rejected the selected-session fixture"

  let missingStorage :=
    startWith missingStorageInitialization returnedDoneOutcome completionFuel
  let missingCode :=
    startWith missingCodeInitialization returnedDoneOutcome completionFuel
  assertTrue
    (resultIsStorageAbsent missingStorage && resultIsCodeAbsent missingCode)
    "session start did not preserve distinct storage/code absence branches"

  let initial := startReturned writeRequestFuel
  assertTrue
    (initial.providedFuel == 9 &&
      exactExhaustion initial oldValue writeRequestReady)
    "fuel 9 did not retain the exact pre-write request and old context"

  let zero := initial.resumeWithFuel 0
  have _zeroExact : zero = initial := wholeSessionZero
  assertTrue
    (zero.providedFuel == 9 &&
      sameExhaustion zero initial oldValue writeRequestReady)
    "zero fuel changed the whole selected execution session"

  let postWrite := initial.resumeWithFuel 1
  let postWriteOneShot := startReturned postWriteFuel
  have _postWriteExact : postWrite = postWriteOneShot := postWriteWholeExact
  assertTrue
    (postWrite.providedFuel == 10 &&
      exactExhaustion postWrite writtenValue postWriteWithoutReplay &&
      sameExhaustion postWrite postWriteOneShot
        writtenValue postWriteWithoutReplay)
    "9+1 did not match one-shot 10 after exactly one storage write"

  let inputRequest := postWrite.resumeWithFuel 5
  let inputRequestOneShot := startReturned inputRequestFuel
  have _inputExact : inputRequest = inputRequestOneShot :=
    inputRequestWholeExact
  assertTrue
    (inputRequest.providedFuel == 15 &&
      exactExhaustion inputRequest writtenValue inputSizeRequestReady &&
      sameExhaustion inputRequest inputRequestOneShot
        writtenValue inputSizeRequestReady)
    "9+1+5 did not match one-shot 15 at the input-size request"

  let directCompletion := initial.resumeWithFuel 7
  let sequentialCompletion := postWrite.resumeWithFuel 6
  let completionOneShot := startReturned completionFuel
  have _directExact : directCompletion = completionOneShot :=
    directCompletionWholeExact
  have _sequentialExact : sequentialCompletion = completionOneShot :=
    sequentialCompletionWholeExact
  assertTrue
    (directCompletion.providedFuel == 16 &&
      sequentialCompletion.providedFuel == 16 &&
      exactCompletion completionOneShot .returned &&
      sameCompletion directCompletion completionOneShot .returned &&
      sameCompletion sequentialCompletion completionOneShot .returned)
    "direct 9+7 or sequential 9+1+6 differed from one-shot 16"

  match completedEq : completionOneShot.result with
  | .completed context value store continuation =>
      let terminal := completionOneShot.resumeWithFuel 100
      have _resultExact : terminal.result = completionOneShot.result :=
        completedResultIdentity completionOneShot context value store
          continuation completedEq 100
      assertTrue
        (terminal.providedFuel == 116 &&
          sameCompletion terminal completionOneShot .returned)
        "terminal resumption changed the result or failed to advance its budget"
  | _ =>
      throw (IO.userError "one-shot fuel 16 did not complete")

end ParentIndexedSelectedExecutionSessionTest

export ParentIndexedSelectedExecutionSessionTest
  (testParentIndexedSelectedExecutionSession)

end Tests
end

section
-- leanmerge: from Solcore.Test.ParentIndexedSelectedExecutionSessionProperties
/-! Compile-only consumers for certified selected-session proof contracts. -/

set_option autoImplicit false

namespace Solcore.Test.ParentIndexedSelectedExecutionSessionProperties

open ContractRuntime
open ContractRuntime.ParentIndexedSelectedExecutionResult

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
end

section
-- leanmerge: from Solcore.Test.SelectedCheckedWordExecutionFixture
/-! Shared absent, non-Word, and measured Word selected-execution fixtures. -/

set_option autoImplicit false

namespace Tests.SelectedCheckedWordExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture
open CheckedHostCoreWordProgramExecutionFixture

def absentContext : HostStorageDriver.Context Nat (FrameTrace Nat) :=
  ⟨missingCodeInitialization
      |>.toCheckpointedWorkingPairWithStorageAddress storageAddress,
    storageAccount,
    by rfl⟩

def boolProgram : Program := {
  resultType := .bool
  body := .bool true
}

theorem boolProgram_host_checked : boolProgram.checkHost = true := by
  decide

def boolCode : CheckedHostCoreProgram :=
  ⟨boolProgram, boolProgram_host_checked⟩

def nonWordWorkingWorld : WorldState :=
  WorldState.empty
    |>.putAccount codeAddress (Account.empty.withCode boolCode)
    |>.putAccount storageAddress storageAccount

def nonWordInitialization :
    ParentIndexedFrameInitialization Nat Nat parentWorking := {
  initialWorld := nonWordWorkingWorld
  workingRollback := 201
}

def nonWordContext : HostStorageDriver.Context Nat (FrameTrace Nat) :=
  ⟨nonWordInitialization
      |>.toCheckpointedWorkingPairWithStorageAddress storageAddress,
    storageAccount,
    by rfl⟩

abbrev Execution (initialContext :
    HostStorageDriver.Context Nat (FrameTrace Nat)) :=
  SelectedCheckedWordExecution initialContext executionInputs

def absentExecution (fuel : Nat) : Execution absentContext :=
  SelectedCheckedWordExecution.start absentContext executionInputs fuel

def nonWordExecution (fuel : Nat) : Execution nonWordContext :=
  SelectedCheckedWordExecution.start nonWordContext executionInputs fuel

def wordExecution (fuel : Nat) : Execution context :=
  SelectedCheckedWordExecution.start context executionInputs fuel

end Tests.SelectedCheckedWordExecutionFixture
end

section
-- leanmerge: from Solcore.Test.ParentIndexedSelectedCheckedWordExecutionFixture
/-! Shared parent-indexed selected checked Word fixtures for ADR-0144. -/

set_option autoImplicit false

namespace Tests.ParentIndexedSelectedCheckedWordExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture
open SelectedCheckedWordExecutionFixture

def missingStorageExecution? (fuel : Nat) :=
  ParentIndexedSelectedCheckedWordExecution.start?
    missingStorageInitialization storageAddress executionInputs fuel

def codeAbsentExecution? (fuel : Nat) :=
  ParentIndexedSelectedCheckedWordExecution.start?
    missingCodeInitialization storageAddress executionInputs fuel

def nonWordExecution? (fuel : Nat) :=
  ParentIndexedSelectedCheckedWordExecution.start?
    nonWordInitialization storageAddress executionInputs fuel

def wordExecution? (fuel : Nat) :=
  ParentIndexedSelectedCheckedWordExecution.start?
    initialization storageAddress executionInputs fuel

/-- Canonical legacy policy used only for the conditional coherence branch. -/
def canonicalWordDoneOutcome
    (_ : HostStorageDriver.Context Nat (FrameTrace Nat))
    (value : Value) (_ : Store) : FrameOutcome TrapReason :=
  match value with
  | .word word => .returned (encodeWordBytesBE word)
  | _ => .trapped .policyTrap

end Tests.ParentIndexedSelectedCheckedWordExecutionFixture
end

section
-- leanmerge: from Solcore.Test.ParentIndexedSelectedCheckedWordExecution
/-! Executable provenance, fuel, and parent-return regressions for ADR-0144. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture
open CheckedHostCoreWordProgramExecutionFixture
open SelectedCheckedWordExecutionFixture
open ParentIndexedSelectedCheckedWordExecutionFixture

private def codeAbsentPresent (fuel : Nat) : Bool :=
  match codeAbsentExecution? fuel with
  | some entry =>
      entry.execution.execution?.isNone &&
        entry.execution.completion?.isNone &&
        (entry.returnedCompletion? (TrapReason := TrapReason)).isNone &&
        match entry.execution.selection with
        | .codeAbsent => true
        | _ => false
  | none => false

private def nonWordPresent (fuel : Nat) : Bool :=
  match nonWordExecution? fuel with
  | some entry =>
      entry.execution.execution?.isNone &&
        entry.execution.completion?.isNone &&
        (entry.returnedCompletion? (TrapReason := TrapReason)).isNone &&
        match entry.execution.selection with
        | .nonWord selected _ => selected.program == boolProgram
        | _ => false
  | none => false

private def exactExhaustionAt
    (fuel : Nat) (expectedStorage : Word)
    (stateMatches : State → Bool) : Bool :=
  match wordExecution? fuel with
  | some entry =>
      entry.execution.completion?.isNone &&
        (entry.returnedCompletion? (TrapReason := TrapReason)).isNone &&
        match entry.execution.selection, entry.execution.execution? with
        | .word selected,
            some (retained, ⟨finalContext, .outOfFuel exhausted⟩) =>
            selected.code.program == program &&
              retained.code.program == program &&
              contextHasTarget finalContext expectedStorage &&
              contextPreserved finalContext && stateMatches exhausted
        | _, _ => false
  | none => false

private def exactReturnedPair (fuel : Nat) : Bool :=
  match wordExecution? fuel with
  | none => false
  | some entry =>
      match entry.returnedCompletion? (TrapReason := TrapReason) with
      | none => false
      | some (completion, continuation) =>
          completion.word == inputData.sizeWord && completion.store == [] &&
            completion.returnData == canonicalInputSizeReturnData &&
            completion.returnData.size == 32 &&
            decodeWordBytesBE? completion.returnData == some inputData.sizeWord &&
            contextHasTarget completion.context writtenValue &&
            contextPreserved completion.context &&
            storageValueAt? continuation.stateCheckpoint
                storageAddress targetSlot == some oldValue &&
            continuation.effectCheckpoint.rollback == 101 &&
            continuation.effectCheckpoint.trace.toList == [] &&
            continuation.effectWorking.rollback == 201 &&
            continuation.effectWorking.trace.toList == [] &&
            match continuation.resolve with
            | .returned state effects data =>
                storageValueAt? state storageAddress targetSlot ==
                    some writtenValue &&
                  effects.rollback == 201 && effects.trace.toList == [] &&
                  data == canonicalInputSizeReturnData
            | _ => false

private def sameReturnedPair
    (left right : Option
      (WordReturnedFrameCompletion Nat (FrameTrace Nat) ×
        ParentIndexedFrameContinuationContext
          Nat Nat TrapReason parentWorking)) : Bool :=
  match left, right with
  | some (leftCompletion, leftContinuation),
      some (rightCompletion, rightContinuation) =>
      leftCompletion.word == rightCompletion.word &&
        leftCompletion.store == rightCompletion.store &&
        leftCompletion.returnData == rightCompletion.returnData &&
        contextHasTarget leftCompletion.context writtenValue &&
        contextHasTarget rightCompletion.context writtenValue &&
        leftContinuation.effectCheckpoint.rollback ==
          rightContinuation.effectCheckpoint.rollback &&
        leftContinuation.effectWorking.rollback ==
          rightContinuation.effectWorking.rollback
  | _, _ => false

private def splitPair? (fuel additional : Nat) :=
  (wordExecution? fuel).bind fun entry =>
    (entry.resumeWithFuel additional).returnedCompletion?
      (TrapReason := TrapReason)

private def legacyCanonicalCompletion : Bool :=
  match wordExecution? completionFuel with
  | none => false
  | some entry =>
      match entry.returnedCompletion? (TrapReason := TrapReason) with
      | none => false
      | some (completion, continuation) =>
          match initialization.runCodeWithStorageParentIndexedResult
              storageAddress executionInputs completionFuel
              canonicalWordDoneOutcome with
          | .completed finalContext (.word word) store legacyContinuation =>
              word == completion.word && store == completion.store &&
                finalContext.readStorage targetSlot ==
                  completion.context.readStorage targetSlot &&
                legacyContinuation.effectCheckpoint.rollback ==
                  continuation.effectCheckpoint.rollback &&
                legacyContinuation.effectWorking.rollback ==
                  continuation.effectWorking.rollback &&
                match legacyContinuation.resolve, continuation.resolve with
                | .returned leftState _ leftData,
                    .returned rightState _ rightData =>
                    storageValueAt? leftState storageAddress targetSlot ==
                        storageValueAt? rightState storageAddress targetSlot &&
                      leftData == rightData
                | _, _ => false
          | _ => false

def testParentIndexedSelectedCheckedWordExecution : IO Unit := do
  assertTrue
    ((missingStorageExecution? 0).isNone &&
      (missingStorageExecution? 64).isNone &&
      ((missingStorageExecution? 0).map
        (fun entry => entry.resumeWithFuel 64)).isNone)
    "storage absence did not remain the unique outer none branch"

  assertTrue
    (codeAbsentPresent 0 && codeAbsentPresent 64 &&
      nonWordPresent 0 && nonWordPresent 64)
    "a present non-executing code branch was flattened or executed"

  assertTrue
    (exactExhaustionAt writeRequestFuel oldValue writeRequestReady &&
      exactExhaustionAt postWriteFuel writtenValue beforeInputSuffix &&
      exactExhaustionAt inputRequestFuel writtenValue inputSizeRequestReady)
    "a measured parent Word exhaustion boundary lost its retained state"

  assertTrue (exactReturnedPair completionFuel)
    "fuel 16 did not produce the exact canonical returned parent pair"

  let completed := (wordExecution? completionFuel).bind fun entry =>
    entry.returnedCompletion? (TrapReason := TrapReason)
  assertTrue
    (sameReturnedPair (splitPair? writeRequestFuel 7) completed &&
      sameReturnedPair (splitPair? postWriteFuel 6) completed &&
      sameReturnedPair (splitPair? inputRequestFuel 1) completed &&
      sameReturnedPair (splitPair? completionFuel 48) completed &&
      sameReturnedPair (splitPair? completionFuel 0) completed &&
      sameReturnedPair (splitPair? writeRequestFuel (3 + 4))
        ((wordExecution? writeRequestFuel).bind fun entry =>
          ((entry.resumeWithFuel 3).resumeWithFuel 4).returnedCompletion?
            (TrapReason := TrapReason)))
    "split, zero, addition, or terminal parent resumption changed completion"

  assertTrue legacyCanonicalCompletion
    "conditional generic parent coherence lost canonical Word completion"

end Tests
end

section
-- leanmerge: from Solcore.Test.SelectedCheckedWordExecution
/-! Executable branch, fuel, and returned-frame regressions for ADR-0143. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture
open CheckedHostCoreWordProgramExecutionFixture
open SelectedCheckedWordExecutionFixture

private def absentRunDoesNotRun
    (execution : Execution absentContext) (expectedFuel : Nat) : Bool :=
  execution.providedFuel == expectedFuel &&
    execution.execution?.isNone && execution.completion?.isNone &&
    match execution.selection with
    | .codeAbsent => true
    | _ => false

private def nonWordRunDoesNotRun
    (execution : Execution nonWordContext) (expectedFuel : Nat) : Bool :=
  execution.providedFuel == expectedFuel &&
    execution.execution?.isNone && execution.completion?.isNone &&
    match execution.selection with
    | .nonWord selected _ => selected.program == boolProgram
    | _ => false

private def exactExhaustionAt_variant
    (fuel : Nat) (expectedStorage : Word)
    (stateMatches : State → Bool) : Bool :=
  let execution := wordExecution fuel
  execution.completion?.isNone &&
    match execution.selection, execution.execution? with
    | .word selected,
        some (retained, ⟨finalContext, .outOfFuel exhausted⟩) =>
        selected.code.program == program &&
          retained.code.program == program &&
          contextHasTarget finalContext expectedStorage &&
          contextPreserved finalContext && stateMatches exhausted
    | _, _ => false

private def exactReturnedResolution
    (completion : WordReturnedFrameCompletion Nat (FrameTrace Nat)) : Bool :=
  let frame : FrameContinuationContext Nat (FrameTrace Nat) TrapReason :=
    completion.toFrameContinuationContext
  completion.word == inputData.sizeWord &&
    completion.store == [] &&
    completion.returnData == canonicalInputSizeReturnData &&
    completion.returnData.size == 32 &&
    decodeWordBytesBE? completion.returnData == some inputData.sizeWord &&
    contextHasTarget completion.context writtenValue &&
    contextPreserved completion.context &&
    match frame.resolve with
    | .returned state effects data =>
        storageValueAt? state storageAddress targetSlot == some writtenValue &&
          effects.rollback == 201 && effects.trace.toList == [] &&
          data == completion.returnData
    | _ => false

private def exactCompletionAt (fuel : Nat) : Bool :=
  let execution := wordExecution fuel
  match execution.selection, execution.execution?, execution.completion? with
  | .word selected,
      some (retained, ⟨finalContext, .done (.word result) store⟩),
      some completion =>
      selected.code.program == program && retained.code.program == program &&
        result == inputData.sizeWord && store == [] &&
        completion.context.readStorage targetSlot == finalContext.readStorage targetSlot &&
        exactReturnedResolution completion
  | _, _, _ => false

private def sameCompletion_variant
    (left right : Option
      (WordReturnedFrameCompletion Nat (FrameTrace Nat))) : Bool :=
  match left, right with
  | some left, some right =>
      left.word == right.word && left.store == right.store &&
        left.returnData == right.returnData &&
        contextHasTarget left.context writtenValue &&
        contextHasTarget right.context writtenValue &&
        contextPreserved left.context && contextPreserved right.context
  | _, _ => false

private theorem split_9_7_exact :
    (wordExecution writeRequestFuel).resumeWithFuel 7 =
      wordExecution completionFuel := by
  simpa [wordExecution, writeRequestFuel, completionFuel] using
    SelectedCheckedWordExecution.start_resumeWithFuel
      context executionInputs writeRequestFuel 7

private theorem split_10_6_exact :
    (wordExecution postWriteFuel).resumeWithFuel 6 =
      wordExecution completionFuel := by
  simpa [wordExecution, postWriteFuel, completionFuel] using
    SelectedCheckedWordExecution.start_resumeWithFuel
      context executionInputs postWriteFuel 6

private theorem split_15_1_exact :
    (wordExecution inputRequestFuel).resumeWithFuel 1 =
      wordExecution completionFuel := by
  simpa [wordExecution, inputRequestFuel, completionFuel] using
    SelectedCheckedWordExecution.start_resumeWithFuel
      context executionInputs inputRequestFuel 1

def testSelectedCheckedWordExecution : IO Unit := do
  assertTrue
    (absentRunDoesNotRun (absentExecution 0) 0 &&
      absentRunDoesNotRun ((absentExecution 0).resumeWithFuel 0) 0 &&
      absentRunDoesNotRun (absentExecution 64) 64 &&
      absentRunDoesNotRun
        ((absentExecution 0).resumeWithFuel 64) 64)
    "codeAbsent selection unexpectedly executed"

  assertTrue
    (nonWordRunDoesNotRun (nonWordExecution 0) 0 &&
      nonWordRunDoesNotRun ((nonWordExecution 0).resumeWithFuel 0) 0 &&
      nonWordRunDoesNotRun (nonWordExecution 64) 64 &&
      nonWordRunDoesNotRun
        ((nonWordExecution 0).resumeWithFuel 64) 64)
    "nonWord selection unexpectedly executed or lost its checked code"

  assertTrue
    (exactExhaustionAt_variant writeRequestFuel oldValue writeRequestReady &&
      exactExhaustionAt_variant postWriteFuel writtenValue beforeInputSuffix &&
      exactExhaustionAt_variant inputRequestFuel writtenValue inputSizeRequestReady)
    "a measured Word exhaustion boundary lost its exact retained run"

  assertTrue (exactCompletionAt completionFuel)
    "fuel 16 did not retain the exact canonical selected Word completion"

  let completion := (wordExecution completionFuel).completion?
  let split9 :=
    ((wordExecution writeRequestFuel).resumeWithFuel 7).completion?
  let split10 :=
    ((wordExecution postWriteFuel).resumeWithFuel 6).completion?
  let split15 :=
    ((wordExecution inputRequestFuel).resumeWithFuel 1).completion?
  let terminal :=
    ((wordExecution completionFuel).resumeWithFuel 48).completion?
  let zero :=
    ((wordExecution completionFuel).resumeWithFuel 0).completion?
  let added :=
    (((wordExecution writeRequestFuel).resumeWithFuel 3)
      |>.resumeWithFuel 4).completion?
  let combined :=
    ((wordExecution writeRequestFuel).resumeWithFuel (3 + 4)).completion?
  assertTrue
    (sameCompletion_variant split9 completion &&
      sameCompletion_variant split10 completion &&
      sameCompletion_variant split15 completion &&
      sameCompletion_variant terminal completion &&
      sameCompletion_variant zero completion &&
      sameCompletion_variant added combined && sameCompletion_variant combined completion &&
      ((wordExecution completionFuel).resumeWithFuel 48).providedFuel == 64)
    "split, summed, or terminal resumption changed the selected completion"

  have _ := split_9_7_exact
  have _ := split_10_6_exact
  have _ := split_15_1_exact
  pure ()

end Tests
end

section
-- leanmerge: from Solcore.Test.CheckedHostCoreWordProgramExecution
/-! Executable regressions for checked Word completion and canonical returns. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open ParentIndexedSelectedExecutionFixture
open CheckedHostCoreWordProgramExecutionFixture

private def boolProgram : Program := {
  resultType := .bool
  body := .bool true
}

private theorem boolProgram_host_checked : boolProgram.checkHost = true := by
  decide

private def boolCode : CheckedHostCoreProgram :=
  ⟨boolProgram, boolProgram_host_checked⟩

private def rejectedWordProgram : Program := {
  resultType := .word
  body := .bool true
}

private def initialResult :=
  wordCode.runWithStorage context executionInputs writeRequestFuel

private def completionAt (fuel : Nat) :=
  wordCode.runWithStorageReturnedFrameCompletion?
    context executionInputs fuel

private def postWriteResult :=
  wordCode.runWithStorage context executionInputs postWriteFuel

private def resumedCompletion :=
  ((wordCode.runWithStorage context executionInputs writeRequestFuel)
    |>.resumeWithFuel
      (@HostStorageDriver.handler Nat (FrameTrace Nat) executionInputs) 7)
    |>.toWordReturnedFrameCompletion?

private def postWriteResumedCompletion :=
  (postWriteResult.resumeWithFuel
      (@HostStorageDriver.handler Nat (FrameTrace Nat) executionInputs) 6)
    |>.toWordReturnedFrameCompletion?

private theorem resumedCompletion_exact :
    resumedCompletion = completionAt completionFuel := by
  simpa [resumedCompletion, completionAt, writeRequestFuel,
    completionFuel] using
    wordCode.toWordReturnedFrameCompletion?_resumeWithFuel_runWithStorage
      context executionInputs writeRequestFuel 7

private theorem postWriteResumedCompletion_exact :
    postWriteResumedCompletion = completionAt completionFuel := by
  simpa [postWriteResumedCompletion, postWriteResult, completionAt,
    postWriteFuel, completionFuel] using
    wordCode.toWordReturnedFrameCompletion?_resumeWithFuel_runWithStorage
      context executionInputs postWriteFuel 6

private def exactReturnedResolution_variant
    (completion : WordReturnedFrameCompletion Nat (FrameTrace Nat))
    (expectedStorage expectedWord : Word)
    (expectedStore : Store) : Bool :=
  let frame : FrameContinuationContext Nat (FrameTrace Nat)
      ParentIndexedSelectedExecutionFixture.TrapReason :=
    completion.toFrameContinuationContext
  completion.word == expectedWord &&
    completion.store == expectedStore &&
    completion.returnData.size == 32 &&
    decodeWordBytesBE? completion.returnData == some expectedWord &&
    contextHasTarget completion.context expectedStorage &&
    contextPreserved completion.context &&
    match frame.resolve with
    | .returned state effects data =>
        storageValueAt? state storageAddress targetSlot ==
            some expectedStorage &&
          effects.rollback == 201 && effects.trace.toList == [] &&
          data == completion.returnData
    | _ => false

private def sameCompletionObservations
    (left right : Option
      (WordReturnedFrameCompletion Nat (FrameTrace Nat))) : Bool :=
  match left, right with
  | some left, some right =>
      left.word == right.word && left.store == right.store &&
        left.returnData == right.returnData &&
        contextHasTarget left.context writtenValue &&
        contextHasTarget right.context writtenValue &&
        contextPreserved left.context && contextPreserved right.context
  | _, _ => false

private def arbitraryUnitProjectionIsNone : Bool :=
  let result : HostDriverResult
      (HostStorageDriver.Context Nat (FrameTrace Nat)) :=
    ⟨context, .done .unit []⟩
  result.toWordReturnedFrameCompletion?.isNone

private def syntheticFrameBridgeIsCanonical (word : Word) : Bool :=
  exactReturnedResolution_variant
    ⟨context, word, [.unit]⟩ oldValue word [.unit]

private def storeIndependentReturn
    (completion : WordReturnedFrameCompletion Nat (FrameTrace Nat)) : Bool :=
  let withoutStore : WordReturnedFrameCompletion Nat (FrameTrace Nat) :=
    ⟨completion.context, completion.word, []⟩
  let left : FrameContinuationContext Nat (FrameTrace Nat)
      ParentIndexedSelectedExecutionFixture.TrapReason :=
    completion.toFrameContinuationContext
  let right : FrameContinuationContext Nat (FrameTrace Nat)
      ParentIndexedSelectedExecutionFixture.TrapReason :=
    withoutStore.toFrameContinuationContext
  match left.resolve, right.resolve with
  | .returned leftState leftEffects leftData,
      .returned rightState rightEffects rightData =>
      storageValueAt? leftState storageAddress targetSlot ==
          storageValueAt? rightState storageAddress targetSlot &&
        leftEffects.rollback == rightEffects.rollback &&
        leftEffects.trace.toList == rightEffects.trace.toList &&
        leftData == rightData
  | _, _ => false

def testCheckedHostCoreWordProgramExecution : IO Unit := do
  match CheckedHostCoreWordProgram.ofChecked? code,
      CheckedHostCoreWordProgram.ofProgram? program with
  | some checked, some checkedFromProgram =>
      assertTrue
        (checked.code.program.resultType == .word &&
          checkedFromProgram.code.program.resultType == .word)
        "Word admission did not retain the exact checked program"
  | _, _ =>
      throw (IO.userError "a checked Word program was rejected")

  assertTrue
    ((CheckedHostCoreWordProgram.ofChecked? boolCode).isNone &&
      (CheckedHostCoreWordProgram.ofProgram? rejectedWordProgram).isNone &&
      arbitraryUnitProjectionIsNone)
    "a non-Word or unchecked result received an invented Word return"

  match initialResult with
  | ⟨exhaustedContext, .outOfFuel exhausted⟩ =>
      assertTrue
        (contextHasTarget exhaustedContext oldValue &&
          contextPreserved exhaustedContext &&
          writeRequestReady exhausted &&
          (completionAt writeRequestFuel).isNone)
        "fuel 9 was not retained as exact pre-write exhaustion"
  | _ =>
      throw (IO.userError "fuel 9 unexpectedly completed or faulted")

  match postWriteResult with
  | ⟨exhaustedContext, .outOfFuel exhausted⟩ =>
      assertTrue
        (contextHasTarget exhaustedContext writtenValue &&
          contextPreserved exhaustedContext &&
          beforeInputSuffix exhausted && !writeRequestReady exhausted &&
          (completionAt postWriteFuel).isNone)
        "fuel 10 did not retain the exact post-write continuation"
  | _ =>
      throw (IO.userError "fuel 10 unexpectedly completed or faulted")

  match wordCode.runWithStorage context executionInputs inputRequestFuel with
  | ⟨exhaustedContext, .outOfFuel exhausted⟩ =>
      assertTrue
        (contextHasTarget exhaustedContext writtenValue &&
          contextPreserved exhaustedContext &&
          inputSizeRequestReady exhausted &&
          (completionAt inputRequestFuel).isNone)
        "fuel 15 was not retained at the exact input-size request"
  | _ =>
      throw (IO.userError "fuel 15 unexpectedly completed or faulted")

  match completionAt completionFuel with
  | none =>
      throw (IO.userError "fuel 16 did not project a Word completion")
  | some completion =>
      assertTrue
        (exactReturnedResolution_variant completion writtenValue inputData.sizeWord [] &&
          completion.returnData == canonicalInputSizeReturnData)
        "fuel 16 did not produce the exact canonical returned frame"

  assertTrue
    (sameCompletionObservations resumedCompletion
      (completionAt completionFuel) &&
      sameCompletionObservations postWriteResumedCompletion
        (completionAt completionFuel) &&
      sameCompletionObservations (completionAt 64)
        (completionAt completionFuel))
    "split or larger fuel changed the completed Word observation"

  assertTrue
    (syntheticFrameBridgeIsCanonical Word.zero &&
      syntheticFrameBridgeIsCanonical cellWord &&
      syntheticFrameBridgeIsCanonical Word.maximum)
    "zero, nontrivial, or maximum Word failed the canonical frame bridge"

  match cellCode.runWithStorageReturnedFrameCompletion?
      context executionInputs 6 with
  | none =>
      throw (IO.userError "the cell-bearing Word program did not complete")
  | some completion =>
      assertTrue
        (exactReturnedResolution_variant completion oldValue cellWord [.bool true] &&
          storeIndependentReturn completion)
        "Core Store was lost or serialized into the returned Word bytes"

end Tests
end

section
-- leanmerge: from Solcore.Test.CheckedHostCoreWordCodeSelection
/-! Executable regressions for branch-complete selected Word-code classification. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def codeAddress : Address := ⟨0x81, by decide⟩
private def slot : Word := ⟨0x82, by decide⟩
private def oldValue : Word := ⟨0x83, by decide⟩
private def newValue : Word := ⟨0x84, by decide⟩
private def returnedWord : Word := ⟨0x1234, by decide⟩

private def wordProgram : Program := {
  resultType := .word
  body := .word returnedWord
}

private theorem boolProgram_checked : boolProgram.checkHost = true := by
  decide

private theorem wordProgram_checked : wordProgram.checkHost = true := by
  decide

private def boolCode_variant : CheckedHostCoreProgram :=
  ⟨boolProgram, boolProgram_checked⟩

private def checkedWordCode : CheckedHostCoreProgram :=
  ⟨wordProgram, wordProgram_checked⟩

private def wordCode : CheckedHostCoreWordProgram :=
  ⟨checkedWordCode, rfl⟩

private def emptyWorld : WorldState := WorldState.empty

private def noCodeWorld : WorldState :=
  WorldState.empty.putAccount codeAddress Account.empty

private def nonWordWorld : WorldState :=
  WorldState.empty.putAccount codeAddress
    (Account.empty.withCode boolCode_variant)

private def wordAccount : Account :=
  (Account.empty.storageWrite slot oldValue).withCode checkedWordCode

private def wordWorld : WorldState :=
  WorldState.empty.putAccount codeAddress wordAccount

private def erasedSelectionMatches (state : WorldState) : Bool :=
  match state.selectWordCode codeAddress, state.code? codeAddress with
  | .codeAbsent, none => true
  | .nonWord selected _, some original =>
      selected.program == original.program
  | .word selected, some original =>
      selected.code.program == original.program
  | _, _ => false

private def wordProjectionMatches
    (state : WorldState) (expected : Bool) : Bool :=
  match (state.selectWordCode codeAddress).toWordCode? with
  | none => !expected
  | some selected => expected && selected.code.program == wordProgram

def testCheckedHostCoreWordCodeSelection : IO Unit := do
  match emptyWorld.selectWordCode codeAddress,
      noCodeWorld.selectWordCode codeAddress with
  | .codeAbsent, .codeAbsent => pure ()
  | _, _ =>
      throw (IO.userError
        "missing Account and Account without code were not codeAbsent")

  match nonWordWorld.selectWordCode codeAddress with
  | .nonWord selected _ =>
      assertTrue (selected.program == boolProgram)
        "nonWord selection did not retain the exact checked program"
  | _ =>
      throw (IO.userError "checked Bool code was not classified nonWord")

  match wordWorld.selectWordCode codeAddress with
  | .word selected =>
      assertTrue
        (selected.code.program == wordProgram &&
          selected.code.program.resultType == .word)
        "Word selection did not retain the exact ADR-0141 refinement"
  | _ =>
      throw (IO.userError "checked Word code was not classified word")

  assertTrue
    (erasedSelectionMatches emptyWorld &&
      erasedSelectionMatches noCodeWorld &&
      erasedSelectionMatches nonWordWorld &&
      erasedSelectionMatches wordWorld)
    "checked-code erasure disagreed with WorldState.code?"

  assertTrue
    (wordProjectionMatches emptyWorld false &&
      wordProjectionMatches noCodeWorld false &&
      wordProjectionMatches nonWordWorld false &&
      wordProjectionMatches wordWorld true)
    "Word projection did not isolate exactly the Word branch"

  let writtenAccount := wordAccount.storageWrite slot newValue
  let writtenWorld :=
    WorldState.empty.putAccount codeAddress writtenAccount
  assertTrue (writtenAccount.storageRead slot == newValue)
    "the storage-write preservation fixture did not update storage"
  match writtenWorld.selectWordCode codeAddress with
  | .word selected =>
      assertTrue
        (selected.code.program == wordCode.code.program &&
          erasedSelectionMatches writtenWorld &&
          wordProjectionMatches writtenWorld true)
        "storage writing changed the Word branch or selected code"
  | _ =>
      throw (IO.userError "storage writing changed the selected branch")

end Tests
end

section
-- leanmerge: from Solcore.Test.SelectedCheckedWordExecutionProperties
/-! Compile-only consumers for the public ADR-0143 proof contract. -/

set_option autoImplicit false

namespace Solcore.Test.SelectedCheckedWordExecutionProperties

open ContractRuntime
open SelectedCheckedWordExecution

universe u v

variable {RollbackState : Type u} {TraceState : Type v}
variable (initialContext :
  HostStorageDriver.Context RollbackState TraceState)
variable (inputs : HostStorageDriver.ExecutionInputs)
variable (fuel additional first second : Nat)
variable (execution left right :
  SelectedCheckedWordExecution initialContext inputs)

example : (start initialContext inputs fuel).providedFuel = fuel :=
  start_providedFuel initialContext inputs fuel

example : (start initialContext inputs fuel).selection =
    initialContext.context.values.working.1.selectWordCode
      inputs.codeAddress :=
  start_selection initialContext inputs fuel

example : (start initialContext inputs fuel).execution? =
    (initialContext.context.values.working.1.selectWordCode
        inputs.codeAddress).toWordCode?.map fun code =>
      (code, code.runWithStorage initialContext inputs fuel) :=
  start_execution? initialContext inputs fuel

variable
  (fuelEq : left.providedFuel = right.providedFuel)
  (selectionEq : left.selection = right.selection)
  (rawEq : left.execution? = right.execution?)

example : left = right :=
  ext fuelEq selectionEq rawEq

example : execution =
    start initialContext inputs execution.providedFuel :=
  eq_start execution

example : left = right :=
  eq_of_providedFuel_eq left right fuelEq

example : execution.selection.toCheckedCode? =
    initialContext.context.values.working.1.code? inputs.codeAddress :=
  selection_toCheckedCode? execution

example : execution.selection.toWordCode? =
    (initialContext.context.values.working.1.code?
      inputs.codeAddress).bind CheckedHostCoreWordProgram.ofChecked? :=
  selection_toWordCode? execution

example : execution.execution? = none ↔
    execution.selection.toWordCode? = none :=
  execution?_eq_none_iff_toWordCode?_eq_none execution

variable (checkedCode : CheckedHostCoreProgram)
variable (resultTypeNe : checkedCode.program.resultType ≠ .word)
variable (wordCode : CheckedHostCoreWordProgram)
variable
  (selectedAbsent : execution.selection = .codeAbsent)
  (selectedNonWord :
    execution.selection = .nonWord checkedCode resultTypeNe)
  (selectedWord : execution.selection = .word wordCode)

example : execution.execution? = none :=
  execution?_eq_none_of_codeAbsent execution selectedAbsent

example : execution.execution? = none :=
  execution?_eq_none_of_nonWord
    execution checkedCode resultTypeNe selectedNonWord

example : execution.execution? =
    some
      (wordCode,
        wordCode.runWithStorage
          initialContext inputs execution.providedFuel) :=
  execution?_eq_some_of_word execution wordCode selectedWord

variable (result :
  HostDriverResult
    (HostStorageDriver.Context RollbackState TraceState))

example : execution.execution? = some (wordCode, result) ↔
    execution.selection = .word wordCode ∧
      result = wordCode.runWithStorage
        initialContext inputs execution.providedFuel :=
  execution?_eq_some_iff execution wordCode result

example : execution.execution? = none ↔
    execution.selection = .codeAbsent ∨
      ∃ code resultTypeNe,
        execution.selection = .nonWord code resultTypeNe :=
  execution?_eq_none_iff_branches execution

variable (retained : execution.execution? = some (wordCode, result))

example : result.outcome.HasType
    .word wordCode.code.program.dataDefinitions :=
  execution?_some_hasType execution wordCode result retained

variable
  (finalContext : HostStorageDriver.Context RollbackState TraceState)
  (error : Core.MachineFault)
  (faultState : Core.State)

example : execution.execution? ≠
    some (wordCode, ⟨finalContext, .fault error faultState⟩) :=
  execution?_ne_some_fault
    execution wordCode finalContext error faultState

variable (value : Core.Value) (store : Core.Store)
variable (doneRetained :
  execution.execution? =
    some (wordCode, ⟨finalContext, .done value store⟩))

example : ∃ word, value = .word word :=
  execution?_some_done_word
    execution wordCode finalContext value store doneRetained

variable (completion :
  WordReturnedFrameCompletion RollbackState TraceState)

example : execution.completion? = some completion ↔
    ∃ code,
      execution.execution? =
        some (code, completion.toHostDriverResult) :=
  completion?_eq_some_iff execution completion

example : execution.completion? = some completion ↔
    ∃ code,
      execution.selection = .word code ∧
        code.runWithStorage
            initialContext inputs execution.providedFuel =
          completion.toHostDriverResult :=
  completion?_eq_some_iff_selected_run execution completion

example : execution.completion? = none ↔
    execution.execution? = none ∨
      (∃ code finalContext exhausted,
        execution.execution? =
          some (code, ⟨finalContext, .outOfFuel exhausted⟩)) ∨
      ∃ code finalContext suspension remainingFuel,
        execution.execution? =
          some (code,
            ⟨finalContext, .unsupported suspension remainingFuel⟩) :=
  completion?_eq_none_iff execution

example : execution.completion? = none ↔
    (∃ finalContext exhausted,
      execution.execution? =
        some (wordCode, ⟨finalContext, .outOfFuel exhausted⟩)) ∨
    ∃ finalContext suspension remainingFuel,
      execution.execution? =
        some (wordCode,
          ⟨finalContext, .unsupported suspension remainingFuel⟩) :=
  completion?_eq_none_iff_of_word execution wordCode selectedWord

example : (execution.resumeWithFuel additional).providedFuel =
    execution.providedFuel + additional :=
  resumeWithFuel_providedFuel execution additional

example : (execution.resumeWithFuel additional).selection =
    execution.selection :=
  resumeWithFuel_selection execution additional

example : (execution.resumeWithFuel additional).execution? =
    execution.execution?.map fun selectedRun =>
      (selectedRun.1,
        selectedRun.2.resumeWithFuel
          (@HostStorageDriver.handler
            RollbackState TraceState inputs) additional) :=
  resumeWithFuel_execution? execution additional

example : execution.resumeWithFuel additional =
    start initialContext inputs
      (execution.providedFuel + additional) :=
  resumeWithFuel_eq_start execution additional

example : (start initialContext inputs fuel).resumeWithFuel additional =
    start initialContext inputs (fuel + additional) :=
  start_resumeWithFuel initialContext inputs fuel additional

example : execution.resumeWithFuel 0 = execution :=
  resumeWithFuel_zero execution

example : (execution.resumeWithFuel first).resumeWithFuel second =
    execution.resumeWithFuel (first + second) :=
  resumeWithFuel_add execution first second

example : (execution.resumeWithFuel additional).execution? = none ↔
    execution.execution? = none :=
  resumeWithFuel_execution?_eq_none_iff execution additional

example : (execution.resumeWithFuel additional).completion? =
    (start initialContext inputs
      (execution.providedFuel + additional)).completion? :=
  completion?_resumeWithFuel_eq_start execution additional

variable (completionRetained :
  execution.execution? =
    some (wordCode, completion.toHostDriverResult))

example : (execution.resumeWithFuel additional).execution? =
    some (wordCode, completion.toHostDriverResult) :=
  execution?_resumeWithFuel_of_completion
    execution additional wordCode completion completionRetained

variable (completed : execution.completion? = some completion)

example : (execution.resumeWithFuel additional).completion? =
    some completion :=
  completion?_resumeWithFuel_of_some
    execution additional completion completed

end Solcore.Test.SelectedCheckedWordExecutionProperties
end
