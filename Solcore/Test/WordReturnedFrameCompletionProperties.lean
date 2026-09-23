import Solcore.ContractRuntime.CheckedHostCoreWordProgramExecutionProperties
import Solcore.ContractRuntime.CheckedHostCoreWordProgramProperties

/-! Compile-only consumers for checked Word returned-frame proof contracts. -/

set_option autoImplicit false

namespace Solcore.Test.WordReturnedFrameCompletionProperties

open ContractRuntime

universe u v w

variable (checkedCode : CheckedHostCoreProgram)
variable (resultTypeEq : checkedCode.program.resultType = .word)
variable (resultTypeNe : checkedCode.program.resultType ≠ .word)

example : (CheckedHostCoreWordProgram.mk checkedCode resultTypeEq).code =
    checkedCode :=
  CheckedHostCoreWordProgram.mk_code checkedCode resultTypeEq

example :
    (CheckedHostCoreWordProgram.mk checkedCode resultTypeEq).code.program.resultType =
      .word :=
  CheckedHostCoreWordProgram.mk_resultType checkedCode resultTypeEq

example : CheckedHostCoreWordProgram.ofChecked? checkedCode =
    some ⟨checkedCode, resultTypeEq⟩ :=
  CheckedHostCoreWordProgram.ofChecked?_of_word checkedCode resultTypeEq

example : CheckedHostCoreWordProgram.ofChecked? checkedCode = none :=
  CheckedHostCoreWordProgram.ofChecked?_of_nonword checkedCode resultTypeNe

variable (program : Core.Program)
variable (checked : program.checkHost = true)
variable (rejected : program.checkHost = false)
variable (programWord : program.resultType = .word)
variable (programNonword : program.resultType ≠ .word)

example : CheckedHostCoreWordProgram.ofProgram? program =
    some ⟨⟨program, checked⟩, programWord⟩ :=
  CheckedHostCoreWordProgram.ofProgram?_of_checked_word
    program checked programWord

example : CheckedHostCoreWordProgram.ofProgram? program = none :=
  CheckedHostCoreWordProgram.ofProgram?_of_rejected program rejected

example : CheckedHostCoreWordProgram.ofProgram? program = none :=
  CheckedHostCoreWordProgram.ofProgram?_of_checked_nonword
    program checked programNonword

variable {RollbackState : Type u} {TraceState : Type v}
variable {TrapReason : Type w}

abbrev Context (RollbackState : Type u) (TraceState : Type v) :=
  HostStorageDriver.Context RollbackState TraceState
abbrev Completion (RollbackState : Type u) (TraceState : Type v) :=
  WordReturnedFrameCompletion RollbackState TraceState

variable (context : Context RollbackState TraceState)
variable (word : Core.Word) (store : Core.Store)
variable (value : Core.Value) (state : Core.State)
variable (error : Core.MachineFault)

example :
    (HostDriverResult.mk context
      (.done (.word word) store)).toWordReturnedFrameCompletion? =
      some ⟨context, word, store⟩ :=
  HostDriverResult.toWordReturnedFrameCompletion?_done_word
    context word store

example :
    (HostDriverResult.mk context
      (.done value store)).toWordReturnedFrameCompletion? = none ↔
      ∀ candidate, value ≠ .word candidate :=
  HostDriverResult.toWordReturnedFrameCompletion?_done_eq_none_iff
    context value store

example :
    (HostDriverResult.mk context
      (.outOfFuel state)).toWordReturnedFrameCompletion? = none :=
  HostDriverResult.toWordReturnedFrameCompletion?_outOfFuel context state

example :
    (HostDriverResult.mk context
      (.fault error state)).toWordReturnedFrameCompletion? = none :=
  HostDriverResult.toWordReturnedFrameCompletion?_fault
    context error state

variable (result : HostDriverResult (Context RollbackState TraceState))
variable (completion : Completion RollbackState TraceState)

example : (WordReturnedFrameCompletion.mk context word store).context =
    context :=
  WordReturnedFrameCompletion.mk_context context word store

example : (WordReturnedFrameCompletion.mk context word store).word = word :=
  WordReturnedFrameCompletion.mk_word context word store

example : (WordReturnedFrameCompletion.mk context word store).store = store :=
  WordReturnedFrameCompletion.mk_store context word store

example : result.toWordReturnedFrameCompletion? = some completion ↔
    result = completion.toHostDriverResult :=
  HostDriverResult.toWordReturnedFrameCompletion?_eq_some_iff
    result completion

example : completion.toHostDriverResult.toWordReturnedFrameCompletion? =
    some completion :=
  WordReturnedFrameCompletion.toWordReturnedFrameCompletion?_toHostDriverResult
    completion

example : completion.returnData.size = 32 :=
  WordReturnedFrameCompletion.returnData_size completion

example : decodeWordBytesBE? completion.returnData = some completion.word :=
  WordReturnedFrameCompletion.decodeWordBytesBE?_returnData completion

example :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).stateCheckpoint =
      completion.context.context.values.checkpoint.state :=
  WordReturnedFrameCompletion.stateCheckpoint_toFrameContinuationContext
    completion

example :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).effectCheckpoint =
      completion.context.context.values.checkpoint.effects :=
  WordReturnedFrameCompletion.effectCheckpoint_toFrameContinuationContext
    completion

example :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).effectWorking =
      completion.context.context.values.working.2 :=
  WordReturnedFrameCompletion.effectWorking_toFrameContinuationContext
    completion

example :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).result =
      ⟨completion.context.context.values.working.1,
        .returned completion.returnData⟩ :=
  WordReturnedFrameCompletion.result_toFrameContinuationContext completion

example :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      .returned completion.context.context.values.working.1
        completion.context.context.values.working.2 completion.returnData :=
  WordReturnedFrameCompletion.resolve_toFrameContinuationContext completion

variable (leftStore rightStore : Core.Store)

example :
    ((⟨context, word, leftStore⟩ :
        Completion RollbackState TraceState).toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason) =
    ((⟨context, word, rightStore⟩ :
        Completion RollbackState TraceState).toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason) :=
  WordReturnedFrameCompletion.toFrameContinuationContext_store_independent
    context word leftStore rightStore

variable {definitions : Core.DataEnvironment}
variable (typing : result.outcome.HasType .word definitions)

example : result.toWordReturnedFrameCompletion? = none ↔
    (∃ finalContext exhausted,
      result = ⟨finalContext, .outOfFuel exhausted⟩) ∨
    ∃ finalContext suspension remainingFuel,
      result = ⟨finalContext, .unsupported suspension remainingFuel⟩ :=
  HostDriverResult.toWordReturnedFrameCompletion?_eq_none_iff_of_hasType
    result typing

variable (handler : HostHandler (Context RollbackState TraceState))
variable (additional : Nat)
variable (projected :
  result.toWordReturnedFrameCompletion? = some completion)

example : HostDriverResult.toWordReturnedFrameCompletion?
      (result.resumeWithFuel handler additional) = some completion :=
  HostDriverResult.toWordReturnedFrameCompletion?_resumeWithFuel_of_some
    result handler additional completion projected

variable (code : CheckedHostCoreWordProgram)
variable (inputs : HostStorageDriver.ExecutionInputs) (fuel : Nat)

example : (code.runWithStorage context inputs fuel).outcome.HasType
    .word code.code.program.dataDefinitions :=
  CheckedHostCoreWordProgram.runWithStorage_hasType
    code context inputs fuel

variable (faultState : Core.State)

example : (code.runWithStorage context inputs fuel).outcome ≠
    .fault error faultState :=
  CheckedHostCoreWordProgram.runWithStorage_ne_fault
    code context inputs fuel error faultState

variable (finalContext : Context RollbackState TraceState)

example : code.runWithStorage context inputs fuel ≠
    ⟨finalContext, .fault error faultState⟩ :=
  CheckedHostCoreWordProgram.runWithStorage_ne_fault_result
    code context finalContext inputs fuel error faultState

variable (execution : code.runWithStorage context inputs fuel =
  ⟨finalContext, .done value store⟩)

example : ∃ completedWord, value = .word completedWord :=
  CheckedHostCoreWordProgram.runWithStorage_done_word
    code context finalContext inputs execution

example :
    code.runWithStorageReturnedFrameCompletion? context inputs fuel =
        some completion ↔
      code.runWithStorage context inputs fuel =
        completion.toHostDriverResult :=
  CheckedHostCoreWordProgram.runWithStorageReturnedFrameCompletion?_eq_some_iff
    code context inputs fuel completion

example :
    code.runWithStorageReturnedFrameCompletion? context inputs fuel = none ↔
      (∃ retainedContext exhausted,
        code.runWithStorage context inputs fuel =
          ⟨retainedContext, .outOfFuel exhausted⟩) ∨
      ∃ retainedContext suspension remainingFuel,
        code.runWithStorage context inputs fuel =
          ⟨retainedContext,
            .unsupported suspension remainingFuel⟩ :=
  CheckedHostCoreWordProgram.runWithStorageReturnedFrameCompletion?_eq_none_iff
    code context inputs fuel

variable {completedFuel largerFuel : Nat}
variable (completed :
  code.runWithStorageReturnedFrameCompletion?
    context inputs completedFuel = some completion)
variable (more : completedFuel ≤ largerFuel)

example : code.runWithStorageReturnedFrameCompletion?
    context inputs largerFuel = some completion :=
  CheckedHostCoreWordProgram.runWithStorageReturnedFrameCompletion?_some_stable
    code context inputs completed more

example :
    (code.runWithStorage context inputs fuel).resumeWithFuel
        (@HostStorageDriver.handler RollbackState TraceState inputs)
        additional =
      code.runWithStorage context inputs (fuel + additional) :=
  CheckedHostCoreWordProgram.runWithStorage_resumeWithFuel
    code context inputs fuel additional

example :
    ((code.runWithStorage context inputs fuel).resumeWithFuel
        (@HostStorageDriver.handler RollbackState TraceState inputs)
        additional).toWordReturnedFrameCompletion? =
      code.runWithStorageReturnedFrameCompletion?
        context inputs (fuel + additional) :=
  CheckedHostCoreWordProgram.toWordReturnedFrameCompletion?_resumeWithFuel_runWithStorage
    code context inputs fuel additional

end Solcore.Test.WordReturnedFrameCompletionProperties
