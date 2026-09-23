import Solcore.ContractRuntime.SelectedCheckedWordExecution

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
