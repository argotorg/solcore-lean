import Solcore.ContractRuntime.CheckedHostCoreWordProgramExecutionProperties
import Solcore.ContractRuntime.SelectedCheckedWordExecutionProperties

/-! Safety and exact completion laws for selected checked Word execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.SelectedCheckedWordExecution

universe u v

/-- At fixed indices, the cumulative offered fuel determines the whole value. -/
theorem eq_of_providedFuel_eq
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (left right : SelectedCheckedWordExecution initialContext inputs)
    (providedFuel : left.providedFuel = right.providedFuel) :
    left = right := by
  calc
    left = start initialContext inputs left.providedFuel := eq_start left
    _ = start initialContext inputs right.providedFuel :=
      congrArg (start initialContext inputs) providedFuel
    _ = right := (eq_start right).symm

/-- Every retained raw run has the declared checked Word type. -/
theorem execution?_some_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (result :
      HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState))
    (retained : execution.execution? = some (code, result)) :
    result.outcome.HasType .word code.code.program.dataDefinitions := by
  have exactRun :=
    (execution.execution?_eq_some_iff code result).mp retained
  rw [exactRun.2]
  exact code.runWithStorage_hasType
    initialContext inputs execution.providedFuel

/-- A retained checked Word run can never be an exact raw fault result. -/
theorem execution?_ne_some_fault
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (finalContext :
      HostStorageDriver.Context RollbackState TraceState)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    execution.execution? ≠
      some (code, ⟨finalContext, .fault error faultState⟩) := by
  intro retained
  have exactRun :=
    (execution.execution?_eq_some_iff
      code ⟨finalContext, .fault error faultState⟩).mp retained
  exact code.runWithStorage_ne_fault_result
    initialContext finalContext inputs execution.providedFuel
      error faultState exactRun.2.symm

/-- Every completed retained execution contains exactly a Word value. -/
theorem execution?_some_done_word
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (finalContext :
      HostStorageDriver.Context RollbackState TraceState)
    (value : Core.Value)
    (store : Core.Store)
    (retained :
      execution.execution? =
        some (code, ⟨finalContext, .done value store⟩)) :
    ∃ word, value = .word word := by
  have exactRun :=
    (execution.execution?_eq_some_iff
      code ⟨finalContext, .done value store⟩).mp retained
  exact code.runWithStorage_done_word
    initialContext finalContext inputs exactRun.2.symm

/-- Successful selected projection reconstructs the exact retained raw run. -/
theorem completion?_eq_some_iff
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState TraceState) :
    execution.completion? = some completion ↔
      ∃ code,
        execution.execution? =
          some (code, completion.toHostDriverResult) := by
  unfold completion?
  cases retained : execution.execution? with
  | none => simp
  | some selectedRun =>
      cases selectedRun with
      | mk code result =>
          simp only [Option.bind_some]
          rw [HostDriverResult.toWordReturnedFrameCompletion?_eq_some_iff]
          simp

/-- Successful projection exposes the exact selected code and canonical run. -/
theorem completion?_eq_some_iff_selected_run
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState TraceState) :
    execution.completion? = some completion ↔
      ∃ code,
        execution.selection = .word code ∧
          code.runWithStorage
              initialContext inputs execution.providedFuel =
            completion.toHostDriverResult := by
  rw [execution.completion?_eq_some_iff completion]
  constructor
  · rintro ⟨code, retained⟩
    have exactRun :=
      (execution.execution?_eq_some_iff
        code completion.toHostDriverResult).mp retained
    exact ⟨code, exactRun.1, exactRun.2.symm⟩
  · rintro ⟨code, selected, exactRun⟩
    exact ⟨code,
      (execution.execution?_eq_some_iff
        code completion.toHostDriverResult).mpr
          ⟨selected, exactRun.symm⟩⟩

/--
Globally, missing completion means no Word execution, exact exhaustion, or an
explicit unsupported-policy boundary.
-/
theorem completion?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.completion? = none ↔
      execution.execution? = none ∨
        (∃ code finalContext exhausted,
          execution.execution? =
            some (code, ⟨finalContext, .outOfFuel exhausted⟩)) ∨
        ∃ code finalContext suspension remainingFuel,
          execution.execution? =
            some (code,
              ⟨finalContext, .unsupported suspension remainingFuel⟩) := by
  unfold completion?
  cases retained : execution.execution? with
  | none => simp
  | some selectedRun =>
      cases selectedRun with
      | mk code result =>
          have typing :=
            execution.execution?_some_hasType code result retained
          simp only [Option.bind_some]
          rw [HostDriverResult.toWordReturnedFrameCompletion?_eq_none_iff_of_hasType
            result typing]
          simp

/-- Under an exact Word selection, absence is exhaustion or policy rejection. -/
theorem completion?_eq_none_iff_of_word
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (selected : execution.selection = .word code) :
    execution.completion? = none ↔
      (∃ finalContext exhausted,
        execution.execution? =
          some (code, ⟨finalContext, .outOfFuel exhausted⟩)) ∨
      ∃ finalContext suspension remainingFuel,
        execution.execution? =
          some (code,
            ⟨finalContext, .unsupported suspension remainingFuel⟩) := by
  unfold completion?
  rw [execution.execution?_eq_some_of_word code selected]
  simp only [Option.bind_some]
  simpa only [CheckedHostCoreWordProgram.runWithStorageReturnedFrameCompletion?,
    Option.some.injEq, Prod.mk.injEq, true_and] using
      code.runWithStorageReturnedFrameCompletion?_eq_none_iff
        initialContext inputs execution.providedFuel

end Solcore.ContractRuntime.SelectedCheckedWordExecution
