import Solcore.Semantics.CheckedHostCoreWordCodeSelectionProperties
import Solcore.Semantics.WorldStateWordCodeSelectionProperties
import Solcore.Semantics.SelectedCheckedWordExecution

/-! Canonical selection and execution laws for selected checked Word code. -/

set_option autoImplicit false

namespace Solcore.Semantics.SelectedCheckedWordExecution

universe u v

@[simp] theorem start_providedFuel
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (start initialContext inputs fuel).providedFuel = fuel :=
  rfl

@[simp] theorem start_selection
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (start initialContext inputs fuel).selection =
      initialContext.context.values.working.1.selectWordCode
        inputs.codeAddress :=
  rfl

@[simp] theorem start_execution?
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (start initialContext inputs fuel).execution? =
      (initialContext.context.values.working.1.selectWordCode
          inputs.codeAddress).toWordCode?.map fun code =>
        (code, code.runWithStorage initialContext inputs fuel) :=
  rfl

/-- The three computational fields determine the proof-refined execution. -/
@[ext] theorem ext
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    {left right : SelectedCheckedWordExecution initialContext inputs}
    (providedFuel : left.providedFuel = right.providedFuel)
    (selection : left.selection = right.selection)
    (execution : left.execution? = right.execution?) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Every certified value is the canonical start at its recorded total fuel. -/
theorem eq_start
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution = start initialContext inputs execution.providedFuel := by
  apply ext
  · rfl
  · exact execution.selection_eq
  · rw [execution.execution_eq_run]
    simp only [start_execution?, execution.selection_eq]

/-- Erasing the retained branch recovers the exact selected checked code. -/
theorem selection_toCheckedCode?
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.selection.toCheckedCode? =
      initialContext.context.values.working.1.code? inputs.codeAddress := by
  rw [execution.selection_eq]
  exact WorldState.toCheckedCode?_selectWordCode _ _

/-- Word projection is the existing optional refinement of selected code. -/
theorem selection_toWordCode?
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.selection.toWordCode? =
      (initialContext.context.values.working.1.code?
        inputs.codeAddress).bind CheckedHostCoreWordProgram.ofChecked? := by
  rw [execution.selection_eq]
  exact WorldState.toWordCode?_selectWordCode _ _

/-- No raw execution exists exactly when no Word program was selected. -/
theorem execution?_eq_none_iff_toWordCode?_eq_none
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.execution? = none ↔
      execution.selection.toWordCode? = none := by
  rw [execution.execution_eq_run]
  simp

theorem execution?_eq_none_of_codeAbsent
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (selected : execution.selection = .codeAbsent) :
    execution.execution? = none := by
  rw [execution.execution_eq_run, selected]
  rfl

theorem execution?_eq_none_of_nonWord
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word)
    (selected : execution.selection = .nonWord code resultTypeNe) :
    execution.execution? = none := by
  rw [execution.execution_eq_run, selected]
  rfl

theorem execution?_eq_some_of_word
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (selected : execution.selection = .word code) :
    execution.execution? =
      some
        (code,
          code.runWithStorage initialContext inputs execution.providedFuel) := by
  rw [execution.execution_eq_run, selected]
  rfl

/-- Exact retained runs characterize the Word selection branch. -/
theorem execution?_eq_some_iff
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (code : CheckedHostCoreWordProgram)
    (result :
      HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :
    execution.execution? = some (code, result) ↔
      execution.selection = .word code ∧
        result =
          code.runWithStorage
            initialContext inputs execution.providedFuel := by
  rw [execution.execution_eq_run]
  cases selectionEq : execution.selection with
  | codeAbsent => simp
  | nonWord selectedCode resultTypeNe => simp
  | word selectedCode =>
      simp only [CheckedHostCoreWordCodeSelection.toWordCode?_word, Option.map_some,
        Option.some.injEq, Prod.mk.injEq,
        CheckedHostCoreWordCodeSelection.word.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩

/-- Missing execution is exactly one of the two non-Word-execution branches. -/
theorem execution?_eq_none_iff_branches
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.execution? = none ↔
      execution.selection = .codeAbsent ∨
        ∃ code resultTypeNe,
          execution.selection = .nonWord code resultTypeNe := by
  rw [execution.execution_eq_run]
  cases selectionEq : execution.selection with
  | codeAbsent => simp
  | nonWord code resultTypeNe =>
      exact ⟨fun _ => Or.inr ⟨code, resultTypeNe, rfl⟩, fun _ => rfl⟩
  | word code => simp

end Solcore.Semantics.SelectedCheckedWordExecution
