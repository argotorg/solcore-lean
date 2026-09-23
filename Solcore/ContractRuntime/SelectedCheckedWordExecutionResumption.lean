import Solcore.ContractRuntime.SelectedCheckedWordExecutionSafetyProperties

/-! Fixed-input fuel resumption for selected checked Word execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.SelectedCheckedWordExecution

universe u v

/--
Offer more fuel while preserving the exact selected code, initial context, and
immutable execution inputs.
-/
def resumeWithFuel
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    SelectedCheckedWordExecution initialContext inputs :=
  {
    providedFuel := execution.providedFuel + additional
    selection := execution.selection
    selection_eq := execution.selection_eq
    execution? := execution.execution?.map fun selectedRun =>
      (selectedRun.1,
        selectedRun.2.resumeWithFuel
          (@HostStorageDriver.handler RollbackState TraceState inputs)
          additional)
    execution_eq_run := by
      rw [execution.execution_eq_run]
      cases execution.selection with
      | codeAbsent => rfl
      | nonWord code resultTypeNe => rfl
      | word code =>
          simp only [CheckedHostCoreWordCodeSelection.toWordCode?_word,
            Option.map_some]
          rw [code.runWithStorage_resumeWithFuel
            initialContext inputs execution.providedFuel additional]
  }

@[simp] theorem resumeWithFuel_providedFuel
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    (execution.resumeWithFuel additional).providedFuel =
      execution.providedFuel + additional :=
  rfl

@[simp] theorem resumeWithFuel_selection
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    (execution.resumeWithFuel additional).selection = execution.selection :=
  rfl

@[simp] theorem resumeWithFuel_execution?
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    (execution.resumeWithFuel additional).execution? =
      execution.execution?.map fun selectedRun =>
        (selectedRun.1,
          selectedRun.2.resumeWithFuel
            (@HostStorageDriver.handler RollbackState TraceState inputs)
            additional) :=
  rfl

end Solcore.ContractRuntime.SelectedCheckedWordExecution
