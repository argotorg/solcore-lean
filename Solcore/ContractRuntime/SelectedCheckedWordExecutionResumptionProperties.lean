import Solcore.ContractRuntime.SelectedCheckedWordExecutionResumption

/-! Canonicality, algebra, and terminal stability of selected Word resumption. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.SelectedCheckedWordExecution

universe u v

/-- Resumption is the canonical one-shot selected run at the summed budget. -/
theorem resumeWithFuel_eq_start
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    execution.resumeWithFuel additional =
      start initialContext inputs
        (execution.providedFuel + additional) := by
  simpa using eq_start (execution.resumeWithFuel additional)

/-- Starting and then resuming agrees with one start at summed fuel. -/
theorem start_resumeWithFuel
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    (start initialContext inputs fuel).resumeWithFuel additional =
      start initialContext inputs (fuel + additional) := by
  simpa using
    resumeWithFuel_eq_start
      (start initialContext inputs fuel) additional

/-- Offering zero additional fuel is the identity on the whole value. -/
@[simp] theorem resumeWithFuel_zero
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    execution.resumeWithFuel 0 = execution := by
  apply eq_of_providedFuel_eq
  simp

/-- Successive fuel offers combine by addition on the whole value. -/
theorem resumeWithFuel_add
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (first second : Nat) :
    (execution.resumeWithFuel first).resumeWithFuel second =
      execution.resumeWithFuel (first + second) := by
  apply eq_of_providedFuel_eq
  simp [Nat.add_assoc]

/-- Resumption cannot create a raw run for either non-executing branch. -/
theorem resumeWithFuel_execution?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    (execution.resumeWithFuel additional).execution? = none ↔
      execution.execution? = none := by
  simp

/-- Selected completion after resumption equals the summed one-shot view. -/
theorem completion?_resumeWithFuel_eq_start
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    (execution.resumeWithFuel additional).completion? =
      (start initialContext inputs
        (execution.providedFuel + additional)).completion? := by
  rw [execution.resumeWithFuel_eq_start additional]

/-- The exact successful raw run is terminal under every later fuel offer. -/
theorem execution?_resumeWithFuel_of_completion
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat)
    (code : CheckedHostCoreWordProgram)
    (completion :
      WordReturnedFrameCompletion RollbackState TraceState)
    (retained :
      execution.execution? =
        some (code, completion.toHostDriverResult)) :
    (execution.resumeWithFuel additional).execution? =
      some (code, completion.toHostDriverResult) := by
  rw [resumeWithFuel_execution?, retained]
  rfl

/-- Once selected Word completion exists, every resumption returns it exactly. -/
theorem completion?_resumeWithFuel_of_some
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState TraceState)
    (completed : execution.completion? = some completion) :
    (execution.resumeWithFuel additional).completion? = some completion := by
  obtain ⟨code, retained⟩ :=
    (execution.completion?_eq_some_iff completion).mp completed
  apply (execution.resumeWithFuel additional).completion?_eq_some_iff
    completion |>.mpr
  exact ⟨code,
    execution.execution?_resumeWithFuel_of_completion
      additional code completion retained⟩

end Solcore.ContractRuntime.SelectedCheckedWordExecution
