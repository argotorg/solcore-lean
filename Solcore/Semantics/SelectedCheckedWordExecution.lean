import Solcore.Semantics.CheckedHostCoreWordProgramExecution
import Solcore.Semantics.WorldStateWordCodeSelection

/-! Proof-refined execution of address-selected checked Word code. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

/--
One address selection and its optional checked Word execution, indexed by the
exact initial context and immutable execution inputs.
-/
structure SelectedCheckedWordExecution
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs) where
  providedFuel : Nat
  selection : CheckedHostCoreWordCodeSelection
  selection_eq :
    selection =
      initialContext.context.values.working.1.selectWordCode
        inputs.codeAddress
  execution? :
    Option
      (CheckedHostCoreWordProgram ×
        HostDriverResult
          (HostStorageDriver.Context RollbackState TraceState))
  execution_eq_run :
    execution? =
      selection.toWordCode?.map fun code =>
        (code, code.runWithStorage initialContext inputs providedFuel)

namespace SelectedCheckedWordExecution

/-- Select once and run exactly the selected Word code, when one exists. -/
def start
    {RollbackState : Type u} {TraceState : Type v}
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    SelectedCheckedWordExecution initialContext inputs :=
  let selection :=
    initialContext.context.values.working.1.selectWordCode
      inputs.codeAddress
  {
    providedFuel := fuel
    selection := selection
    selection_eq := rfl
    execution? :=
      selection.toWordCode?.map fun code =>
        (code, code.runWithStorage initialContext inputs fuel)
    execution_eq_run := rfl
  }

/-- Project only the existing successful checked Word completion. -/
def completion?
    {RollbackState : Type u} {TraceState : Type v}
    {initialContext : HostStorageDriver.Context RollbackState TraceState}
    {inputs : HostStorageDriver.ExecutionInputs}
    (execution : SelectedCheckedWordExecution initialContext inputs) :
    Option (WordReturnedFrameCompletion RollbackState TraceState) :=
  execution.execution?.bind fun selectedRun =>
    selectedRun.2.toWordReturnedFrameCompletion?

end SelectedCheckedWordExecution

end Solcore.Semantics
