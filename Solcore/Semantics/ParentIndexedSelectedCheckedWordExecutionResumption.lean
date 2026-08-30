import Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution
import Solcore.Semantics.SelectedCheckedWordExecutionResumption

/-! Closed fuel resumption for parent-indexed selected checked Word execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution

universe u v

/--
Offer more fuel without replacing the parent initialization, storage Address,
immutable execution inputs, or the exact refined initial context.
-/
def resumeWithFuel
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs :=
  {
    initialContext := entry.initialContext
    context_refined := entry.context_refined
    execution := entry.execution.resumeWithFuel additional
  }

@[simp] theorem resumeWithFuel_initialContext
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    (entry.resumeWithFuel additional).initialContext =
      entry.initialContext :=
  rfl

@[simp] theorem resumeWithFuel_execution
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    (entry.resumeWithFuel additional).execution =
      entry.execution.resumeWithFuel additional :=
  rfl

@[simp] theorem resumeWithFuel_providedFuel
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    (entry.resumeWithFuel additional).execution.providedFuel =
      entry.execution.providedFuel + additional :=
  rfl

@[simp] theorem resumeWithFuel_selection
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat) :
    (entry.resumeWithFuel additional).execution.selection =
      entry.execution.selection :=
  rfl

end Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution
