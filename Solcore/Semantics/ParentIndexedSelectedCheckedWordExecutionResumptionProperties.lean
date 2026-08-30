import Solcore.Semantics.ParentIndexedSelectedCheckedWordExecutionProperties
import Solcore.Semantics.ParentIndexedSelectedCheckedWordExecutionResumption
import Solcore.Semantics.SelectedCheckedWordExecutionResumptionProperties

/-! Canonicality and algebra for parent-indexed selected Word resumption. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution

universe u v

/-- A resumed carrier is the exact parent start at its summed budget. -/
theorem some_resumeWithFuel_eq_start?
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
    some (entry.resumeWithFuel additional) =
      start? initialization storageAddress inputs
        (entry.execution.providedFuel + additional) := by
  rw [start?_of_present initialization storageAddress inputs
    (entry.execution.providedFuel + additional) entry.initialContext
    entry.context_refined]
  congr 1
  apply ext
  · rfl
  · exact heq_of_eq
      (SelectedCheckedWordExecution.resumeWithFuel_eq_start
        entry.execution additional)

/-- Starting and then resuming agrees with one parent start at summed fuel. -/
theorem start?_map_resumeWithFuel
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    (start? initialization storageAddress inputs fuel).map
        (fun entry => entry.resumeWithFuel additional) =
      start? initialization storageAddress inputs (fuel + additional) := by
  cases started : start? initialization storageAddress inputs fuel with
  | none =>
      have absent :=
        (start?_eq_none_iff initialization storageAddress inputs fuel).mp
          started
      simpa [started] using
        ((start?_eq_none_iff initialization storageAddress inputs
          (fuel + additional)).mpr absent).symm
  | some entry =>
      have fuelEq : entry.execution.providedFuel = fuel := by
        have canonical :=
          (start?_eq_some_iff initialization storageAddress inputs fuel
            entry).mp started
        rw [canonical]
        rfl
      simpa [started, fuelEq] using entry.some_resumeWithFuel_eq_start? additional

/-- Offering zero additional fuel preserves the entire provenance carrier. -/
@[simp] theorem resumeWithFuel_zero
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.resumeWithFuel 0 = entry := by
  apply ext
  · rfl
  · exact heq_of_eq entry.execution.resumeWithFuel_zero

/-- Successive fuel offers combine by addition on the whole carrier. -/
theorem resumeWithFuel_add
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (first second : Nat) :
    (entry.resumeWithFuel first).resumeWithFuel second =
      entry.resumeWithFuel (first + second) := by
  apply ext
  · rfl
  · exact heq_of_eq
      (SelectedCheckedWordExecution.resumeWithFuel_add
        entry.execution first second)

/-- Completion after resumption is exactly the inner fixed-input view. -/
theorem completion?_resumeWithFuel
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
    (entry.resumeWithFuel additional).execution.completion? =
      (SelectedCheckedWordExecution.start entry.initialContext inputs
        (entry.execution.providedFuel + additional)).completion? := by
  exact SelectedCheckedWordExecution.completion?_resumeWithFuel_eq_start
    entry.execution additional

/-- Once completion exists, parent resumption retains that exact completion. -/
theorem completion?_resumeWithFuel_of_some
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (additional : Nat)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion) :
    (entry.resumeWithFuel additional).execution.completion? =
      some completion :=
  SelectedCheckedWordExecution.completion?_resumeWithFuel_of_some
    entry.execution additional completion completed

end Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution
