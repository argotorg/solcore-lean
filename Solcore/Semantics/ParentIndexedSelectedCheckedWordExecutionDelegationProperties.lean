import Solcore.Semantics.ParentIndexedSelectedCheckedWordExecutionProperties
import Solcore.Semantics.SelectedCheckedWordExecutionSafetyProperties

/-! Direct parent-carrier access to retained ADR-0143 branches and provenance. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution

universe u v

/-- The retained initial working rollback is exactly the initialization input. -/
theorem initialContext_workingRollback
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.values.working.2.rollback =
      initialization.workingRollback := by
  rw [entry.initialContext_workingEffects]

/-- The retained initial working trace is exactly the indexed parent trace. -/
theorem initialContext_parentTrace
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.values.working.2.trace =
      parentWorking.2.trace := by
  rw [entry.initialContext_workingEffects]

/-- Missing raw execution is exactly code absence or checked non-Word code. -/
theorem execution?_eq_none_iff_branches
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.execution.execution? = none ↔
      entry.execution.selection = .codeAbsent ∨
        ∃ code resultTypeNe,
          entry.execution.selection = .nonWord code resultTypeNe :=
  entry.execution.execution?_eq_none_iff_branches

/-- Exact completion reconstructs the exact selected checked Word raw result. -/
theorem completion?_eq_some_iff
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event)) :
    entry.execution.completion? = some completion ↔
      ∃ code,
        entry.execution.execution? =
          some (code, completion.toHostDriverResult) :=
  entry.execution.completion?_eq_some_iff completion

/-- Missing completion retains absence, exhaustion, and policy rejection. -/
theorem completion?_eq_none_iff
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.execution.completion? = none ↔
      entry.execution.execution? = none ∨
        (∃ code finalContext exhausted,
          entry.execution.execution? =
            some (code, ⟨finalContext, .outOfFuel exhausted⟩)) ∨
        ∃ code finalContext suspension remainingFuel,
          entry.execution.execution? =
            some (code,
              ⟨finalContext, .unsupported suspension remainingFuel⟩) :=
  entry.execution.completion?_eq_none_iff

end Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution
