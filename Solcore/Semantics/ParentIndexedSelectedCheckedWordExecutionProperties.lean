import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccountProperties
import Solcore.Semantics.ParentIndexedFrameInitializationProperties
import Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution
import Solcore.Semantics.SelectedCheckedWordExecutionProperties

/-! Exact storage refinement and provenance laws for ADR-0144. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution

universe u v

/-- Outer absence means exactly that the selected storage Account is absent. -/
theorem start?_eq_none_iff
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    start? initialization storageAddress inputs fuel = none ↔
      initialization.initialWorld.account? storageAddress = none := by
  cases observed : initialization.initialWorld.account? storageAddress with
  | none =>
      have refinedNone :=
        ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
          initialization storageAddress observed
      unfold start?
      split
      · simp
      · rename_i context refinedSome
        rw [refinedNone] at refinedSome
        contradiction
  | some account =>
      have refinedSome :=
        ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
          initialization storageAddress account observed
      unfold start?
      split
      · rename_i refinedNone
        rw [refinedSome] at refinedNone
        contradiction
      · simp

/-- Exact present storage refinement starts the exact ADR-0143 execution. -/
@[simp] theorem start?_of_present
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context) :
    start? initialization storageAddress inputs fuel =
      some
        (ParentIndexedSelectedCheckedWordExecution.mk context refined
          (SelectedCheckedWordExecution.start context inputs fuel)) := by
  unfold start?
  split
  · rename_i refinedNone
    rw [refined] at refinedNone
    contradiction
  · rename_i selectedContext selected
    have contextEq : selectedContext = context :=
      Option.some.inj (selected.symm.trans refined)
    subst selectedContext
    rfl

/-- The named carrier erases to exactly the existing refinement and inner start. -/
theorem toExecutionSigma_start?
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (start? initialization storageAddress inputs fuel).map toExecutionSigma =
      (initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress).map fun context =>
          ⟨context,
            SelectedCheckedWordExecution.start context inputs fuel⟩ := by
  let erasedStart :
      (context : HostStorageDriver.Context
        RollbackState (FrameTrace Event)) →
        (Σ context : HostStorageDriver.Context
            RollbackState (FrameTrace Event),
          SelectedCheckedWordExecution context inputs) :=
    fun context =>
      ⟨context,
        SelectedCheckedWordExecution.start context inputs fuel⟩
  unfold start?
  split
  · rename_i refinedNone
    simpa [erasedStart, toExecutionSigma] using
      (congrArg (Option.map erasedStart) refinedNone).symm
  · rename_i context refinedSome
    simpa [erasedStart, toExecutionSigma] using
      (congrArg (Option.map erasedStart) refinedSome).symm

/-- The initial context and inner execution determine the provenance carrier. -/
@[ext] theorem ext
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    {left right : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs}
    (initialContext : left.initialContext = right.initialContext)
    (execution : HEq left.execution right.execution) :
    left = right := by
  cases left
  cases right
  simp_all

/-- A returned carrier is exact iff its inner value is the canonical start. -/
theorem start?_eq_some_iff
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    start? initialization storageAddress inputs fuel = some entry ↔
      entry.execution =
        SelectedCheckedWordExecution.start
          entry.initialContext inputs fuel := by
  constructor
  · intro started
    cases entry with
    | mk context refined execution =>
        rw [start?_of_present initialization storageAddress inputs fuel
          context refined] at started
        have entryEq := Option.some.inj started
        cases entryEq
        rfl
  · intro executionEq
    cases entry with
    | mk context refined execution =>
        rw [start?_of_present initialization storageAddress inputs fuel
          context refined]
        simp only [Option.some.injEq]
        apply ext
        · rfl
        · exact heq_of_eq executionEq.symm

/-- Every provenance carrier is the canonical start at its inner total fuel. -/
theorem start?_canonical
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    start? initialization storageAddress inputs
        entry.execution.providedFuel =
      some entry := by
  apply (start?_eq_some_iff initialization storageAddress inputs
    entry.execution.providedFuel entry).2
  exact SelectedCheckedWordExecution.eq_start entry.execution

/-- The retained context contains exactly the initialization's frame values. -/
theorem initialContext_values
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.values =
      initialization.toCheckpointedWorkingPair := by
  cases entry with
  | mk context refined execution =>
      unfold ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        at refined
      unfold FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?
        at refined
      split at refined
      · contradiction
      · have contextEq := Option.some.inj refined
        cases contextEq
        rfl

/-- The retained initial selector is the requested storage Address. -/
theorem initialContext_storageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.storageAddress = storageAddress := by
  cases entry with
  | mk context refined execution =>
      unfold ParentIndexedFrameInitialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        at refined
      unfold FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?
        at refined
      split at refined
      · contradiction
      · have contextEq := Option.some.inj refined
        cases contextEq
        rfl

/-- Inner code selection observes exactly the initialization's working world. -/
theorem selection_eq_initialWorld
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.execution.selection =
      initialization.initialWorld.selectWordCode inputs.codeAddress := by
  rw [entry.execution.selection_eq, entry.initialContext_values]
  rfl

/-- The initial checkpoint is exactly the indexed parent working pair. -/
theorem initialContext_checkpoint
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.values.checkpoint =
      FrameCheckpointSnapshot.fromWorkingPair parentWorking := by
  rw [entry.initialContext_values,
    ParentIndexedFrameInitialization.toCheckpointedWorkingPair_eq]

/-- Initial working effects retain the supplied rollback and parent trace. -/
theorem initialContext_workingEffects
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    entry.initialContext.context.values.working.2 =
      ⟨initialization.workingRollback, parentWorking.2.trace⟩ := by
  rw [entry.initialContext_values,
    ParentIndexedFrameInitialization.toCheckpointedWorkingPair_eq]

end Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution
