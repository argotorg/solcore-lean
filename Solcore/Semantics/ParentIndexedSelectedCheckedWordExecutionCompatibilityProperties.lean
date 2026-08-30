import Solcore.Semantics.ParentIndexedFrameInitializationSelectedExecutionProperties
import Solcore.Semantics.ParentIndexedSelectedCheckedWordExecutionContinuationCoherenceProperties

/-! Meaning-preserving branch-local coherence with generic selected execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution

universe u v w

/-- Outer storage absence agrees exactly with the generic parent producer. -/
theorem start?_eq_none_iff_legacy_storageAbsent
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    start? initialization storageAddress inputs fuel = none ↔
      initialization.runCodeWithStorageParentIndexedResult
          storageAddress inputs fuel doneOutcome =
        .storageAbsent := by
  rw [start?_eq_none_iff]
  exact
    (ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_storageAbsent_iff
      initialization storageAddress inputs fuel doneOutcome).symm

/-- Generic selected execution is absent exactly on this carrier's code branch. -/
theorem legacy_runCodeWithStorage?_eq_none_iff_codeAbsent
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (fuel : Nat) :
    entry.initialContext.runCodeWithStorage? inputs fuel = none ↔
      entry.execution.selection = .codeAbsent := by
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_eq_none_iff]
  rw [← entry.execution.selection_toCheckedCode?]
  cases entry.execution.selection <;> simp

/-- On the Word branch, the retained raw run is the generic selected run. -/
theorem execution?_map_snd_eq_legacy_runCodeWithStorage?_of_word
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (code : CheckedHostCoreWordProgram)
    (selected : entry.execution.selection = .word code) :
    entry.execution.execution?.map Prod.snd =
      entry.initialContext.runCodeWithStorage?
        inputs entry.execution.providedFuel := by
  rw [entry.execution.execution?_eq_some_of_word code selected]
  unfold FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?
  rw [← entry.execution.selection_toCheckedCode?, selected]
  rfl

/--
The old branch-complete producer agrees only when its completion policy returns
the exact canonical bytes for this exact completed Word.
-/
theorem legacy_parent_result_eq_completed_of_canonical_word
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : entry.execution.completion? = some completion)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (canonical :
      doneOutcome completion.context (.word completion.word)
          completion.store =
        .returned completion.returnData) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs entry.execution.providedFuel doneOutcome =
      .completed completion.context (.word completion.word) completion.store
        (entry.toReturnedContinuation completion completed) := by
  apply (ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_eq_completed_iff
    initialization storageAddress inputs entry.execution.providedFuel
    doneOutcome completion.context (.word completion.word) completion.store
    (entry.toReturnedContinuation completion completed)).mpr
  refine ⟨entry.initialContext, entry.context_refined, ?_, ?_⟩
  · obtain ⟨code, selected, exactRun⟩ :=
      (entry.execution.completion?_eq_some_iff_selected_run completion).mp
        completed
    unfold FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?
    rw [← entry.execution.selection_toCheckedCode?, selected]
    simpa only [CheckedHostCoreWordCodeSelection.toCheckedCode?_word,
      Option.map_some, CheckedHostCoreWordProgram.runWithStorage,
      WordReturnedFrameCompletion.toHostDriverResult] using
      congrArg some exactRun
  · unfold ParentIndexedSelectedExecutionResult.completedContinuation
    unfold toReturnedContinuation
    rw [canonical]
    rfl

end Solcore.Semantics.ParentIndexedSelectedCheckedWordExecution
