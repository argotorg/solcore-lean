import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionProperties
import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccountProperties
import Solcore.Semantics.ParentIndexedFrameInitializationSelectedExecution

/-! Exact branch laws for branch-complete parent-indexed execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v w

open ParentIndexedSelectedExecutionResult

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

@[simp] theorem runCodeWithStorageParentIndexedResult_eq_storageAbsent_iff
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome = .storageAbsent ↔
      initialization.initialWorld.account? storageAddress = none := by
  cases observed : initialization.initialWorld.account? storageAddress with
  | none =>
      unfold runCodeWithStorageParentIndexedResult
      rw [toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
        initialization storageAddress observed]
      simp
  | some account =>
      unfold runCodeWithStorageParentIndexedResult
      rw [toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
        initialization storageAddress account observed]
      simp only
      let context : HostStorageDriver.Context
          RollbackState (FrameTrace Event) :=
        ⟨initialization.toCheckpointedWorkingPairWithStorageAddress
            storageAddress,
          account,
          observed⟩
      cases execution : context.runCodeWithStorage? inputs fuel with
      | none => simp
      | some result =>
          cases result with
          | mk finalContext outcome => cases outcome <;> simp [classify]

theorem runCodeWithStorageParentIndexedResult_eq_codeAbsent_iff
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome = .codeAbsent ↔
      ∃ context,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.context.values.working.1.code? inputs.codeAddress = none := by
  unfold runCodeWithStorageParentIndexedResult
  cases refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => simp
  | some context =>
      simp only
      cases execution : context.runCodeWithStorage? inputs fuel with
      | none =>
          have codeAbsent :=
            (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_eq_none_iff
              context inputs fuel).mp execution
          simp [codeAbsent]
      | some result =>
          have codePresent :
              context.context.values.working.1.code? inputs.codeAddress ≠ none := by
            intro codeAbsent
            have absentRun :=
              (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_eq_none_iff
                context inputs fuel).mpr codeAbsent
            rw [execution] at absentRun
            contradiction
          cases result with
          | mk finalContext outcome =>
              cases outcome <;> simp [classify, codePresent]

theorem runCodeWithStorageParentIndexedResult_eq_outOfFuel_iff
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome =
      .outOfFuel finalContext state ↔
    ∃ context,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .outOfFuel state⟩ := by
  unfold runCodeWithStorageParentIndexedResult
  cases refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => simp
  | some context =>
      simp only
      cases execution : context.runCodeWithStorage? inputs fuel with
      | none => simp [execution]
      | some result =>
          cases result with
          | mk resultContext outcome =>
              cases outcome <;> simp [classify, execution, eq_comm]

theorem runCodeWithStorageParentIndexedResult_eq_fault_iff
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome =
      .fault finalContext error state ↔
    ∃ context,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .fault error state⟩ := by
  unfold runCodeWithStorageParentIndexedResult
  cases refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => simp
  | some context =>
      simp only
      cases execution : context.runCodeWithStorage? inputs fuel with
      | none => simp [execution]
      | some result =>
          cases result with
          | mk resultContext outcome =>
              cases outcome <;> simp [classify, execution]

theorem runCodeWithStorageParentIndexedResult_eq_completed_iff
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome =
      .completed finalContext value store continuation ↔
    ∃ context,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorage? inputs fuel =
        some ⟨finalContext, .done value store⟩ ∧
      continuation = completedContinuation
        initialization doneOutcome finalContext value store := by
  unfold runCodeWithStorageParentIndexedResult
  cases refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => simp
  | some context =>
      simp only
      cases execution : context.runCodeWithStorage? inputs fuel with
      | none => simp [execution]
      | some result =>
          cases result with
          | mk resultContext outcome =>
              cases outcome with
              | done resultValue resultStore =>
                  simp [classify, execution, eq_comm, and_assoc]
                  intro contextEq valueEq storeEq
                  cases contextEq
                  cases valueEq
                  cases storeEq
                  rfl
              | outOfFuel state => simp [classify, execution]
              | fault error state => simp [classify, execution]

theorem runCodeWithStorageParentIndexedResult_ne_fault
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome ≠
      .fault finalContext error state := by
  intro fault
  obtain ⟨context, _refined, execution⟩ :=
    (runCodeWithStorageParentIndexedResult_eq_fault_iff
      initialization storageAddress inputs fuel doneOutcome
      finalContext error state).mp fault
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_ne_some_fault
      context inputs fuel finalContext error state execution

end Solcore.Semantics.ParentIndexedFrameInitialization
