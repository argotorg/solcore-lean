import Solcore.ContractRuntime.HostStorageDriverFuelProperties
import Solcore.ContractRuntime.ParentIndexedFrameInitializationSelectedExecutionProperties
import Solcore.ContractRuntime.ParentIndexedSelectedExecutionResumptionProperties

/-! Split and summed-budget laws for actual parent-indexed selected runs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

open ParentIndexedSelectedExecutionResult

/-- Resuming an actual selected run is exactly one run at summed fuel. -/
theorem runCodeWithStorageParentIndexedResult_resumeWithFuel
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome additional =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs (fuel + additional) doneOutcome := by
  unfold runCodeWithStorageParentIndexedResult
  cases refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => rfl
  | some context =>
      cases selected : context.context.values.working.1.code?
          inputs.codeAddress with
      | none =>
          simp [FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?,
            selected]
      | some code =>
          simp only [FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?,
            selected, Option.map_some]
          rw [ParentIndexedSelectedExecutionResult.resumeWithFuel_classify]
          rw [CheckedHostCoreProgram.runWithStorage_resumeWithFuel]

/-- Zero additional fuel is an identity for every actual selected run. -/
@[simp] theorem runCodeWithStorageParentIndexedResult_resumeWithFuel_zero
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
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome 0 =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome := by
  simpa using runCodeWithStorageParentIndexedResult_resumeWithFuel
    initialization storageAddress inputs fuel 0 doneOutcome

/-- Two additions after an actual run retain its selector and exact policy. -/
theorem runCodeWithStorageParentIndexedResult_resumeWithFuel_add
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel first second : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    ((initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs fuel doneOutcome).resumeWithFuel
          initialization inputs doneOutcome first).resumeWithFuel
        initialization inputs doneOutcome second =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs (fuel + (first + second)) doneOutcome := by
  rw [ParentIndexedSelectedExecutionResult.resumeWithFuel_add]
  exact runCodeWithStorageParentIndexedResult_resumeWithFuel
    initialization storageAddress inputs fuel (first + second) doneOutcome

/-- Resuming an actual checked selected run cannot expose a raw fault. -/
theorem runCodeWithStorageParentIndexedResult_resumeWithFuel_ne_fault
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    (initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs fuel doneOutcome).resumeWithFuel
        initialization inputs doneOutcome additional ≠
      .fault finalContext error state := by
  rw [runCodeWithStorageParentIndexedResult_resumeWithFuel]
  exact runCodeWithStorageParentIndexedResult_ne_fault
    initialization storageAddress inputs (fuel + additional) doneOutcome
      finalContext error state

end Solcore.ContractRuntime.ParentIndexedFrameInitialization
