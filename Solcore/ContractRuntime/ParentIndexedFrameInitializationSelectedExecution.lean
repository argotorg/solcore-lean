import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecution
import Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccount
import Solcore.ContractRuntime.ParentIndexedSelectedExecutionResult

/-! Total parent-indexed selection into the branch-complete result. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

open ParentIndexedSelectedExecutionResult

/--
Refine storage, select code, and retain every handled execution branch.
-/
def runCodeWithStorageParentIndexedResult
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
    ParentIndexedSelectedExecutionResult
      RollbackState Event TrapReason parentWorking :=
  match initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress with
  | none => .storageAbsent
  | some context =>
      match context.runCodeWithStorage? inputs fuel with
      | none => .codeAbsent
      | some result => classify initialization doneOutcome result

end Solcore.ContractRuntime.ParentIndexedFrameInitialization
