import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccount
import Solcore.Semantics.SelectedCheckedWordExecution

/-! Parent-indexed storage provenance for selected checked Word execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

/--
A selected checked Word execution whose initial storage context is proven to
come from one exact parent initialization and storage Address.
-/
structure ParentIndexedSelectedCheckedWordExecution
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs) where
  initialContext :
    HostStorageDriver.Context RollbackState (FrameTrace Event)
  context_refined :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress =
      some initialContext
  execution : SelectedCheckedWordExecution initialContext inputs

namespace ParentIndexedSelectedCheckedWordExecution

/-- Erase only the named parent provenance wrapper to its dependent pair. -/
def toExecutionSigma
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    {initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking}
    {storageAddress : Address}
    {inputs : HostStorageDriver.ExecutionInputs}
    (entry : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs) :
    Σ context : HostStorageDriver.Context
        RollbackState (FrameTrace Event),
      SelectedCheckedWordExecution context inputs :=
  ⟨entry.initialContext, entry.execution⟩

/--
Refine storage once and start ADR-0143 in exactly the resulting present
context. Outer absence means only that the storage Account is absent.
-/
def start?
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    Option
      (ParentIndexedSelectedCheckedWordExecution
        initialization storageAddress inputs) :=
  match contextRefined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress with
  | none => none
  | some context =>
      some {
        initialContext := context
        context_refined := contextRefined
        execution := SelectedCheckedWordExecution.start context inputs fuel
      }

end ParentIndexedSelectedCheckedWordExecution

end Solcore.Semantics
