import Solcore.Semantics.ParentIndexedFrameInitializationSelectedExecution

/-! Certified configuration and result for one parent-indexed selected run. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v w

/--
One selected run together with the exact configuration and total fuel budget
that produced its retained branch-complete result.
-/
structure ParentIndexedSelectedExecutionSession
    (RollbackState : Type u) (Event : Type v) (TrapReason : Type w)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) where
  initialization : ParentIndexedFrameInitialization
    RollbackState Event parentWorking
  storageAddress : Address
  inputs : HostStorageDriver.ExecutionInputs
  doneOutcome :
    HostStorageDriver.Context RollbackState (FrameTrace Event) →
      Core.Value → Core.Store → FrameOutcome TrapReason
  providedFuel : Nat
  result : ParentIndexedSelectedExecutionResult
    RollbackState Event TrapReason parentWorking
  result_eq_run :
    result = initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs providedFuel doneOutcome

namespace ParentIndexedSelectedExecutionSession

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Short name for a session at one fixed parent working pair. -/
abbrev Session := ParentIndexedSelectedExecutionSession
  RollbackState Event TrapReason parentWorking

/-- Start one certified session from the existing branch-complete producer. -/
def start
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking := {
  initialization := initialization
  storageAddress := storageAddress
  inputs := inputs
  doneOutcome := doneOutcome
  providedFuel := providedFuel
  result := initialization.runCodeWithStorageParentIndexedResult
    storageAddress inputs providedFuel doneOutcome
  result_eq_run := rfl
}

@[simp] theorem start_initialization
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).initialization =
      initialization :=
  rfl

@[simp] theorem start_storageAddress
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).storageAddress =
      storageAddress :=
  rfl

@[simp] theorem start_inputs
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).inputs =
      inputs :=
  rfl

@[simp] theorem start_doneOutcome
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).doneOutcome =
      doneOutcome :=
  rfl

@[simp] theorem start_providedFuel
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).providedFuel =
      providedFuel :=
  rfl

@[simp] theorem start_result
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).result =
      initialization.runCodeWithStorageParentIndexedResult
        storageAddress inputs providedFuel doneOutcome :=
  rfl

end ParentIndexedSelectedExecutionSession

end Solcore.Semantics
