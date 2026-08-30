import Solcore.Semantics.HostStorageDriver
import Solcore.Semantics.ParentIndexedSelectedExecutionResult

/-! Out-of-fuel-only resumption for branch-complete selected execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedExecutionResult

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/--
Continue only retained exhaustion. Unsupported requests remain suspended and
only accumulate offered fuel; they are never passed to the rejecting handler.
Absence, raw fault, and completion are terminal identities.
-/
def resumeWithFuel
    (result : Result RollbackState Event TrapReason parentWorking)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    Result RollbackState Event TrapReason parentWorking :=
  match result with
  | .outOfFuel context state =>
      classify initialization doneOutcome
        (HostStorageDriver.run context inputs additional state)
  | .unsupported context suspension remainingFuel =>
      .unsupported context suspension (remainingFuel + additional)
  | terminal => terminal

@[simp] theorem resumeWithFuel_storageAbsent
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.storageAbsent : Result
        RollbackState Event TrapReason parentWorking)
        initialization inputs doneOutcome additional = .storageAbsent :=
  rfl

@[simp] theorem resumeWithFuel_codeAbsent
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.codeAbsent : Result
        RollbackState Event TrapReason parentWorking)
        initialization inputs doneOutcome additional = .codeAbsent :=
  rfl

@[simp] theorem resumeWithFuel_outOfFuel
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.outOfFuel context state)
        initialization inputs doneOutcome additional =
      classify initialization doneOutcome
        (HostStorageDriver.run context inputs additional state) :=
  rfl

@[simp] theorem resumeWithFuel_fault
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.fault context error state)
        initialization inputs doneOutcome additional =
      .fault context error state :=
  rfl

@[simp] theorem resumeWithFuel_unsupported
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.unsupported context suspension remainingFuel)
        initialization inputs doneOutcome additional =
      .unsupported context suspension (remainingFuel + additional) :=
  rfl

@[simp] theorem resumeWithFuel_completed
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat) :
    resumeWithFuel (.completed context value store continuation)
        initialization inputs doneOutcome additional =
      .completed context value store continuation :=
  rfl

end Solcore.Semantics.ParentIndexedSelectedExecutionResult
