import Solcore.ContractRuntime.FrameContinuationContextFromCheckpointedWorkingPair
import Solcore.ContractRuntime.HostDriver
import Solcore.ContractRuntime.HostStorageContext
import Solcore.ContractRuntime.ParentIndexedFrameContinuationConstruction
import Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-! Branch-complete results for parent-indexed selected execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

/--
Every branch of parent-indexed selected execution. Exhaustion and fault retain
the exact driver state; completion also retains its canonical parent context.
-/
inductive ParentIndexedSelectedExecutionResult
    (RollbackState : Type u) (Event : Type v) (TrapReason : Type w)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) where
  | storageAbsent
  | codeAbsent
  | outOfFuel
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (state : Core.State)
  | fault
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (error : Core.MachineFault)
      (state : Core.State)
  | unsupported
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (suspension : Core.HostSuspension)
      (remainingFuel : Nat)
  | completed
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (value : Core.Value)
      (store : Core.Store)
      (continuation : ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)

namespace ParentIndexedSelectedExecutionResult

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Short name for a result at one fixed parent working pair. -/
abbrev Result
    (RollbackState : Type u) (Event : Type v) (TrapReason : Type w)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) :=
  ParentIndexedSelectedExecutionResult
    RollbackState Event TrapReason parentWorking

/-- Canonical completed parent context built from an exact driver result. -/
def completedContinuation
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store) :
    ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking :=
  ParentIndexedFrameContinuationContext.fromTraceExtension
    parentWorking initialization.workingRollback
    initialization.initialTraceExtension
    (FrameContinuationContext.fromCheckpointedWorkingPair
      context.context.values (doneOutcome context value store)).result

/-- Classify every terminal shape of an exact handled-driver result. -/
def classify
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (result : HostDriverResult
      (HostStorageDriver.Context RollbackState (FrameTrace Event))) :
    Result RollbackState Event TrapReason parentWorking :=
  match result with
  | ⟨context, .done value store⟩ =>
      .completed context value store
        (completedContinuation initialization doneOutcome context value store)
  | ⟨context, .outOfFuel state⟩ => .outOfFuel context state
  | ⟨context, .fault error state⟩ => .fault context error state
  | ⟨context, .unsupported suspension remainingFuel⟩ =>
      .unsupported context suspension remainingFuel

@[simp] theorem classify_done
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store) :
    classify initialization doneOutcome ⟨context, .done value store⟩ =
      .completed context value store
        (completedContinuation initialization doneOutcome context value store) :=
  rfl

@[simp] theorem classify_outOfFuel
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State) :
    classify initialization doneOutcome ⟨context, .outOfFuel state⟩ =
      .outOfFuel context state :=
  rfl

@[simp] theorem classify_fault
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (error : Core.MachineFault)
    (state : Core.State) :
    classify initialization doneOutcome ⟨context, .fault error state⟩ =
      .fault context error state :=
  rfl

@[simp] theorem classify_unsupported
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    classify initialization doneOutcome
        ⟨context, .unsupported suspension remainingFuel⟩ =
      .unsupported context suspension remainingFuel :=
  rfl

end ParentIndexedSelectedExecutionResult

end Solcore.ContractRuntime
