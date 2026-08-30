import Solcore.Semantics.HostStorageDriverFuelProperties
import Solcore.Semantics.ParentIndexedSelectedExecutionResumption

/-! Algebra and exact inversion for branch-complete resumption. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedExecutionResult

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Classifying before or after generic resumption gives the same result. -/
theorem resumeWithFuel_classify
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (result : HostDriverResult
      (HostStorageDriver.Context RollbackState (FrameTrace Event)))
    (additional : Nat) :
    resumeWithFuel (classify initialization doneOutcome result)
        initialization inputs doneOutcome additional =
      classify initialization doneOutcome
        (result.resumeWithFuel
          (@HostStorageDriver.handler RollbackState (FrameTrace Event) inputs)
          additional) := by
  cases result with
  | mk context outcome => cases outcome <;> rfl

/-- Sequential additions associate under one fixed initialization and policy. -/
theorem resumeWithFuel_add
    (result : Result RollbackState Event TrapReason parentWorking)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (first second : Nat) :
    resumeWithFuel
        (resumeWithFuel result initialization inputs doneOutcome first)
        initialization inputs doneOutcome second =
      resumeWithFuel result initialization inputs doneOutcome
        (first + second) := by
  cases result with
  | storageAbsent => rfl
  | codeAbsent => rfl
  | fault context error state => rfl
  | completed context value store continuation => rfl
  | outOfFuel context state =>
      rw [resumeWithFuel, resumeWithFuel_classify]
      change classify initialization doneOutcome
          ((HostStorageDriver.run context inputs first state).resumeWithFuel
            (@HostStorageDriver.handler RollbackState (FrameTrace Event) inputs)
            second) =
        classify initialization doneOutcome
          (HostStorageDriver.run context inputs (first + second) state)
      rw [HostStorageDriver.resumeWithFuel_run]

/-- Exact completion inversion from one retained exhausted context and state. -/
theorem resumeWithFuel_outOfFuel_eq_completed_iff
    (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
    (state : Core.State)
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (additional : Nat)
    (finalContext :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (value : Core.Value)
    (store : Core.Store)
    (continuation : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    resumeWithFuel (.outOfFuel context state)
        initialization inputs doneOutcome additional =
      .completed finalContext value store continuation ↔
    HostStorageDriver.run context inputs additional state =
        ⟨finalContext, .done value store⟩ ∧
      continuation = completedContinuation
        initialization doneOutcome finalContext value store := by
  simp only [resumeWithFuel_outOfFuel]
  cases execution : HostStorageDriver.run context inputs additional state with
  | mk resultContext outcome =>
      cases outcome with
      | done resultValue resultStore =>
          simp [classify, eq_comm, and_assoc]
          intro contextEq valueEq storeEq
          cases contextEq
          cases valueEq
          cases storeEq
          rfl
      | outOfFuel exhausted => simp [classify]
      | fault error faultState => simp [classify]

end Solcore.Semantics.ParentIndexedSelectedExecutionResult
