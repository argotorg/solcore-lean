import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionWithInputsPreservationProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionWithInputsProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuationWithInputs
import Solcore.Semantics.HostDriverFrameContinuationProperties

/-! Completion laws for explicit-input selected frame construction. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v w

namespace CheckedHostCoreProgram

theorem runWithStorageInputs_toFrameContinuationContext?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    (code.runWithStorageInputs context inputs fuel).toFrameContinuationContext?
          (fun current => current.context.values) doneOutcome = none ↔
      ∃ finalContext exhausted,
        code.runWithStorageInputs context inputs fuel =
          ⟨finalContext, .outOfFuel exhausted⟩ := by
  cases execution : code.runWithStorageInputs context inputs fuel with
  | mk finalContext outcome =>
      cases outcome with
      | done value store => simp
      | outOfFuel exhausted => simp
      | fault error faultState =>
          have contradiction :=
            code.runWithStorageInputs_ne_fault
              context inputs fuel error faultState
          rw [execution] at contradiction
          simp at contradiction

theorem runWithStorageInputs_toFrameContinuationContext?_some_stable
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {continuation :
      FrameContinuationContext RollbackState TraceState TrapReason}
    (completed :
      (code.runWithStorageInputs context inputs fuel).toFrameContinuationContext?
          (fun current => current.context.values) doneOutcome =
        some continuation)
    (more : fuel ≤ largerFuel) :
    (code.runWithStorageInputs context inputs largerFuel).toFrameContinuationContext?
        (fun current => current.context.values) doneOutcome =
      some continuation := by
  cases execution : code.runWithStorageInputs context inputs fuel with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          have stable :=
            code.runWithStorageInputs_done_stable
              context inputs execution more
          rw [stable]
          rw [execution] at completed
          exact completed
      | outOfFuel exhausted =>
          rw [execution] at completed
          simp at completed
      | fault error faultState =>
          rw [execution] at completed
          simp at completed

end CheckedHostCoreProgram

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

@[simp] theorem
    runCodeWithStorageContinuationContextWithInputs?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    context.runCodeWithStorageContinuationContextWithInputs?
          inputs fuel doneOutcome = none ↔
      context.context.values.working.1.code? inputs.codeAddress = none := by
  unfold runCodeWithStorageContinuationContextWithInputs?
  unfold runCodeWithStorageWithInputs?
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp only [Option.map_none]
  | some code => simp only [Option.map_some, reduceCtorEq]

theorem
    runCodeWithStorageContinuationContextWithInputs?_eq_some_none_iff
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    context.runCodeWithStorageContinuationContextWithInputs?
          inputs fuel doneOutcome = some none ↔
      ∃ resultContext exhausted,
        context.runCodeWithStorageWithInputs? inputs fuel =
          some ⟨resultContext, .outOfFuel exhausted⟩ := by
  unfold runCodeWithStorageContinuationContextWithInputs?
  cases execution : context.runCodeWithStorageWithInputs? inputs fuel with
  | none => simp
  | some result =>
      cases result with
      | mk resultContext outcome =>
          cases outcome with
          | done value store => simp
          | outOfFuel exhausted => simp
          | fault error faultState =>
              exact False.elim
                (runCodeWithStorageWithInputs?_ne_some_fault
                  context inputs fuel resultContext error faultState execution)

theorem
    runCodeWithStorageContinuationContextWithInputs?_some_some_stable
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {continuation :
      FrameContinuationContext RollbackState TraceState TrapReason}
    (completed :
      context.runCodeWithStorageContinuationContextWithInputs?
          inputs fuel doneOutcome = some (some continuation))
    (more : fuel ≤ largerFuel) :
    context.runCodeWithStorageContinuationContextWithInputs?
        inputs largerFuel doneOutcome = some (some continuation) := by
  unfold runCodeWithStorageContinuationContextWithInputs? at completed ⊢
  rw [Option.map_eq_some_iff] at completed
  obtain ⟨result, execution, resultCompleted⟩ := completed
  cases result with
  | mk resultContext outcome =>
      cases outcome with
      | done value store =>
          have stable :=
            runCodeWithStorageWithInputs?_some_done_stable
              context inputs execution more
          rw [stable]
          exact congrArg some resultCompleted
      | outOfFuel exhausted => simp at resultCompleted
      | fault error faultState =>
          exact False.elim
            (runCodeWithStorageWithInputs?_ne_some_fault
              context inputs fuel resultContext error faultState execution)

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
