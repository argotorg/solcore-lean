import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionWithInputsPreservationProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionWithInputsProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuationWithInputs
import Solcore.Semantics.HostDriverFrameContinuationProperties

/-! Completion laws for explicit-input selected frame construction. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v w

namespace CheckedHostCoreProgram

theorem runWithStorage_toFrameContinuationContext?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    (code.runWithStorage context inputs fuel).toFrameContinuationContext?
          (fun current => current.context.values) doneOutcome = none ↔
      ∃ finalContext exhausted,
        code.runWithStorage context inputs fuel =
          ⟨finalContext, .outOfFuel exhausted⟩ := by
  cases execution : code.runWithStorage context inputs fuel with
  | mk finalContext outcome =>
      cases outcome with
      | done value store => simp
      | outOfFuel exhausted => simp
      | fault error faultState =>
          have contradiction :=
            code.runWithStorage_ne_fault
              context inputs fuel error faultState
          rw [execution] at contradiction
          simp at contradiction

theorem runWithStorage_toFrameContinuationContext?_some_stable
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
      (code.runWithStorage context inputs fuel).toFrameContinuationContext?
          (fun current => current.context.values) doneOutcome =
        some continuation)
    (more : fuel ≤ largerFuel) :
    (code.runWithStorage context inputs largerFuel).toFrameContinuationContext?
        (fun current => current.context.values) doneOutcome =
      some continuation := by
  cases execution : code.runWithStorage context inputs fuel with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          have stable :=
            code.runWithStorage_done_stable
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
    runCodeWithStorageContinuationContext?_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = none ↔
      context.context.values.working.1.code? inputs.codeAddress = none := by
  unfold runCodeWithStorageContinuationContext?
  unfold runCodeWithStorage?
  cases selected :
      context.context.values.working.1.code? inputs.codeAddress with
  | none => simp only [Option.map_none]
  | some code => simp only [Option.map_some, reduceCtorEq]

theorem
    runCodeWithStorageContinuationContext?_eq_some_none_iff
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some none ↔
      ∃ resultContext exhausted,
        context.runCodeWithStorage? inputs fuel =
          some ⟨resultContext, .outOfFuel exhausted⟩ := by
  unfold runCodeWithStorageContinuationContext?
  cases execution : context.runCodeWithStorage? inputs fuel with
  | none => simp
  | some result =>
      cases result with
      | mk resultContext outcome =>
          cases outcome with
          | done value store => simp
          | outOfFuel exhausted => simp
          | fault error faultState =>
              exact False.elim
                (runCodeWithStorage?_ne_some_fault
                  context inputs fuel resultContext error faultState execution)

theorem
    runCodeWithStorageContinuationContext?_some_some_stable
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
      context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some (some continuation))
    (more : fuel ≤ largerFuel) :
    context.runCodeWithStorageContinuationContext?
        inputs largerFuel doneOutcome = some (some continuation) := by
  unfold runCodeWithStorageContinuationContext? at completed ⊢
  rw [Option.map_eq_some_iff] at completed
  obtain ⟨result, execution, resultCompleted⟩ := completed
  cases result with
  | mk resultContext outcome =>
      cases outcome with
      | done value store =>
          have stable :=
            runCodeWithStorage?_some_done_stable
              context inputs execution more
          rw [stable]
          exact congrArg some resultCompleted
      | outOfFuel exhausted => simp at resultCompleted
      | fault error faultState =>
          exact False.elim
            (runCodeWithStorage?_ne_some_fault
              context inputs fuel resultContext error faultState execution)

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
