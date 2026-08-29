import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeExecutionProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountCodeFrameContinuation
import Solcore.Semantics.HostDriverFrameContinuationProperties

/-! Completion and optional-boundary laws for selected frame construction. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v w

namespace CheckedHostCoreProgram

/-- A checked handled run lacks continuation inputs exactly when fuel expires. -/
theorem runWithStorage_toFrameContinuationContext?_eq_none_iff
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    (code.runWithStorage context fuel).toFrameContinuationContext?
          (fun current => current.context.values) doneOutcome = none ↔
      ∃ finalContext exhausted,
        code.runWithStorage context fuel =
          ⟨finalContext, .outOfFuel exhausted⟩ := by
  cases execution : code.runWithStorage context fuel with
  | mk finalContext outcome =>
      cases outcome with
      | done value store => simp
      | outOfFuel exhausted => simp
      | fault error faultState =>
          have contradiction :=
            code.runWithStorage_ne_fault context fuel error faultState
          rw [execution] at contradiction
          simp at contradiction

/-- Completed continuation inputs are unchanged when supplied more fuel. -/
theorem runWithStorage_toFrameContinuationContext?_some_stable
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {continuation :
      FrameContinuationContext RollbackState TraceState TrapReason}
    (completed :
      (code.runWithStorage context fuel).toFrameContinuationContext?
          (fun current => current.context.values) doneOutcome =
        some continuation)
    (more : fuel ≤ largerFuel) :
    (code.runWithStorage context largerFuel).toFrameContinuationContext?
        (fun current => current.context.values) doneOutcome =
      some continuation := by
  cases execution : code.runWithStorage context fuel with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          have stable :=
            code.runWithStorage_done_stable context execution more
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

/-- The outer option fails exactly when the working WorldState has no code. -/
@[simp] theorem runCodeWithStorageContinuationContext?_eq_none_iff
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    context.runCodeWithStorageContinuationContext?
          codeAddress fuel doneOutcome = none ↔
      context.context.values.working.1.code? codeAddress = none := by
  unfold runCodeWithStorageContinuationContext?
  unfold runCodeWithStorage?
  cases selected :
      context.context.values.working.1.code? codeAddress with
  | none => simp only [Option.map_none]
  | some code => simp only [Option.map_some, reduceCtorEq]

/--
An inner failure means that code was selected but its checked run exhausted
fuel. It is distinct from outer code-selection failure.
-/
theorem runCodeWithStorageContinuationContext?_eq_some_none_iff
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    context.runCodeWithStorageContinuationContext?
          codeAddress fuel doneOutcome = some none ↔
      ∃ resultContext exhausted,
        context.runCodeWithStorage? codeAddress fuel =
          some ⟨resultContext, .outOfFuel exhausted⟩ := by
  unfold runCodeWithStorageContinuationContext?
  cases execution : context.runCodeWithStorage? codeAddress fuel with
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
                  context codeAddress fuel resultContext error faultState
                  execution)

/-- A selected completed continuation is stable under additional fuel. -/
theorem runCodeWithStorageContinuationContext?_some_some_stable
    {RollbackState : Type u}
    {TraceState : Type v}
    {TrapReason : Type w}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (codeAddress : Address)
    (doneOutcome :
      HostStorageDriver.Context RollbackState TraceState →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {continuation :
      FrameContinuationContext RollbackState TraceState TrapReason}
    (completed :
      context.runCodeWithStorageContinuationContext?
          codeAddress fuel doneOutcome = some (some continuation))
    (more : fuel ≤ largerFuel) :
    context.runCodeWithStorageContinuationContext?
        codeAddress largerFuel doneOutcome = some (some continuation) := by
  unfold runCodeWithStorageContinuationContext? at completed ⊢
  rw [Option.map_eq_some_iff] at completed
  obtain ⟨result, execution, resultCompleted⟩ := completed
  cases result with
  | mk resultContext outcome =>
      cases outcome with
      | done value store =>
          have stable :=
            runCodeWithStorage?_some_done_stable
              context codeAddress execution more
          rw [stable]
          exact congrArg some resultCompleted
      | outOfFuel exhausted => simp at resultCompleted
      | fault error faultState =>
          exact False.elim
            (runCodeWithStorage?_ne_some_fault
              context codeAddress fuel resultContext error faultState
              execution)

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
