import Solcore.ContractRuntime.HostDriverFrameContinuation
import Solcore.ContractRuntime.FrameResolutionResult

/-! Exact branch, projection, and resolution laws for handled completion. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostDriverResult

universe u v w x

/-- A completed run retains its terminal context, value, and local store. -/
@[simp] theorem toFrameContinuationContext?_done
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    toFrameContinuationContext?
        (HostDriverResult.mk context (.done value store))
        values doneOutcome =
      some (FrameContinuationContext.fromCheckpointedWorkingPair
        (values context) (doneOutcome context value store)) := by
  rfl

/-- Exhausted execution does not yet supply a frame continuation. -/
@[simp] theorem toFrameContinuationContext?_outOfFuel
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (state : Core.State)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    toFrameContinuationContext?
        (HostDriverResult.mk context (.outOfFuel state))
        values doneOutcome = none := by
  rfl

/-- A raw Core fault receives no implicit frame-trap interpretation. -/
@[simp] theorem toFrameContinuationContext?_fault
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (error : Core.MachineFault)
    (state : Core.State)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    toFrameContinuationContext?
        (HostDriverResult.mk context (.fault error state))
        values doneOutcome = none := by
  rfl

/-- A policy-rejected request is not a completed frame. -/
@[simp] theorem toFrameContinuationContext?_unsupported
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    toFrameContinuationContext?
        (HostDriverResult.mk context
          (.unsupported suspension remainingFuel))
        values doneOutcome = none := by
  rfl

/-- Completed construction retains the terminal checkpoint state exactly. -/
@[simp] theorem stateCheckpoint_toFrameContinuationContext?_done
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option.map FrameContinuationContext.stateCheckpoint
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (values context).checkpoint.state := by
  rfl

/-- Completed construction retains the terminal checkpoint journal exactly. -/
@[simp] theorem effectCheckpoint_toFrameContinuationContext?_done
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option.map FrameContinuationContext.effectCheckpoint
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (values context).checkpoint.effects := by
  rfl

/-- Completed construction retains the terminal working journal exactly. -/
@[simp] theorem effectWorking_toFrameContinuationContext?_done
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option.map FrameContinuationContext.effectWorking
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (values context).working.2 := by
  rfl

/--
Completed construction pairs the terminal working world with the exact outcome
selected from the terminal context, Core value, and Core-local store.
-/
@[simp] theorem result_toFrameContinuationContext?_done
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option.map FrameContinuationContext.result
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (FrameRunResult.mk
        (values context).working.1
        (doneOutcome context value store)) := by
  rfl

/-- A caller-selected return resolves the terminal working values. -/
theorem resolve_toFrameContinuationContext?_done_returned
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason)
    (data : Bytes)
    (outcomeEq : doneOutcome context value store = .returned data) :
    Option.map FrameContinuationContext.resolve
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (FrameResolutionResult.returned
        (TrapReason := TrapReason)
        (values context).working.1 (values context).working.2 data) := by
  simp only [toFrameContinuationContext?_done, Option.map_some,
    FrameContinuationContext.resolve]
  rw [outcomeEq]
  rfl

/-- A caller-selected revert restores checkpoint state and rollback effects. -/
theorem resolve_toFrameContinuationContext?_done_reverted
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason)
    (data : Bytes)
    (outcomeEq : doneOutcome context value store = .reverted data) :
    Option.map FrameContinuationContext.resolve
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (FrameResolutionResult.reverted
        (TrapReason := TrapReason)
        (values context).checkpoint.state
        ⟨(values context).checkpoint.effects.rollback,
          (values context).working.2.trace⟩
        data) := by
  simp only [toFrameContinuationContext?_done, Option.map_some,
    FrameContinuationContext.resolve]
  rw [outcomeEq]
  rfl

/-- A caller-selected trap resolves without inventing state disposition. -/
theorem resolve_toFrameContinuationContext?_done_trapped
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : Context)
    (value : Core.Value)
    (store : Core.Store)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason)
    (reason : TrapReason)
    (outcomeEq : doneOutcome context value store = .trapped reason) :
    Option.map FrameContinuationContext.resolve
        (toFrameContinuationContext?
          (HostDriverResult.mk context (.done value store))
          values doneOutcome) =
      some (FrameResolutionResult.trapped
        (RollbackState := RollbackState) (TraceState := TraceState)
        reason) := by
  simp only [toFrameContinuationContext?_done, Option.map_some,
    FrameContinuationContext.resolve]
  rw [outcomeEq]
  rfl

end Solcore.ContractRuntime.HostDriverResult
