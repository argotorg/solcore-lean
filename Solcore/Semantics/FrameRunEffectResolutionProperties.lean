import Solcore.Semantics.FrameRunEffectResolution

/-! Laws for synchronized frame state and effect resolution. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameRunResult

universe u v w

@[simp] theorem resolvedWorldStateAndEffects?_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) =
      some (workingWorld, effectWorking) := by
  rfl

set_option doc.verso true in
/-- Revert selects the checkpoint world and rollback journal together, while
retaining the working trace component. This keeps speculative logs from being
committed alongside restored state. A trace can retain attempted work without
making it a committed contract effect.
-/
@[simp] theorem resolvedWorldStateAndEffects?_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) =
      some (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩) := by
  rfl

@[simp] theorem resolvedWorldStateAndEffects?_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.trapped reason⟩ : FrameRunResult TrapReason) =
      none := by
  rfl

theorem resolvedWorldStateAndEffects?_worldState
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option.map Prod.fst
      (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint
        effectWorking result) =
      result.resolvedWorldState? stateCheckpoint := by
  cases result with
  | mk working outcome => cases outcome <;> rfl

theorem resolvedWorldStateAndEffects?_effects
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option.map Prod.snd
      (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint
        effectWorking result) =
      FrameEffectJournal.resolved? effectCheckpoint effectWorking result.outcome := by
  cases result with
  | mk working outcome => cases outcome <;> rfl

end Solcore.Semantics.FrameRunResult
