import Solcore.ContractRuntime.FrameRunContinuation

/-! Constructor laws for caller-owned frame continuation. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w x

@[simp] theorem continueWithResolvedStateAndEffects?_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    continueWithResolvedStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) next =
      next (workingWorld, effectWorking) := by
  rfl

@[simp] theorem continueWithResolvedStateAndEffects?_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    continueWithResolvedStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) next =
      next (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩) := by
  rfl

@[simp] theorem continueWithResolvedStateAndEffects?_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    continueWithResolvedStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.trapped reason⟩ :
        FrameRunResult TrapReason) next = none := by
  rfl

end Solcore.ContractRuntime.FrameRunResult
