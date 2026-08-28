import Solcore.Semantics.FrameResolutionResult

/-! Constructor laws for total frame resolution. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameContinuationContext

universe u v w

@[simp] theorem resolve_returned
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    (⟨stateCheckpoint, effectCheckpoint, effectWorking,
      ⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩⟩ :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      FrameResolutionResult.returned workingWorld effectWorking data := by
  rfl

@[simp] theorem resolve_reverted
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    (⟨stateCheckpoint, effectCheckpoint, effectWorking,
      ⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩⟩ :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      FrameResolutionResult.reverted stateCheckpoint
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩ data := by
  rfl

@[simp] theorem resolve_trapped
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason) :
    (⟨stateCheckpoint, effectCheckpoint, effectWorking,
      ⟨workingWorld, FrameOutcome.trapped reason⟩⟩ :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      FrameResolutionResult.trapped reason := by
  rfl

end Solcore.Semantics.FrameContinuationContext
