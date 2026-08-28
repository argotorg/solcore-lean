import Solcore.Semantics.FrameRunEffectResolution

/-! Nested composition laws for synchronized frame state and effects. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameRunResult

universe u v w

theorem resolvedWorldStateAndEffects?_child_return_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentStateCheckpoint childStateCheckpoint childStateWorking : WorldState)
    (parentEffectCheckpoint childEffectCheckpoint childEffectWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolvedWorldStateAndEffects?
      childStateCheckpoint childEffectCheckpoint childEffectWorking
      (⟨childStateWorking, FrameOutcome.returned
        (TrapReason := TrapReason) childData⟩ : FrameRunResult TrapReason)).bind
        (fun childResolved => resolvedWorldStateAndEffects?
          parentStateCheckpoint parentEffectCheckpoint childResolved.2
          (⟨childResolved.1, FrameOutcome.reverted
            (TrapReason := TrapReason) parentData⟩ : FrameRunResult TrapReason)) =
      some (parentStateCheckpoint,
        ⟨parentEffectCheckpoint.rollback, childEffectWorking.trace⟩) := by
  rfl

theorem resolvedWorldStateAndEffects?_child_revert_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentStateCheckpoint childStateCheckpoint childStateWorking : WorldState)
    (parentEffectCheckpoint childEffectCheckpoint childEffectWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolvedWorldStateAndEffects?
      childStateCheckpoint childEffectCheckpoint childEffectWorking
      (⟨childStateWorking, FrameOutcome.reverted
        (TrapReason := TrapReason) childData⟩ : FrameRunResult TrapReason)).bind
        (fun childResolved => resolvedWorldStateAndEffects?
          parentStateCheckpoint parentEffectCheckpoint childResolved.2
          (⟨childResolved.1, FrameOutcome.reverted
            (TrapReason := TrapReason) parentData⟩ : FrameRunResult TrapReason)) =
      some (parentStateCheckpoint,
        ⟨parentEffectCheckpoint.rollback, childEffectWorking.trace⟩) := by
  rfl

end Solcore.Semantics.FrameRunResult
