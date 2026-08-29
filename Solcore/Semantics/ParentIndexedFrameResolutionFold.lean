import Solcore.Semantics.ParentIndexedFrameContinuationContext

/-! Caller-owned elimination of parent-indexed frame outcomes. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w x

/-- Select one pure caller-owned function for a completed frame outcome. -/
def foldResolutionWithTrapRollback
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) : Next :=
  match context.result.outcome with
  | .returned data =>
      onReturned (context.result.working, context.effectWorking) data
  | .reverted data =>
      onReverted
        (context.stateCheckpoint,
          ⟨context.effectCheckpoint.rollback, context.effectWorking.trace⟩)
        data
  | .trapped reason =>
      onTrapped
        (context.stateCheckpoint,
          ⟨context.effectCheckpoint.rollback, context.effectWorking.trace⟩)
        reason

end Solcore.Semantics.ParentIndexedFrameContinuationContext
