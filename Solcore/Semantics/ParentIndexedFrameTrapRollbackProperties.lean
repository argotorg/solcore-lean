import Solcore.Semantics.ParentIndexedFrameTrapRollback

/-! Outcome laws for parent-indexed trapped-frame rollback selection. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

theorem trapRollback?_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.trapRollback? = none := by
  unfold trapRollback?
  rw [outcomeEq]

theorem trapRollback?_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.trapRollback? = none := by
  unfold trapRollback?
  rw [outcomeEq]

theorem trapRollback?_trapped
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason) :
    context.trapRollback? =
      some
        (parentWorking.1,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) := by
  have stateCheckpointEq : context.stateCheckpoint = parentWorking.1 :=
    congrArg Prod.fst context.checkpoint_eq_parentWorking
  have effectCheckpointEq : context.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd context.checkpoint_eq_parentWorking
  unfold trapRollback?
  rw [outcomeEq, stateCheckpointEq, effectCheckpointEq]

end Solcore.Semantics.ParentIndexedFrameContinuationContext
