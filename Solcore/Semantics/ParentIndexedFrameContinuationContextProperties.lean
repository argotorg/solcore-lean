import Solcore.Semantics.ParentIndexedFrameContinuationContext

/-! Parent-indexed trace and resolution laws for completed frame contexts. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

/-- The indexed parent trace prefixes the completed context's working trace. -/
theorem parentWorking_tracePrefix
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    FrameTrace.IsPrefixOf
      parentWorking.2.trace context.effectWorking.trace := by
  have effectCheckpointEq : context.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd context.checkpoint_eq_parentWorking
  simpa only [effectCheckpointEq] using context.tracePrefix

/-- A returned outcome resolves to the completed context's working pair. -/
theorem resolve_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.resolve = FrameResolutionResult.returned
      context.result.working context.effectWorking data ∧
    FrameTrace.IsPrefixOf
      parentWorking.2.trace context.effectWorking.trace := by
  constructor
  · unfold FrameContinuationContext.resolve
    rw [outcomeEq]
  · exact context.parentWorking_tracePrefix

/-- A reverted outcome restores the indexed parent state and rollback component. -/
theorem resolve_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.resolve = FrameResolutionResult.reverted parentWorking.1
      ⟨parentWorking.2.rollback, context.effectWorking.trace⟩ data ∧
    FrameTrace.IsPrefixOf
      parentWorking.2.trace context.effectWorking.trace := by
  have stateCheckpointEq : context.stateCheckpoint = parentWorking.1 :=
    congrArg Prod.fst context.checkpoint_eq_parentWorking
  have effectCheckpointEq : context.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd context.checkpoint_eq_parentWorking
  constructor
  · unfold FrameContinuationContext.resolve
    rw [outcomeEq, stateCheckpointEq, effectCheckpointEq]
  · exact context.parentWorking_tracePrefix

end Solcore.Semantics.ParentIndexedFrameContinuationContext
