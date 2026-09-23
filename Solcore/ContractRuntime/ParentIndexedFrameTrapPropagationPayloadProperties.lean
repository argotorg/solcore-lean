import Solcore.ContractRuntime.ParentIndexedFrameTrapPropagationPayload
import Solcore.ContractRuntime.ParentIndexedFrameTrapRollbackProperties

/-! Outcome laws for parent-indexed trap propagation payload selection. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

theorem trapPropagationPayload?_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.trapPropagationPayload? = none := by
  unfold trapPropagationPayload?
  rw [context.trapRollback?_returned data outcomeEq]
  rfl

theorem trapPropagationPayload?_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.trapPropagationPayload? = none := by
  unfold trapPropagationPayload?
  rw [context.trapRollback?_reverted data outcomeEq]
  rfl

theorem trapPropagationPayload?_trapped
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason) :
    context.trapPropagationPayload? =
      some
        (⟨parentWorking.1, FrameOutcome.trapped reason⟩,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) := by
  unfold trapPropagationPayload?
  rw [context.trapRollback?_trapped reason outcomeEq, outcomeEq]
  rfl

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
