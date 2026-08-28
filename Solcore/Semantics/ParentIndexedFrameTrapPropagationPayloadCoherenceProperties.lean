import Solcore.Semantics.ParentIndexedFrameTrapPropagationPayloadProperties
import Solcore.Semantics.ParentIndexedFrameContinuationContextProperties

/-! Coherence laws for successfully selected trap propagation payloads. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

theorem trapPropagationPayload?_eq_some_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (payload :
      FrameRunResult TrapReason ×
        FrameEffectJournal RollbackState (FrameTrace Event)) :
    context.trapPropagationPayload? = some payload ↔
      ∃ reason,
        context.result.outcome = FrameOutcome.trapped reason ∧
        payload =
          (⟨parentWorking.1, FrameOutcome.trapped reason⟩,
            ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) := by
  constructor
  · intro payloadEq
    cases outcomeEq : context.result.outcome with
    | returned data =>
        rw [context.trapPropagationPayload?_returned data outcomeEq] at payloadEq
        contradiction
    | reverted data =>
        rw [context.trapPropagationPayload?_reverted data outcomeEq] at payloadEq
        contradiction
    | trapped reason =>
        rw [context.trapPropagationPayload?_trapped reason outcomeEq] at payloadEq
        exact ⟨reason, rfl, Option.some.inj payloadEq.symm⟩
  · rintro ⟨reason, outcomeEq, rfl⟩
    exact context.trapPropagationPayload?_trapped reason outcomeEq

theorem trapPropagationPayload?_some_tracePrefix
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (payload :
      FrameRunResult TrapReason ×
        FrameEffectJournal RollbackState (FrameTrace Event))
    (payloadEq : context.trapPropagationPayload? = some payload) :
    FrameTrace.IsPrefixOf parentWorking.2.trace payload.2.trace := by
  obtain ⟨reason, outcomeEq, payloadExact⟩ :=
    (context.trapPropagationPayload?_eq_some_iff payload).mp payloadEq
  subst payload
  exact context.parentWorking_tracePrefix

end Solcore.Semantics.ParentIndexedFrameContinuationContext
