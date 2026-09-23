import Solcore.ContractRuntime.ParentIndexedFrameTrapRollback
import Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-! Opt-in trap propagation payloads for parent-indexed frame contexts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

/-- Select one prospective enclosing-boundary payload only on trap. -/
def trapPropagationPayload?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    Option
      (FrameRunResult TrapReason ×
        FrameEffectJournal RollbackState (FrameTrace Event)) :=
  context.trapRollback?.map fun (state, effects) =>
    (⟨state, context.result.outcome⟩, effects)

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameTrapPropagationPayloadProperties`
-/

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

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameTrapPropagationPayloadCoherenceProperties`
-/

/-! Coherence laws for successfully selected trap propagation payloads. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

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

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
