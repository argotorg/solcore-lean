import Solcore.ContractRuntime.FrameResolutionResult
import Solcore.ContractRuntime.ParentIndexedFrameTrapRollback
import Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-! Read-only pairing of parent-indexed resolution and trap rollback selection. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

/--
Observe ordinary frame resolution together with the existing opt-in rollback
pair selected only for a trapped outcome.
-/
def resolveWithTrapRollback
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    FrameResolutionResult RollbackState (FrameTrace Event) TrapReason ×
      Option
        (WorldState ×
          FrameEffectJournal RollbackState (FrameTrace Event)) :=
  (context.resolve, context.trapRollback?)

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameResolutionViewProperties`
-/

/-! Exact branch laws for the parent-indexed resolution view. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

theorem resolveWithTrapRollback_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.resolveWithTrapRollback =
        (FrameResolutionResult.returned
          context.result.working context.effectWorking data, none) ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  have resolved := context.resolve_returned data outcomeEq
  constructor
  · unfold resolveWithTrapRollback
    rw [resolved.1, context.trapRollback?_returned data outcomeEq]
  · exact resolved.2

theorem resolveWithTrapRollback_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.resolveWithTrapRollback =
        (FrameResolutionResult.reverted parentWorking.1
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩ data,
          none) ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  have resolved := context.resolve_reverted data outcomeEq
  constructor
  · unfold resolveWithTrapRollback
    rw [resolved.1, context.trapRollback?_reverted data outcomeEq]
  · exact resolved.2

theorem resolveWithTrapRollback_trapped
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason) :
    context.resolveWithTrapRollback =
        (FrameResolutionResult.trapped reason,
          some
            (parentWorking.1,
              ⟨parentWorking.2.rollback, context.effectWorking.trace⟩)) ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  constructor
  · unfold resolveWithTrapRollback FrameContinuationContext.resolve
    rw [outcomeEq, context.trapRollback?_trapped reason outcomeEq]
  · exact context.parentWorking_tracePrefix

theorem resolveWithTrapRollback_snd_eq_some_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (values :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) :
    (context.resolveWithTrapRollback).2 = some values ↔
      ∃ reason,
        context.result.outcome = FrameOutcome.trapped reason ∧
          values =
            (parentWorking.1,
              ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) := by
  change context.trapRollback? = some values ↔ _
  constructor
  · intro selected
    cases outcomeEq : context.result.outcome with
    | returned data =>
        rw [context.trapRollback?_returned data outcomeEq] at selected
        contradiction
    | reverted data =>
        rw [context.trapRollback?_reverted data outcomeEq] at selected
        contradiction
    | trapped reason =>
        rw [context.trapRollback?_trapped reason outcomeEq] at selected
        exact ⟨reason, rfl, (Option.some.inj selected).symm⟩
  · rintro ⟨reason, outcomeEq, rfl⟩
    exact context.trapRollback?_trapped reason outcomeEq

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameResolutionViewTrapReasonMapProperties`
-/

/-! Naturality of trap-reason mapping under parent-indexed resolution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w x

/-- Reason mapping changes only the resolution component of the view. -/
@[simp] theorem resolveWithTrapRollback_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (context.mapTrapReason mapReason).resolveWithTrapRollback =
      (FrameResolutionResult.mapTrapReason mapReason
          (context.resolveWithTrapRollback).1,
        (context.resolveWithTrapRollback).2) := by
  apply Prod.ext
  · change
      (context.toFrameContinuationContext.mapTrapReason mapReason).resolve =
        FrameResolutionResult.mapTrapReason mapReason
          context.toFrameContinuationContext.resolve
    exact FrameContinuationContext.resolve_mapTrapReason
      mapReason context.toFrameContinuationContext
  · unfold resolveWithTrapRollback trapRollback?
    cases context with
    | mk context checkpointEq =>
        cases context with
        | mk context tracePrefix =>
            cases context with
            | mk stateCheckpoint effectCheckpoint effectWorking result =>
                cases result with
                | mk working outcome =>
                    cases outcome <;> rfl

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
