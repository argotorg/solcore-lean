import Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
import Solcore.ContractRuntime.ParentIndexedFrameResolutionView

/-! Caller-owned elimination of parent-indexed frame outcomes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

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

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameResolutionFoldProperties`
-/

/-! Exact branch and view-coherence laws for parent-indexed resolution folds. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w x

theorem foldResolutionWithTrapRollback_returned
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReturned (context.result.working, context.effectWorking) data := by
  unfold foldResolutionWithTrapRollback
  rw [outcomeEq]

theorem foldResolutionWithTrapRollback_reverted
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReverted
        (parentWorking.1,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) data := by
  have stateCheckpointEq : context.stateCheckpoint = parentWorking.1 :=
    congrArg Prod.fst context.checkpoint_eq_parentWorking
  have effectCheckpointEq : context.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd context.checkpoint_eq_parentWorking
  unfold foldResolutionWithTrapRollback
  rw [outcomeEq, stateCheckpointEq, effectCheckpointEq]

theorem foldResolutionWithTrapRollback_trapped
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onTrapped
        (parentWorking.1,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) reason := by
  have stateCheckpointEq : context.stateCheckpoint = parentWorking.1 :=
    congrArg Prod.fst context.checkpoint_eq_parentWorking
  have effectCheckpointEq : context.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd context.checkpoint_eq_parentWorking
  unfold foldResolutionWithTrapRollback
  rw [outcomeEq, stateCheckpointEq, effectCheckpointEq]

theorem foldResolutionWithTrapRollback_reconstructs_view
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    context.foldResolutionWithTrapRollback
        (fun values data =>
          (FrameResolutionResult.returned values.1 values.2 data, none))
        (fun values data =>
          (FrameResolutionResult.reverted values.1 values.2 data, none))
        (fun values reason =>
          (FrameResolutionResult.trapped reason, some values)) =
      context.resolveWithTrapRollback := by
  cases outcomeEq : context.result.outcome with
  | returned data =>
      rw [context.foldResolutionWithTrapRollback_returned data outcomeEq]
      exact (context.resolveWithTrapRollback_returned data outcomeEq).1.symm
  | reverted data =>
      rw [context.foldResolutionWithTrapRollback_reverted data outcomeEq]
      exact (context.resolveWithTrapRollback_reverted data outcomeEq).1.symm
  | trapped reason =>
      rw [context.foldResolutionWithTrapRollback_trapped reason outcomeEq]
      exact (context.resolveWithTrapRollback_trapped reason outcomeEq).1.symm

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameResolutionFoldTrapReasonMapProperties`
-/

/-! Naturality of trap-reason mapping under parent-indexed resolution folds. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w x y

/-- Reason mapping changes only the trap function observed by the fold. -/
@[simp] theorem foldResolutionWithTrapRollback_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        MappedTrapReason → Next) :
    (context.mapTrapReason mapReason).foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      context.foldResolutionWithTrapRollback
        onReturned onReverted
        (fun values reason => onTrapped values (mapReason reason)) := by
  unfold foldResolutionWithTrapRollback
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
