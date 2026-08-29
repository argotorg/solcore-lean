import Solcore.Semantics.ParentIndexedFrameContinuationContextTrapReasonMap
import Solcore.Semantics.ParentIndexedFrameResolutionFold

/-! Naturality of trap-reason mapping under parent-indexed resolution folds. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

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

end Solcore.Semantics.ParentIndexedFrameContinuationContext
