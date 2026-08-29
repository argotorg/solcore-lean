import Solcore.Semantics.FrameContinuationContextResolveTrapReasonMapProperties
import Solcore.Semantics.ParentIndexedFrameContinuationContextTrapReasonMapProperties
import Solcore.Semantics.ParentIndexedFrameResolutionView

/-! Naturality of trap-reason mapping under parent-indexed resolution. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

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

end Solcore.Semantics.ParentIndexedFrameContinuationContext
