import Solcore.Semantics.FrameResolutionResult
import Solcore.Semantics.ParentIndexedFrameTrapRollback

/-! Read-only pairing of parent-indexed resolution and trap rollback selection. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

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

end Solcore.Semantics.ParentIndexedFrameContinuationContext
