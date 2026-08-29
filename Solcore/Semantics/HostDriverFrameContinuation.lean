import Solcore.Semantics.HostDriver
import Solcore.Semantics.FrameContinuationContextFromCheckpointedWorkingPair

/-! Partial frame-continuation construction from completed handled execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostDriverResult

universe u v w x

/--
Build continuation inputs only for a completed handled run. The caller owns
both the terminal-context projection and the interpretation of Core's final
value and local store as a frame outcome.
-/
def toFrameContinuationContext?
    {Context : Type x}
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (result : HostDriverResult Context)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option (FrameContinuationContext RollbackState TraceState TrapReason) :=
  match result.outcome with
  | .done value store =>
      some (FrameContinuationContext.fromCheckpointedWorkingPair
        (values result.context)
        (doneOutcome result.context value store))
  | .outOfFuel _ => none
  | .fault _ _ => none

end Solcore.Semantics.HostDriverResult
