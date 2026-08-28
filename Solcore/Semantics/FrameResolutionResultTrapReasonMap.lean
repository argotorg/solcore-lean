import Solcore.Semantics.FrameResolutionResult

/-! Caller-supplied pure mapping of total frame-resolution trap reasons. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameResolutionResult

universe u v w x

/-- Preserve resolved return/revert data while mapping only trapped reasons. -/
def mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (result :
      FrameResolutionResult RollbackState TraceState TrapReason) :
    FrameResolutionResult RollbackState TraceState MappedTrapReason :=
  match result with
  | .returned state effects data => .returned state effects data
  | .reverted state effects data => .reverted state effects data
  | .trapped reason => .trapped (mapReason reason)

end Solcore.Semantics.FrameResolutionResult
