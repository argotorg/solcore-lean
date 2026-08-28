import Solcore.Semantics.FrameOutcome

/-! Caller-supplied pure mapping of frame trap-reason types. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameOutcome

universe u v

/-- Preserve halt kind and byte payload while mapping only trapped reasons. -/
def mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (outcome : FrameOutcome TrapReason) :
    FrameOutcome MappedTrapReason :=
  match outcome with
  | .returned data => .returned data
  | .reverted data => .reverted data
  | .trapped reason => .trapped (mapReason reason)

end Solcore.Semantics.FrameOutcome
