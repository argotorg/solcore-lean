import Solcore.Semantics.FrameOutcome
import Solcore.Semantics.WorldState

set_option autoImplicit false

namespace Solcore.Semantics

universe u

namespace FrameOutcome

set_option doc.verso true in
/-- Resolve a frame's return to the working world and its revert to the
checkpoint. A trap yields {lean}`none`: this generic helper leaves trap
disposition to its caller.

That open trap disposition must not be confused with the root execution policy,
which selects rollback on trap. The checkpoint and working world are explicit
inputs; selecting one does not imply the other was never computed.
-/
def resolvedWorldState?
    {TrapReason : Type u}
    (checkpoint working : WorldState)
    (outcome : FrameOutcome TrapReason) : Option WorldState :=
  match outcome with
  | .returned _ => some working
  | .reverted _ => some checkpoint
  | .trapped _ => none

end FrameOutcome

end Solcore.Semantics
