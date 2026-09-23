import Solcore.ContractRuntime.FrameOutcome
import Solcore.ContractRuntime.WorldState

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

namespace FrameOutcome

/-- Resolve return and revert states while leaving trap disposition open. -/
def resolvedWorldState?
    {TrapReason : Type u}
    (checkpoint working : WorldState)
    (outcome : FrameOutcome TrapReason) : Option WorldState :=
  match outcome with
  | .returned _ => some working
  | .reverted _ => some checkpoint
  | .trapped _ => none

end FrameOutcome

end Solcore.ContractRuntime
