import Solcore.Semantics.FrameStateResolution

/-! The minimal state-and-outcome payload produced by one frame run. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u

/-- A speculative working state paired with the frame outcome it produced. -/
structure FrameRunResult (TrapReason : Type u) : Type u where
  working : WorldState
  outcome : FrameOutcome TrapReason

namespace FrameRunResult

/-- Resolve a frame result against a checkpoint still owned by the caller. -/
def resolvedWorldState?
    {TrapReason : Type u}
    (checkpoint : WorldState)
    (result : FrameRunResult TrapReason) : Option WorldState :=
  FrameOutcome.resolvedWorldState?
    checkpoint result.working result.outcome

end FrameRunResult

end Solcore.Semantics
