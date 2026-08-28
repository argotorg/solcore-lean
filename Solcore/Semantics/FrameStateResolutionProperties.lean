import Solcore.Semantics.FrameStateResolution

set_option autoImplicit false

namespace Solcore.Semantics.FrameOutcome

universe u

@[simp] theorem resolvedWorldState?_returned
    {TrapReason : Type u}
    (checkpoint working : WorldState)
    (data : Bytes) :
    resolvedWorldState? checkpoint working
      (FrameOutcome.returned (TrapReason := TrapReason) data) = some working := by
  rfl

@[simp] theorem resolvedWorldState?_reverted
    {TrapReason : Type u}
    (checkpoint working : WorldState)
    (data : Bytes) :
    resolvedWorldState? checkpoint working
      (FrameOutcome.reverted (TrapReason := TrapReason) data) = some checkpoint := by
  rfl

@[simp] theorem resolvedWorldState?_trapped
    {TrapReason : Type u}
    (checkpoint working : WorldState)
    (reason : TrapReason) :
    resolvedWorldState? checkpoint working (.trapped reason) = none := by
  rfl

end Solcore.Semantics.FrameOutcome
