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

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameStateResolutionProperties`
-/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameOutcome

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

end Solcore.ContractRuntime.FrameOutcome
