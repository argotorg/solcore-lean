import Solcore.ContractRuntime.FrameRunResult

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u

@[simp] theorem resolvedWorldState?_returned
    {TrapReason : Type u}
    (checkpoint working : WorldState) (data : Bytes) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .returned data⟩ : FrameRunResult TrapReason) =
      some working := by
  rfl

@[simp] theorem resolvedWorldState?_reverted
    {TrapReason : Type u}
    (checkpoint working : WorldState) (data : Bytes) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .reverted data⟩ : FrameRunResult TrapReason) =
      some checkpoint := by
  rfl

@[simp] theorem resolvedWorldState?_trapped
    {TrapReason : Type u}
    (checkpoint working : WorldState) (reason : TrapReason) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .trapped reason⟩ : FrameRunResult TrapReason) = none := by
  rfl

end Solcore.ContractRuntime.FrameRunResult
