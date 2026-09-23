import Solcore.ContractRuntime.FrameResolutionResult

/-! Caller-owned non-trapping continuation of total frame resolution results. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameResolutionResult

universe u v w x

/-- Continue a resolved return or revert with its synchronized pair and bytes. -/
def continue?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (result : FrameResolutionResult RollbackState TraceState TrapReason)
    (onReturned :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next)
    (onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    Option Next :=
  match result with
  | .returned state effects data => onReturned (state, effects) data
  | .reverted state effects data => onReverted (state, effects) data
  | .trapped _ => none

end Solcore.ContractRuntime.FrameResolutionResult
