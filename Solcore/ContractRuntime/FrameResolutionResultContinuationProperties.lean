import Solcore.ContractRuntime.FrameResolutionResultContinuation

/-! Constructor laws for bytes-aware frame resolution continuation. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameResolutionResult

universe u v w x

/-- A returned result selects the return callback with every carried value. -/
@[simp] theorem continue?_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (FrameResolutionResult.returned
      (TrapReason := TrapReason) state effects data).continue?
        onReturned onReverted = onReturned (state, effects) data := by
  rfl

/-- A reverted result selects the revert callback with every carried value. -/
@[simp] theorem continue?_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (FrameResolutionResult.reverted
      (TrapReason := TrapReason) state effects data).continue?
        onReturned onReverted = onReverted (state, effects) data := by
  rfl

/-- A trapped result leaves both non-trapping callbacks unselected. -/
@[simp] theorem continue?_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (reason : TrapReason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (FrameResolutionResult.trapped
      (RollbackState := RollbackState) (TraceState := TraceState) reason).continue?
        onReturned onReverted = (none : Option Next) := by
  rfl

end Solcore.ContractRuntime.FrameResolutionResult
