import Solcore.ContractRuntime.FrameContinuationContext

/-! Total, first-order resolution of one completed frame. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

/-- The branch-complete result of resolving one completed frame. -/
inductive FrameResolutionResult
    (RollbackState : Type u) (TraceState : Type v)
    (TrapReason : Type w) : Type (max u v w) where
  | returned
      (state : WorldState)
      (effects : FrameEffectJournal RollbackState TraceState)
      (data : Bytes)
  | reverted
      (state : WorldState)
      (effects : FrameEffectJournal RollbackState TraceState)
      (data : Bytes)
  | trapped (reason : TrapReason)

namespace FrameContinuationContext

/-- Resolve every frame branch without selecting a continuation. -/
def resolve
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    FrameResolutionResult RollbackState TraceState TrapReason :=
  match context.result.outcome with
  | .returned data =>
      .returned context.result.working context.effectWorking data
  | .reverted data =>
      .reverted context.stateCheckpoint
        ⟨context.effectCheckpoint.rollback, context.effectWorking.trace⟩ data
  | .trapped reason => .trapped reason

end FrameContinuationContext

end Solcore.ContractRuntime
