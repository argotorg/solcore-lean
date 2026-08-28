import Solcore.Semantics.FrameResolutionResultContinuation

/-! Coherence after erasing resolution-result branch and byte observations. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameContinuationContext

universe u v w x

/-- Bytes-erasing identical result callbacks recover context continuation. -/
theorem resolve_continue?_ignoreBranchAndBytes
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    context.resolve.continue?
        (fun selected _ => next selected)
        (fun selected _ => next selected) =
      context.continue? next := by
  cases context with
  | mk stateCheckpoint effectCheckpoint effectWorking result =>
      cases result with
      | mk working outcome =>
          cases outcome <;> rfl

end Solcore.Semantics.FrameContinuationContext
