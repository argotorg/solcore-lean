import Solcore.ContractRuntime.FrameResolutionResult
import Solcore.ContractRuntime.FrameContinuationContext

/-! Compile-only regressions for branch/byte erasure coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x y

private example
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
  exact FrameContinuationContext.resolve_continue?_ignoreBranchAndBytes
    context next

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    (context.mapTrapReason mapReason).resolve.continue?
        (fun selected _ => next selected)
        (fun selected _ => next selected) =
      context.continue? next := by
  rw [FrameContinuationContext.resolve_continue?_ignoreBranchAndBytes]
  exact FrameContinuationContext.continue?_mapTrapReason
    mapReason context next

end Tests
