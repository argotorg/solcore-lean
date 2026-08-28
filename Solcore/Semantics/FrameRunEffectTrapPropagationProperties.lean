import Solcore.Semantics.FrameRunEffectResolution

/-! Propagation of unresolved traps through synchronized frame continuations. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameRunResult

universe u v w x

/-- A trapped synchronized resolution cannot invoke or succeed through a continuation. -/
theorem resolvedWorldStateAndEffects?_trapped_bind
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.trapped reason⟩ :
        FrameRunResult TrapReason)).bind next = none := by
  rfl

end Solcore.Semantics.FrameRunResult
