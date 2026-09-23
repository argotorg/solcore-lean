import Solcore.ContractRuntime.FrameRunResult
import Solcore.ContractRuntime.FrameEffectJournal

/-! Synchronized resolution of one frame's WorldState and effect journal. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w

/-- Resolve state and effects from the same outcome without choosing trap policy. -/
def resolvedWorldStateAndEffects?
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option (WorldState × FrameEffectJournal RollbackState TraceState) :=
  match result.outcome with
  | .returned _ => some (result.working, effectWorking)
  | .reverted _ =>
      some (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩)
  | .trapped _ => none

end Solcore.ContractRuntime.FrameRunResult
