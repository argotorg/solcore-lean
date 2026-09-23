import Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-! Opt-in frame-local rollback selection for parent-indexed traps. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

/-- Select checkpoint state and rollback with the working trace only on trap. -/
def trapRollback?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    Option
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) :=
  match context.result.outcome with
  | .returned _ => none
  | .reverted _ => none
  | .trapped _ =>
      some
        (context.stateCheckpoint,
          ⟨context.effectCheckpoint.rollback,
            context.effectWorking.trace⟩)

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
