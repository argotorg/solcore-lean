import Solcore.Semantics.ParentIndexedFrameTrapRollback

/-! Opt-in trap propagation payloads for parent-indexed frame contexts. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

/-- Select one prospective enclosing-boundary payload only on trap. -/
def trapPropagationPayload?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    Option
      (FrameRunResult TrapReason ×
        FrameEffectJournal RollbackState (FrameTrace Event)) :=
  context.trapRollback?.map fun (state, effects) =>
    (⟨state, context.result.outcome⟩, effects)

end Solcore.Semantics.ParentIndexedFrameContinuationContext
