import Solcore.ContractRuntime.FrameContinuationContextWithTracePrefix

/-! A completed frame context indexed by one designated parent working pair. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

/-- A trace-prefixed context whose checkpoints equal one parent working pair. -/
structure ParentIndexedFrameContinuationContext
    (RollbackState : Type u) (Event : Type v) (TrapReason : Type w)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    extends
      FrameContinuationContextWithTracePrefix
        RollbackState Event TrapReason where
  checkpoint_eq_parentWorking :
    (stateCheckpoint, effectCheckpoint) = parentWorking

end Solcore.ContractRuntime
