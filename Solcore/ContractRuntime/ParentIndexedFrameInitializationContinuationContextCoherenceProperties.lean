import Solcore.ContractRuntime.ParentIndexedFrameInitialization
import Solcore.ContractRuntime.ParentIndexedFrameContinuationConstruction
import Solcore.ContractRuntime.FrameContinuationContextFromCheckpointedWorkingPair

/-! Coherence of two continuation-context routes from indexed initialization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

/-- Both pure initialization routes produce the same plain continuation context. -/
theorem toFrameContinuationContext_fromTraceExtension_eq_fromCheckpointedWorkingPair
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (outcome : FrameOutcome TrapReason) :
    (ParentIndexedFrameContinuationContext.fromTraceExtension
      parentWorking initialization.workingRollback
      initialization.initialTraceExtension
      ⟨initialization.initialWorld, outcome⟩).toFrameContinuationContext =
      FrameContinuationContext.fromCheckpointedWorkingPair
        initialization.toCheckpointedWorkingPair outcome := by
  rfl

end Solcore.ContractRuntime.ParentIndexedFrameInitialization
