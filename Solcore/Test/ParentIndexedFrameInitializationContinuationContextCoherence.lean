import Solcore.ContractRuntime.ParentIndexedFrameInitializationContinuationContextCoherenceProperties

/-! Compile-only regressions for initialization continuation-context coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x

private example
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
  exact
    ParentIndexedFrameInitialization.toFrameContinuationContext_fromTraceExtension_eq_fromCheckpointedWorkingPair
      initialization outcome

private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (outcome : FrameOutcome TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Option Next) :
    (ParentIndexedFrameContinuationContext.fromTraceExtension
      parentWorking initialization.workingRollback
      initialization.initialTraceExtension
      ⟨initialization.initialWorld, outcome⟩).toFrameContinuationContext.continue?
        next =
      (FrameContinuationContext.fromCheckpointedWorkingPair
        initialization.toCheckpointedWorkingPair outcome).continue? next := by
  exact congrArg (fun context => context.continue? next)
    (ParentIndexedFrameInitialization.toFrameContinuationContext_fromTraceExtension_eq_fromCheckpointedWorkingPair
      initialization outcome)

end Tests
