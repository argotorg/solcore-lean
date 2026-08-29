import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuationCoherenceProperties
import Solcore.Semantics.ParentIndexedFrameContinuationContextProperties
import Solcore.Semantics.ParentIndexedFrameTrapPropagationPayloadProperties
import Solcore.Semantics.FrameResolutionResultContinuation

/-! Compile-only consumers of parent-indexed selected execution continuation. -/

set_option autoImplicit false

namespace Tests

open Solcore.Semantics

universe u v w x

/-- All four partial boundaries remain distinguishable through the public laws. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress codeAddress : Address)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking) :
    (initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress codeAddress fuel doneOutcome = none ↔
        initialization.initialWorld.account? storageAddress = none) ∧
      (initialization.runCodeWithStorageParentIndexedContinuationContext?
            storageAddress codeAddress fuel doneOutcome = some none ↔
        ∃ context,
          initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
              storageAddress = some context ∧
          context.context.values.working.1.code? codeAddress = none) ∧
      (initialization.runCodeWithStorageParentIndexedContinuationContext?
            storageAddress codeAddress fuel doneOutcome = some (some none) ↔
        ∃ context resultContext exhausted,
          initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
              storageAddress = some context ∧
          context.runCodeWithStorage? codeAddress fuel =
            some ⟨resultContext, .outOfFuel exhausted⟩) ∧
      (initialization.runCodeWithStorageParentIndexedContinuationContext?
            storageAddress codeAddress fuel doneOutcome =
          some (some (some parentContinuation)) ↔
        ∃ context continuation,
          initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
              storageAddress = some context ∧
          context.runCodeWithStorageContinuationContext?
              codeAddress fuel doneOutcome = some (some continuation) ∧
          parentContinuation =
            ParentIndexedFrameContinuationContext.fromTraceExtension
              parentWorking initialization.workingRollback
              initialization.initialTraceExtension continuation.result) := by
  exact
    ⟨initialization.runCodeWithStorageParentIndexedContinuationContext?_eq_none_iff
        storageAddress codeAddress fuel doneOutcome,
      initialization.runCodeWithStorageParentIndexedContinuationContext?_eq_some_none_iff
        storageAddress codeAddress fuel doneOutcome,
      initialization.runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_none_iff
        storageAddress codeAddress fuel doneOutcome,
      initialization.runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_some_iff
        storageAddress codeAddress fuel doneOutcome parentContinuation⟩

/-- Whole-context equality transports resolution and continuation unchanged. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress codeAddress : Address)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress codeAddress fuel doneOutcome =
        some (some (some parentContinuation)))
    (next :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) → Option Next)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          Bytes → Option Next) :
    ∃ context continuation,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorageContinuationContext?
          codeAddress fuel doneOutcome = some (some continuation) ∧
      parentContinuation.toFrameContinuationContext = continuation ∧
      parentContinuation.toFrameContinuationContext.resolve =
        continuation.resolve ∧
      parentContinuation.toFrameContinuationContext.continue? next =
        continuation.continue? next ∧
      parentContinuation.toFrameContinuationContext.resolve.continue?
          onReturned onReverted =
        continuation.resolve.continue? onReturned onReverted := by
  obtain ⟨context, continuation, refined, lowerCompleted, coherent⟩ :=
    initialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_toFrameContinuationContext
      storageAddress codeAddress fuel doneOutcome parentContinuation completed
  exact ⟨context, continuation, refined, lowerCompleted, coherent,
    congrArg FrameContinuationContext.resolve coherent,
    congrArg (fun current => current.continue? next) coherent,
    congrArg
      (fun current => current.resolve.continue? onReturned onReverted)
      coherent⟩

/-- A completed parent-indexed return uses the terminal working pair. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : parentContinuation.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    parentContinuation.resolve = FrameResolutionResult.returned
        parentContinuation.result.working parentContinuation.effectWorking data ∧
      FrameTrace.IsPrefixOf parentWorking.2.trace
        parentContinuation.effectWorking.trace := by
  exact parentContinuation.resolve_returned data outcomeEq

/-- A completed parent-indexed revert restores the indexed parent pair. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : parentContinuation.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    parentContinuation.resolve = FrameResolutionResult.reverted parentWorking.1
        ⟨parentWorking.2.rollback, parentContinuation.effectWorking.trace⟩ data ∧
      FrameTrace.IsPrefixOf parentWorking.2.trace
        parentContinuation.effectWorking.trace := by
  exact parentContinuation.resolve_reverted data outcomeEq

/-- A completed parent-indexed trap feeds both existing parent selectors. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq :
      parentContinuation.result.outcome = FrameOutcome.trapped reason) :
    parentContinuation.trapRollback? =
        some
          (parentWorking.1,
            ⟨parentWorking.2.rollback,
              parentContinuation.effectWorking.trace⟩) ∧
      parentContinuation.trapPropagationPayload? =
        some
          (⟨parentWorking.1, FrameOutcome.trapped reason⟩,
            ⟨parentWorking.2.rollback,
              parentContinuation.effectWorking.trace⟩) := by
  exact
    ⟨parentContinuation.trapRollback?_trapped reason outcomeEq,
      parentContinuation.trapPropagationPayload?_trapped reason outcomeEq⟩

/-- Additional fuel preserves the exact completed parent-indexed context. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress codeAddress : Address)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking}
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress codeAddress fuel doneOutcome =
        some (some (some parentContinuation)))
    (more : fuel ≤ largerFuel) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress codeAddress largerFuel doneOutcome =
      some (some (some parentContinuation)) := by
  exact
    initialization.runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
      storageAddress codeAddress doneOutcome completed more

end Tests
