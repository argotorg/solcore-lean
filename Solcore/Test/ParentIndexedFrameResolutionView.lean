import Solcore.Semantics.FrameResolutionResultContinuationProperties
import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuationWithInputsCoherenceProperties
import Solcore.Semantics.ParentIndexedFrameResolutionViewProperties

/-! Compile-only consumers of the parent-indexed resolution view. -/

set_option autoImplicit false

namespace Tests

open Solcore.Semantics

universe u v w x

/-- Returned resolution selects the returned callback and no trap rollback. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          Bytes → Option Next) :
    (context.resolveWithTrapRollback).1.continue?
          onReturned onReverted =
        onReturned
          (context.result.working, context.effectWorking) data ∧
      (context.resolveWithTrapRollback).2 = none ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  have branch := context.resolveWithTrapRollback_returned data outcomeEq
  constructor
  · simp only [branch.1, FrameResolutionResult.continue?_returned]
  · constructor
    · simp only [branch.1]
    · exact branch.2

/-- Reverted resolution selects the reverted callback and no trap rollback. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          Bytes → Option Next) :
    (context.resolveWithTrapRollback).1.continue?
          onReturned onReverted =
        onReverted
          (parentWorking.1,
            ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) data ∧
      (context.resolveWithTrapRollback).2 = none ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  have branch := context.resolveWithTrapRollback_reverted data outcomeEq
  constructor
  · simp only [branch.1, FrameResolutionResult.continue?_reverted]
  · constructor
    · simp only [branch.1]
    · exact branch.2

/-- Trap rejects both callbacks while selecting the exact parent rollback. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason)
    (onReturned onReverted :
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) →
          Bytes → Option Next) :
    (context.resolveWithTrapRollback).1.continue?
          onReturned onReverted = none ∧
      (context.resolveWithTrapRollback).2 =
        some
          (parentWorking.1,
            ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  have branch := context.resolveWithTrapRollback_trapped reason outcomeEq
  constructor
  · simp only [branch.1, FrameResolutionResult.continue?_trapped]
  · constructor
    · simp only [branch.1]
    · exact branch.2

/-- The public inverse law recovers exactly the trapped rollback selection. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (values :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) :
    (context.resolveWithTrapRollback).2 = some values ↔
      ∃ reason,
        context.result.outcome = FrameOutcome.trapped reason ∧
          values =
            (parentWorking.1,
              ⟨parentWorking.2.rollback,
                context.effectWorking.trace⟩) := by
  exact context.resolveWithTrapRollback_snd_eq_some_iff values

/-- ADR-0125 whole-context coherence transports through the first component. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation))) :
    ∃ context continuation,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorageContinuationContextWithInputs?
          inputs fuel doneOutcome = some (some continuation) ∧
      parentContinuation.toFrameContinuationContext = continuation ∧
      (parentContinuation.resolveWithTrapRollback).1 =
        continuation.resolve := by
  obtain ⟨context, continuation, refined, lowerCompleted, coherent⟩ :=
    initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?_some_some_some_toFrameContinuationContext
      storageAddress inputs fuel doneOutcome parentContinuation completed
  exact ⟨context, continuation, refined, lowerCompleted, coherent, by
    simpa only [
      ParentIndexedFrameContinuationContext.resolveWithTrapRollback] using
      congrArg FrameContinuationContext.resolve coherent⟩

/-- Additional fuel preserves the completed optional boundary and exact view. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Solcore.Core.Value → Solcore.Core.Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking}
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)))
    (more : fuel ≤ largerFuel) :
    ∃ largerContinuation,
      initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
          storageAddress inputs largerFuel doneOutcome =
        some (some (some largerContinuation)) ∧
      largerContinuation.resolveWithTrapRollback =
        parentContinuation.resolveWithTrapRollback := by
  refine ⟨parentContinuation, ?_, rfl⟩
  exact
    initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?_some_some_some_stable
      storageAddress inputs doneOutcome completed more

end Tests
