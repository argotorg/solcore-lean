import Solcore.Semantics.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuationWithInputsCoherenceProperties
import Solcore.Semantics.ParentIndexedFrameResolutionFoldProperties

/-! Compile-only consumers of parent-indexed resolution-fold laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Semantics

universe u v w x

/-- The returned branch law is consumed without unfolding the fold. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReturned (context.result.working, context.effectWorking) data := by
  exact context.foldResolutionWithTrapRollback_returned data outcomeEq
    onReturned onReverted onTrapped

/-- The reverted branch law exposes the exact indexed parent rollback pair. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReverted
        (parentWorking.1,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) data := by
  exact context.foldResolutionWithTrapRollback_reverted data outcomeEq
    onReturned onReverted onTrapped

private inductive ResolutionFoldCompileMarker where
  | trapped

/-- Choosing an optional result does not make the fold reject a trapped branch. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason) :
    context.foldResolutionWithTrapRollback
        (fun _ _ => none)
        (fun _ _ => none)
        (fun _ _ => some ResolutionFoldCompileMarker.trapped) =
      some ResolutionFoldCompileMarker.trapped := by
  rw [context.foldResolutionWithTrapRollback_trapped reason outcomeEq]

/-- The fourth law reconstructs the complete ADR-0127 view directly. -/
private example
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    context.foldResolutionWithTrapRollback
        (fun values data =>
          (FrameResolutionResult.returned values.1 values.2 data, none))
        (fun values data =>
          (FrameResolutionResult.reverted values.1 values.2 data, none))
        (fun values reason =>
          (FrameResolutionResult.trapped reason, some values)) =
      context.resolveWithTrapRollback := by
  exact context.foldResolutionWithTrapRollback_reconstructs_view

/-- ADR-0125 completion exposes the exact plain context and reconstructed view. -/
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
      parentContinuation.foldResolutionWithTrapRollback
          (fun values data =>
            (FrameResolutionResult.returned values.1 values.2 data, none))
          (fun values data =>
            (FrameResolutionResult.reverted values.1 values.2 data, none))
          (fun values reason =>
            (FrameResolutionResult.trapped reason, some values)) =
        parentContinuation.resolveWithTrapRollback := by
  obtain ⟨context, continuation, refined, lowerCompleted, coherent⟩ :=
    initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?_some_some_some_toFrameContinuationContext
      storageAddress inputs fuel doneOutcome parentContinuation completed
  exact ⟨context, continuation, refined, lowerCompleted, coherent,
    parentContinuation.foldResolutionWithTrapRollback_reconstructs_view⟩

/-- Additional fuel preserves both the nested boundary and exact fold result. -/
private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
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
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next)
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)))
    (more : fuel ≤ largerFuel) :
    ∃ largerContinuation,
      initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?
          storageAddress inputs largerFuel doneOutcome =
        some (some (some largerContinuation)) ∧
      largerContinuation.foldResolutionWithTrapRollback
          onReturned onReverted onTrapped =
        parentContinuation.foldResolutionWithTrapRollback
          onReturned onReverted onTrapped := by
  refine ⟨parentContinuation, ?_, rfl⟩
  exact
    initialization.runCodeWithStorageParentIndexedContinuationContextWithInputs?_some_some_some_stable
      storageAddress inputs doneOutcome completed more

end Tests
