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

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameContinuationContextProperties`
-/

/-! Parent-indexed trace and resolution laws for completed frame contexts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

/-- The indexed parent trace prefixes the completed context's working trace. -/
theorem parentWorking_tracePrefix
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    FrameTrace.IsPrefixOf
      parentWorking.2.trace context.effectWorking.trace := by
  have effectCheckpointEq : context.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd context.checkpoint_eq_parentWorking
  simpa only [effectCheckpointEq] using context.tracePrefix

/-- A returned outcome resolves to the completed context's working pair. -/
theorem resolve_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.resolve = FrameResolutionResult.returned
      context.result.working context.effectWorking data ∧
    FrameTrace.IsPrefixOf
      parentWorking.2.trace context.effectWorking.trace := by
  constructor
  · unfold FrameContinuationContext.resolve
    rw [outcomeEq]
  · exact context.parentWorking_tracePrefix

/-- A reverted outcome restores the indexed parent state and rollback component. -/
theorem resolve_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.resolve = FrameResolutionResult.reverted parentWorking.1
      ⟨parentWorking.2.rollback, context.effectWorking.trace⟩ data ∧
    FrameTrace.IsPrefixOf
      parentWorking.2.trace context.effectWorking.trace := by
  have stateCheckpointEq : context.stateCheckpoint = parentWorking.1 :=
    congrArg Prod.fst context.checkpoint_eq_parentWorking
  have effectCheckpointEq : context.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd context.checkpoint_eq_parentWorking
  constructor
  · unfold FrameContinuationContext.resolve
    rw [outcomeEq, stateCheckpointEq, effectCheckpointEq]
  · exact context.parentWorking_tracePrefix

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameContinuationContextTrapReasonMap`
-/

/-! Trap-reason mapping for parent-indexed continuation contexts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w x

/-- Map only the refined context's trap reason, retaining the parent index. -/
def mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    ParentIndexedFrameContinuationContext
      RollbackState Event MappedTrapReason parentWorking :=
  {
    toFrameContinuationContextWithTracePrefix :=
      context.toFrameContinuationContextWithTracePrefix.mapTrapReason mapReason
    checkpoint_eq_parentWorking := context.checkpoint_eq_parentWorking
  }

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameContinuationContextTrapReasonMapProperties`
-/

/-! Construction, projection, and composition laws for indexed context mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w x y

@[simp] theorem mapTrapReason_mk
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContextWithTracePrefix
      RollbackState Event TrapReason)
    (checkpointEq :
      (context.stateCheckpoint, context.effectCheckpoint) = parentWorking) :
    mapTrapReason mapReason
        (⟨context, checkpointEq⟩ : ParentIndexedFrameContinuationContext
          RollbackState Event TrapReason parentWorking) =
      (⟨context.mapTrapReason mapReason, checkpointEq⟩ :
        ParentIndexedFrameContinuationContext
          RollbackState Event MappedTrapReason parentWorking) := by
  rfl

@[simp] theorem toFrameContinuationContextWithTracePrefix_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (mapTrapReason mapReason context).toFrameContinuationContextWithTracePrefix =
      context.toFrameContinuationContextWithTracePrefix.mapTrapReason mapReason := by
  rfl

@[simp] theorem mapTrapReason_id
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    mapTrapReason (fun reason => reason) context = context := by
  cases context with
  | mk context checkpointEq => simp

@[simp] theorem mapTrapReason_comp
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {IntermediateTrapReason : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    mapTrapReason second (mapTrapReason first context) =
      mapTrapReason (fun reason => second (first reason)) context := by
  cases context with
  | mk context checkpointEq =>
      cases context with
      | mk context tracePrefix =>
          cases context with
          | mk stateCheckpoint effectCheckpoint effectWorking result =>
              cases result with
              | mk working outcome =>
                  cases outcome <;> rfl

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
