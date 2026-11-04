import Solcore.ContractRuntime.Internal.FrameLaws
import Solcore.ContractRuntime.Internal.CodeExecution

/-!
# Parent-indexed frames

Frame contexts tied to one designated parent working pair: trace prefixes, construction, trap
rollback, resolution, and initialization. Tests use this refinement layer; the top-level runners do
not.
-/

section
-- leanmerge: from Solcore.ContractRuntime.FrameContinuationContextWithTracePrefix
/-! A frame continuation context carrying an ordered trace-prefix invariant. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

/-- A continuation context whose checkpoint trace prefixes its working trace. -/
structure FrameContinuationContextWithTracePrefix
    (RollbackState : Type u) (Event : Type v)
    (TrapReason : Type w)
    extends FrameContinuationContext
      RollbackState (FrameTrace Event) TrapReason where
  tracePrefix :
    FrameTrace.IsPrefixOf effectCheckpoint.trace effectWorking.trace

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextWithTracePrefixTrapReasonMap`
-/

/-! Trap-reason mapping for continuation contexts with trace-prefix evidence. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContextWithTracePrefix

universe u v w x

/-- Map only the base context's trap reason, retaining exact prefix evidence. -/
def mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    FrameContinuationContextWithTracePrefix
      RollbackState Event MappedTrapReason :=
  {
    toFrameContinuationContext :=
      context.toFrameContinuationContext.mapTrapReason mapReason
    tracePrefix := context.tracePrefix
  }

end Solcore.ContractRuntime.FrameContinuationContextWithTracePrefix

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextWithTracePrefixTrapReasonMapProperties`
-/

/-! Construction, projection, and composition laws for refined context mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContextWithTracePrefix

universe u v w x y

@[simp] theorem mapTrapReason_mk
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContext RollbackState (FrameTrace Event) TrapReason)
    (tracePrefix :
      FrameTrace.IsPrefixOf
        context.effectCheckpoint.trace context.effectWorking.trace) :
    mapTrapReason mapReason
        (⟨context, tracePrefix⟩ :
          FrameContinuationContextWithTracePrefix
            RollbackState Event TrapReason) =
      (⟨context.mapTrapReason mapReason, tracePrefix⟩ :
        FrameContinuationContextWithTracePrefix
          RollbackState Event MappedTrapReason) := by
  rfl

@[simp] theorem toFrameContinuationContext_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    (mapTrapReason mapReason context).toFrameContinuationContext =
      context.toFrameContinuationContext.mapTrapReason mapReason := by
  rfl

@[simp] theorem mapTrapReason_id
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    mapTrapReason (fun reason => reason) context = context := by
  cases context with
  | mk context tracePrefix => simp

@[simp] theorem mapTrapReason_comp
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {IntermediateTrapReason : Type y}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    mapTrapReason second (mapTrapReason first context) =
      mapTrapReason (fun reason => second (first reason)) context := by
  cases context with
  | mk context tracePrefix =>
      cases context with
      | mk stateCheckpoint effectCheckpoint effectWorking result =>
          cases result with
          | mk working outcome =>
              cases outcome <;> rfl

end Solcore.ContractRuntime.FrameContinuationContextWithTracePrefix
end

section
-- leanmerge: from Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
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
end

section
-- leanmerge: from Solcore.ContractRuntime.ParentIndexedFrameContinuationConstruction
/-! Restricted construction of a parent-indexed context from a trace extension. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

/-- Build the indexed context while deriving its two relationship proofs. -/
def fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking :=
  {
    stateCheckpoint := parentWorking.1
    effectCheckpoint := parentWorking.2
    effectWorking := ⟨workingRollback, extension.toTrace⟩
    result := result
    tracePrefix := extension.earlier_isPrefixOf_toTrace
    checkpoint_eq_parentWorking := rfl
  }

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameContinuationConstructionProperties`
-/

/-! Projection laws for trace-extension parent-context construction. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

@[simp] theorem stateCheckpoint_fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    (fromTraceExtension
      parentWorking workingRollback extension result).stateCheckpoint =
      parentWorking.1 := by
  rfl

@[simp] theorem effectCheckpoint_fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    (fromTraceExtension
      parentWorking workingRollback extension result).effectCheckpoint =
      parentWorking.2 := by
  rfl

@[simp] theorem effectWorking_fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    (fromTraceExtension
      parentWorking workingRollback extension result).effectWorking =
      ⟨workingRollback, extension.toTrace⟩ := by
  rfl

@[simp] theorem result_fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    (fromTraceExtension
      parentWorking workingRollback extension result).result = result := by
  rfl

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
end

section
-- leanmerge: from Solcore.ContractRuntime.ParentIndexedFrameTrapRollback
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

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameTrapRollbackProperties`
-/

/-! Outcome laws for parent-indexed trapped-frame rollback selection. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

theorem trapRollback?_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.trapRollback? = none := by
  unfold trapRollback?
  rw [outcomeEq]

theorem trapRollback?_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.trapRollback? = none := by
  unfold trapRollback?
  rw [outcomeEq]

theorem trapRollback?_trapped
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason) :
    context.trapRollback? =
      some
        (parentWorking.1,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) := by
  have stateCheckpointEq : context.stateCheckpoint = parentWorking.1 :=
    congrArg Prod.fst context.checkpoint_eq_parentWorking
  have effectCheckpointEq : context.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd context.checkpoint_eq_parentWorking
  unfold trapRollback?
  rw [outcomeEq, stateCheckpointEq, effectCheckpointEq]

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
end

section
-- leanmerge: from Solcore.ContractRuntime.ParentIndexedFrameResolutionView
/-! Read-only pairing of parent-indexed resolution and trap rollback selection. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

/--
Observe ordinary frame resolution together with the existing opt-in rollback
pair selected only for a trapped outcome.
-/
def resolveWithTrapRollback
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    FrameResolutionResult RollbackState (FrameTrace Event) TrapReason ×
      Option
        (WorldState ×
          FrameEffectJournal RollbackState (FrameTrace Event)) :=
  (context.resolve, context.trapRollback?)

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameResolutionViewProperties`
-/

/-! Exact branch laws for the parent-indexed resolution view. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

theorem resolveWithTrapRollback_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.resolveWithTrapRollback =
        (FrameResolutionResult.returned
          context.result.working context.effectWorking data, none) ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  have resolved := context.resolve_returned data outcomeEq
  constructor
  · unfold resolveWithTrapRollback
    rw [resolved.1, context.trapRollback?_returned data outcomeEq]
  · exact resolved.2

theorem resolveWithTrapRollback_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.resolveWithTrapRollback =
        (FrameResolutionResult.reverted parentWorking.1
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩ data,
          none) ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  have resolved := context.resolve_reverted data outcomeEq
  constructor
  · unfold resolveWithTrapRollback
    rw [resolved.1, context.trapRollback?_reverted data outcomeEq]
  · exact resolved.2

theorem resolveWithTrapRollback_trapped
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason) :
    context.resolveWithTrapRollback =
        (FrameResolutionResult.trapped reason,
          some
            (parentWorking.1,
              ⟨parentWorking.2.rollback, context.effectWorking.trace⟩)) ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace := by
  constructor
  · unfold resolveWithTrapRollback FrameContinuationContext.resolve
    rw [outcomeEq, context.trapRollback?_trapped reason outcomeEq]
  · exact context.parentWorking_tracePrefix

theorem resolveWithTrapRollback_snd_eq_some_iff
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
              ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) := by
  change context.trapRollback? = some values ↔ _
  constructor
  · intro selected
    cases outcomeEq : context.result.outcome with
    | returned data =>
        rw [context.trapRollback?_returned data outcomeEq] at selected
        contradiction
    | reverted data =>
        rw [context.trapRollback?_reverted data outcomeEq] at selected
        contradiction
    | trapped reason =>
        rw [context.trapRollback?_trapped reason outcomeEq] at selected
        exact ⟨reason, rfl, (Option.some.inj selected).symm⟩
  · rintro ⟨reason, outcomeEq, rfl⟩
    exact context.trapRollback?_trapped reason outcomeEq

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameResolutionViewTrapReasonMapProperties`
-/

/-! Naturality of trap-reason mapping under parent-indexed resolution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w x

/-- Reason mapping changes only the resolution component of the view. -/
@[simp] theorem resolveWithTrapRollback_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (context.mapTrapReason mapReason).resolveWithTrapRollback =
      (FrameResolutionResult.mapTrapReason mapReason
          (context.resolveWithTrapRollback).1,
        (context.resolveWithTrapRollback).2) := by
  apply Prod.ext
  · change
      (context.toFrameContinuationContext.mapTrapReason mapReason).resolve =
        FrameResolutionResult.mapTrapReason mapReason
          context.toFrameContinuationContext.resolve
    exact FrameContinuationContext.resolve_mapTrapReason
      mapReason context.toFrameContinuationContext
  · unfold resolveWithTrapRollback trapRollback?
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
end

section
-- leanmerge: from Solcore.ContractRuntime.ParentIndexedFrameResolutionFold
/-! Caller-owned elimination of parent-indexed frame outcomes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w x

/-- Select one pure caller-owned function for a completed frame outcome. -/
def foldResolutionWithTrapRollback
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) : Next :=
  match context.result.outcome with
  | .returned data =>
      onReturned (context.result.working, context.effectWorking) data
  | .reverted data =>
      onReverted
        (context.stateCheckpoint,
          ⟨context.effectCheckpoint.rollback, context.effectWorking.trace⟩)
        data
  | .trapped reason =>
      onTrapped
        (context.stateCheckpoint,
          ⟨context.effectCheckpoint.rollback, context.effectWorking.trace⟩)
        reason

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameResolutionFoldProperties`
-/

/-! Exact branch and view-coherence laws for parent-indexed resolution folds. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w x

theorem foldResolutionWithTrapRollback_returned
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
  unfold foldResolutionWithTrapRollback
  rw [outcomeEq]

theorem foldResolutionWithTrapRollback_reverted
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
  have stateCheckpointEq : context.stateCheckpoint = parentWorking.1 :=
    congrArg Prod.fst context.checkpoint_eq_parentWorking
  have effectCheckpointEq : context.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd context.checkpoint_eq_parentWorking
  unfold foldResolutionWithTrapRollback
  rw [outcomeEq, stateCheckpointEq, effectCheckpointEq]

theorem foldResolutionWithTrapRollback_trapped
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onTrapped
        (parentWorking.1,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) reason := by
  have stateCheckpointEq : context.stateCheckpoint = parentWorking.1 :=
    congrArg Prod.fst context.checkpoint_eq_parentWorking
  have effectCheckpointEq : context.effectCheckpoint = parentWorking.2 :=
    congrArg Prod.snd context.checkpoint_eq_parentWorking
  unfold foldResolutionWithTrapRollback
  rw [outcomeEq, stateCheckpointEq, effectCheckpointEq]

theorem foldResolutionWithTrapRollback_reconstructs_view
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
  cases outcomeEq : context.result.outcome with
  | returned data =>
      rw [context.foldResolutionWithTrapRollback_returned data outcomeEq]
      exact (context.resolveWithTrapRollback_returned data outcomeEq).1.symm
  | reverted data =>
      rw [context.foldResolutionWithTrapRollback_reverted data outcomeEq]
      exact (context.resolveWithTrapRollback_reverted data outcomeEq).1.symm
  | trapped reason =>
      rw [context.foldResolutionWithTrapRollback_trapped reason outcomeEq]
      exact (context.resolveWithTrapRollback_trapped reason outcomeEq).1.symm

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameResolutionFoldTrapReasonMapProperties`
-/

/-! Naturality of trap-reason mapping under parent-indexed resolution folds. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w x y

/-- Reason mapping changes only the trap function observed by the fold. -/
@[simp] theorem foldResolutionWithTrapRollback_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        MappedTrapReason → Next) :
    (context.mapTrapReason mapReason).foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      context.foldResolutionWithTrapRollback
        onReturned onReverted
        (fun values reason => onTrapped values (mapReason reason)) := by
  unfold foldResolutionWithTrapRollback
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
end

section
-- leanmerge: from Solcore.ContractRuntime.ParentIndexedFrameTrapPropagationPayload
/-! Opt-in trap propagation payloads for parent-indexed frame contexts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

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

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameTrapPropagationPayloadProperties`
-/

/-! Outcome laws for parent-indexed trap propagation payload selection. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

theorem trapPropagationPayload?_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.trapPropagationPayload? = none := by
  unfold trapPropagationPayload?
  rw [context.trapRollback?_returned data outcomeEq]
  rfl

theorem trapPropagationPayload?_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.trapPropagationPayload? = none := by
  unfold trapPropagationPayload?
  rw [context.trapRollback?_reverted data outcomeEq]
  rfl

theorem trapPropagationPayload?_trapped
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason) :
    context.trapPropagationPayload? =
      some
        (⟨parentWorking.1, FrameOutcome.trapped reason⟩,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) := by
  unfold trapPropagationPayload?
  rw [context.trapRollback?_trapped reason outcomeEq, outcomeEq]
  rfl

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameTrapPropagationPayloadCoherenceProperties`
-/

/-! Coherence laws for successfully selected trap propagation payloads. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameContinuationContext

universe u v w

theorem trapPropagationPayload?_eq_some_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (payload :
      FrameRunResult TrapReason ×
        FrameEffectJournal RollbackState (FrameTrace Event)) :
    context.trapPropagationPayload? = some payload ↔
      ∃ reason,
        context.result.outcome = FrameOutcome.trapped reason ∧
        payload =
          (⟨parentWorking.1, FrameOutcome.trapped reason⟩,
            ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) := by
  constructor
  · intro payloadEq
    cases outcomeEq : context.result.outcome with
    | returned data =>
        rw [context.trapPropagationPayload?_returned data outcomeEq] at payloadEq
        contradiction
    | reverted data =>
        rw [context.trapPropagationPayload?_reverted data outcomeEq] at payloadEq
        contradiction
    | trapped reason =>
        rw [context.trapPropagationPayload?_trapped reason outcomeEq] at payloadEq
        exact ⟨reason, rfl, Option.some.inj payloadEq.symm⟩
  · rintro ⟨reason, outcomeEq, rfl⟩
    exact context.trapPropagationPayload?_trapped reason outcomeEq

theorem trapPropagationPayload?_some_tracePrefix
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (payload :
      FrameRunResult TrapReason ×
        FrameEffectJournal RollbackState (FrameTrace Event))
    (payloadEq : context.trapPropagationPayload? = some payload) :
    FrameTrace.IsPrefixOf parentWorking.2.trace payload.2.trace := by
  obtain ⟨reason, outcomeEq, payloadExact⟩ :=
    (context.trapPropagationPayload?_eq_some_iff payload).mp payloadEq
  subst payload
  exact context.parentWorking_tracePrefix

end Solcore.ContractRuntime.ParentIndexedFrameContinuationContext
end

section
-- leanmerge: from Solcore.ContractRuntime.ParentIndexedFrameInitialization
/-! Parent-indexed construction of initial frame state values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/-- Caller-supplied initial state values relative to one parent working pair. -/
structure ParentIndexedFrameInitialization
    (RollbackState : Type u) (Event : Type v)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) :
    Type (max u v) where
  initialWorld : WorldState
  workingRollback : RollbackState

namespace ParentIndexedFrameInitialization

/-- Start an event-only trace extension at the indexed parent trace. -/
def initialTraceExtension
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (_initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    FrameTrace.ExtensionFrom parentWorking.2.trace :=
  FrameTrace.ExtensionFrom.start parentWorking.2.trace

/-- Build checkpointed values from the parent and caller-supplied state. -/
def toCheckpointedWorkingPair
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    FrameCheckpointedWorkingPair RollbackState (FrameTrace Event) :=
  ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
    (initialization.initialWorld,
      ⟨initialization.workingRollback,
        initialization.initialTraceExtension.toTrace⟩)⟩

end ParentIndexedFrameInitialization

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationProperties`
-/

/-! Canonical observation laws for parent-indexed frame initialization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

/-- The initial extension observes the exact indexed parent trace. -/
@[simp] theorem initialTraceExtension_toTrace
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.initialTraceExtension.toTrace =
      parentWorking.2.trace := by
  exact FrameTrace.ExtensionFrom.toTrace_start parentWorking.2.trace

/-- The derived carrier has the parent checkpoint and supplied initial state. -/
@[simp] theorem toCheckpointedWorkingPair_eq
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.toCheckpointedWorkingPair =
      ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
        (initialization.initialWorld,
          ⟨initialization.workingRollback, parentWorking.2.trace⟩)⟩ := by
  simp [toCheckpointedWorkingPair]

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationStorageAddress`
-/

/-! Canonical storage-address wiring for parent-indexed initialization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

/-- Bind one storage selector to the initialized checkpointed working values. -/
def toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    FrameCheckpointedWorkingPairWithStorageAddress
      RollbackState (FrameTrace Event) :=
  ⟨storageAddress, initialization.toCheckpointedWorkingPair⟩

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationStorageAddressProperties`
-/

/-! Projection laws for storage-address initialization wiring. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

@[simp] theorem
    storageAddress_toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).storageAddress = storageAddress := by
  rfl

@[simp] theorem values_toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).values = initialization.toCheckpointedWorkingPair := by
  rfl

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccount`
-/

/-! Present-storage refinement for parent-indexed initialization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

/-- Refine the initialized storage selector exactly when its Account exists. -/
def toCheckpointedWorkingPairWithPresentStorageAccount?
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    Option
      (FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState (FrameTrace Event)) :=
  (initialization.toCheckpointedWorkingPairWithStorageAddress
    storageAddress).withPresentStorageAccount?

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccountProperties`
-/

/-! Branch laws for parent-indexed initialization storage refinement. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v

/-- An absent Account keeps the initialization refinement unavailable. -/
@[simp] theorem
    toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (absent :
      initialization.initialWorld.account? storageAddress = none) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress = none := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_absent
      (initialization.toCheckpointedWorkingPairWithStorageAddress storageAddress)
      absent

/-- A present Account returns its exact initialized evidence carrier. -/
@[simp] theorem
    toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (account : Account)
    (present :
      initialization.initialWorld.account? storageAddress = some account) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress =
      some
        ⟨initialization.toCheckpointedWorkingPairWithStorageAddress
            storageAddress,
          account,
          present⟩ := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_present
      (initialization.toCheckpointedWorkingPairWithStorageAddress storageAddress)
      account present

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuation`
-/

/-! Parent-indexed continuation construction with immutable execution input. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

/-- Lift the same input through storage selection, execution, and completion. -/
def runCodeWithStorageParentIndexedContinuationContext?
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
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option
      (Option
        (Option
          (ParentIndexedFrameContinuationContext
            RollbackState Event TrapReason parentWorking))) :=
  (initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress).map fun context =>
    (context.runCodeWithStorageContinuationContext?
      inputs fuel doneOutcome).map fun completed =>
        completed.map fun continuation =>
          ParentIndexedFrameContinuationContext.fromTraceExtension
            parentWorking initialization.workingRollback
            initialization.initialTraceExtension continuation.result

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuationProperties`
-/

/-! Result-shape laws for parent-indexed execution with immutable input. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

@[simp] theorem
    runCodeWithStorageParentIndexedContinuationContext?_eq_none_iff
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
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome = none ↔
      initialization.initialWorld.account? storageAddress = none := by
  cases observed : initialization.initialWorld.account? storageAddress with
  | none =>
      unfold runCodeWithStorageParentIndexedContinuationContext?
      rw [toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
        initialization storageAddress observed]
      simp only [Option.map_none]
  | some account =>
      unfold runCodeWithStorageParentIndexedContinuationContext?
      rw [toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
        initialization storageAddress account observed]
      simp only [Option.map_some, Option.some_ne_none]

theorem
    runCodeWithStorageParentIndexedContinuationContext?_eq_some_none_iff
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
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome = some none ↔
      ∃ context,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.context.values.working.1.code? inputs.codeAddress = none := by
  unfold runCodeWithStorageParentIndexedContinuationContext?
  constructor
  · intro observed
    rw [Option.map_eq_some_iff] at observed
    obtain ⟨context, refined, selected⟩ := observed
    have lowerNone := Option.map_eq_none_iff.mp selected
    exact ⟨context, refined,
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_none_iff
        context inputs fuel doneOutcome).mp lowerNone⟩
  · rintro ⟨context, refined, codeAbsent⟩
    have selected :=
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_none_iff
        context inputs fuel doneOutcome).mpr codeAbsent
    rw [refined]
    simp only [Option.map_some]
    rw [selected]
    rfl

theorem
    runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_none_iff
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
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome = some (some none) ↔
      (∃ context resultContext exhausted,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.runCodeWithStorage? inputs fuel =
          some ⟨resultContext, .outOfFuel exhausted⟩) ∨
      ∃ context resultContext suspension remainingFuel,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.runCodeWithStorage? inputs fuel =
          some ⟨resultContext,
            .unsupported suspension remainingFuel⟩ := by
  unfold runCodeWithStorageParentIndexedContinuationContext?
  constructor
  · intro observed
    rw [Option.map_eq_some_iff] at observed
    obtain ⟨context, refined, selected⟩ := observed
    rw [Option.map_eq_some_iff] at selected
    obtain ⟨completion, ran, built⟩ := selected
    have completionEq : completion = none := by
      simpa only [Option.map_eq_none_iff] using built
    subst completion
    rcases
      (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_some_none_iff
        context inputs fuel doneOutcome).mp ran with
      ⟨⟨resultContext, exhausted, exactRun⟩⟩ |
        ⟨resultContext, suspension, remainingFuel, exactRun⟩
    · exact .inl ⟨context, resultContext, exhausted, refined, exactRun⟩
    · exact .inr
        ⟨context, resultContext, suspension, remainingFuel, refined, exactRun⟩
  · intro observed
    rcases observed with
      ⟨context, resultContext, exhausted, refined, exactRun⟩ |
      ⟨context, resultContext, suspension, remainingFuel, refined, exactRun⟩
    · have selected :=
        (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_some_none_iff
          context inputs fuel doneOutcome).mpr
            (.inl ⟨resultContext, exhausted, exactRun⟩)
      rw [refined]
      simp only [Option.map_some]
      rw [selected]
      rfl
    · have selected :=
        (FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_eq_some_none_iff
          context inputs fuel doneOutcome).mpr
            (.inr ⟨resultContext, suspension, remainingFuel, exactRun⟩)
      rw [refined]
      simp only [Option.map_some]
      rw [selected]
      rfl

theorem
    runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_some_iff
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
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)) ↔
      ∃ context continuation,
        initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
            storageAddress = some context ∧
        context.runCodeWithStorageContinuationContext?
            inputs fuel doneOutcome = some (some continuation) ∧
        parentContinuation =
          ParentIndexedFrameContinuationContext.fromTraceExtension
            parentWorking initialization.workingRollback
            initialization.initialTraceExtension continuation.result := by
  unfold runCodeWithStorageParentIndexedContinuationContext?
  constructor
  · intro observed
    rw [Option.map_eq_some_iff] at observed
    obtain ⟨context, refined, selected⟩ := observed
    rw [Option.map_eq_some_iff] at selected
    obtain ⟨completion, ran, built⟩ := selected
    rw [Option.map_eq_some_iff] at built
    obtain ⟨continuation, completionEq, parentEq⟩ := built
    subst completion
    exact ⟨context, continuation, refined, ran, parentEq.symm⟩
  · rintro ⟨context, continuation, refined, completed, parentEq⟩
    rw [refined]
    simp only [Option.map_some]
    rw [completed]
    simp only [Option.map_some]
    rw [← parentEq]

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationPresentStorageAccountCodeFrameContinuationCoherenceProperties`
-/

/-! Coherence and stability for parent-indexed explicit-input execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedFrameInitialization

universe u v w

private theorem completedContinuation_eq_parentIndexed
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (context :
      HostStorageDriver.Context RollbackState (FrameTrace Event))
    (refined :
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (continuation :
      FrameContinuationContext RollbackState (FrameTrace Event) TrapReason)
    (completed :
      context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some (some continuation)) :
    (ParentIndexedFrameContinuationContext.fromTraceExtension
      parentWorking initialization.workingRollback
      initialization.initialTraceExtension continuation.result
    ).toFrameContinuationContext = continuation := by
  have contextValues :
      context.context.values = initialization.toCheckpointedWorkingPair := by
    unfold toCheckpointedWorkingPairWithPresentStorageAccount? at refined
    unfold FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?
      at refined
    split at refined
    · contradiction
    · have exactContext := Option.some.inj refined
      subst context
      rfl
  unfold FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?
    at completed
  rw [Option.map_eq_some_iff] at completed
  obtain ⟨result, execution, resultCompleted⟩ := completed
  cases result with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          have continuationEq :
              FrameContinuationContext.fromCheckpointedWorkingPair
                  finalContext.context.values
                  (doneOutcome finalContext value store) = continuation := by
            simpa only [HostDriverResult.toFrameContinuationContext?_done,
              Option.some.injEq] using resultCompleted
          have checkpointPreserved :=
            FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_checkpoint
              context inputs fuel
              (HostDriverResult.mk finalContext (.done value store)) execution
          have effectsPreserved :=
            FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorage?_some_workingEffects
              context inputs fuel
              (HostDriverResult.mk finalContext (.done value store)) execution
          have finalCheckpoint :
              finalContext.context.values.checkpoint =
                FrameCheckpointSnapshot.fromWorkingPair parentWorking := by
            rw [checkpointPreserved, contextValues,
              toCheckpointedWorkingPair_eq]
          have finalEffects :
              finalContext.context.values.working.2 =
                ⟨initialization.workingRollback, parentWorking.2.trace⟩ := by
            rw [effectsPreserved, contextValues,
              toCheckpointedWorkingPair_eq]
          rw [← continuationEq]
          unfold ParentIndexedFrameContinuationContext.fromTraceExtension
          unfold FrameContinuationContext.fromCheckpointedWorkingPair
          simp only [initialTraceExtension_toTrace]
          rw [finalCheckpoint, finalEffects]
          rfl
      | unsupported suspension remainingFuel => simp at resultCompleted
      | outOfFuel exhausted => simp at resultCompleted
      | fault error faultState => simp at resultCompleted

theorem
    runCodeWithStorageParentIndexedContinuationContext?_some_some_some_toFrameContinuationContext
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
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation))) :
    ∃ context continuation,
      initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress = some context ∧
      context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some (some continuation) ∧
      parentContinuation.toFrameContinuationContext = continuation := by
  unfold runCodeWithStorageParentIndexedContinuationContext?
    at completed
  rw [Option.map_eq_some_iff] at completed
  obtain ⟨context, refined, selected⟩ := completed
  rw [Option.map_eq_some_iff] at selected
  obtain ⟨completion, ran, parentBuilt⟩ := selected
  rw [Option.map_eq_some_iff] at parentBuilt
  obtain ⟨continuation, continuationEq, parentEq⟩ := parentBuilt
  have lowerCompleted :
      context.runCodeWithStorageContinuationContext?
          inputs fuel doneOutcome = some (some continuation) := by
    rw [ran, continuationEq]
  subst parentContinuation
  exact ⟨context, continuation, refined, lowerCompleted,
    completedContinuation_eq_parentIndexed initialization
      storageAddress inputs context refined fuel doneOutcome continuation
      lowerCompleted⟩

theorem
    runCodeWithStorageParentIndexedContinuationContext?_some_some_some_stable
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    {fuel largerFuel : Nat}
    {parentContinuation :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking}
    (completed :
      initialization.runCodeWithStorageParentIndexedContinuationContext?
          storageAddress inputs fuel doneOutcome =
        some (some (some parentContinuation)))
    (more : fuel ≤ largerFuel) :
    initialization.runCodeWithStorageParentIndexedContinuationContext?
        storageAddress inputs largerFuel doneOutcome =
      some (some (some parentContinuation)) := by
  rw [
    runCodeWithStorageParentIndexedContinuationContext?_eq_some_some_some_iff]
    at completed ⊢
  obtain ⟨context, continuation, refined, lowerCompleted, parentEq⟩ :=
    completed
  exact ⟨context, continuation, refined,
    FrameCheckpointedWorkingPairWithPresentStorageAccount.runCodeWithStorageContinuationContext?_some_some_stable
      context inputs doneOutcome lowerCompleted more,
    parentEq⟩

end Solcore.ContractRuntime.ParentIndexedFrameInitialization

/-!
## Consolidated module: `Solcore.ContractRuntime.ParentIndexedFrameInitializationContinuationContextCoherenceProperties`
-/

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
end
