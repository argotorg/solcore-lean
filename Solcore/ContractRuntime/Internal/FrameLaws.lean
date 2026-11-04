import Solcore.ContractRuntime.Frames
import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.WorldState
import Solcore.ContractRuntime.Internal.WorldStateLaws

/-!
# Laws of frames

Outcomes, journals, traces, run results, continuation contexts, resolution, and the checkpointed
working pairs.
-/

section
-- leanmerge: from Solcore.ContractRuntime.FrameOutcome
/-! Internal, syntax-independent outcomes produced when one contract frame halts. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameOutcomeProperties`
-/

/-! Focused laws for syntax-independent contract frame halt outcomes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace FrameOutcome

universe u

@[simp] theorem kind_returned
    {TrapReason : Type u} (data : Bytes) :
    kind (FrameOutcome.returned (TrapReason := TrapReason) data) =
      FrameHaltKind.returned := by
  rfl

@[simp] theorem kind_reverted
    {TrapReason : Type u} (data : Bytes) :
    kind (FrameOutcome.reverted (TrapReason := TrapReason) data) =
      FrameHaltKind.reverted := by
  rfl

@[simp] theorem kind_trapped
    {TrapReason : Type u} (reason : TrapReason) :
    kind (FrameOutcome.trapped reason) = FrameHaltKind.trapped := by
  rfl

theorem returndata?_eq_some_iff
    {TrapReason : Type u} (outcome : FrameOutcome TrapReason) (data : Bytes) :
    returndata? outcome = some data ↔
      outcome = FrameOutcome.returned data := by
  cases outcome <;> constructor <;> intro h <;> cases h <;> rfl

theorem revertdata?_eq_some_iff
    {TrapReason : Type u} (outcome : FrameOutcome TrapReason) (data : Bytes) :
    revertdata? outcome = some data ↔
      outcome = FrameOutcome.reverted data := by
  cases outcome <;> constructor <;> intro h <;> cases h <;> rfl

theorem trapReason?_eq_some_iff
    {TrapReason : Type u} (outcome : FrameOutcome TrapReason)
    (reason : TrapReason) :
    trapReason? outcome = some reason ↔
      outcome = FrameOutcome.trapped reason := by
  cases outcome <;> constructor <;> intro h <;> cases h <;> rfl

end FrameOutcome

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameOutcomeTrapReasonMap`
-/

/-! Caller-supplied pure mapping of frame trap-reason types. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameOutcomeTrapReasonMapProperties`
-/

/-! Constructor and composition laws for frame trap-reason mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameOutcome

universe u v w

@[simp] theorem mapTrapReason_returned
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason) (data : Bytes) :
    mapTrapReason mapReason
        (FrameOutcome.returned (TrapReason := TrapReason) data) =
      FrameOutcome.returned (TrapReason := MappedTrapReason) data := by
  rfl

@[simp] theorem mapTrapReason_reverted
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason) (data : Bytes) :
    mapTrapReason mapReason
        (FrameOutcome.reverted (TrapReason := TrapReason) data) =
      FrameOutcome.reverted (TrapReason := MappedTrapReason) data := by
  rfl

@[simp] theorem mapTrapReason_trapped
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (reason : TrapReason) :
    mapTrapReason mapReason (FrameOutcome.trapped reason) =
      FrameOutcome.trapped (mapReason reason) := by
  rfl

@[simp] theorem mapTrapReason_id
    {TrapReason : Type u} (outcome : FrameOutcome TrapReason) :
    mapTrapReason (fun reason => reason) outcome = outcome := by
  cases outcome <;> rfl

@[simp] theorem mapTrapReason_comp
    {TrapReason : Type u}
    {IntermediateTrapReason : Type v}
    {MappedTrapReason : Type w}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (outcome : FrameOutcome TrapReason) :
    mapTrapReason second (mapTrapReason first outcome) =
      mapTrapReason (fun reason => second (first reason)) outcome := by
  cases outcome <;> rfl

end Solcore.ContractRuntime.FrameOutcome
end

section
-- leanmerge: from Solcore.ContractRuntime.FrameEffectJournal
/-! Generic rollback-scoped state and revert-surviving trace policy. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameEffectJournalProperties`
-/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameEffectJournal

universe u v w

@[simp] theorem resolved?_returned
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolved? checkpoint working
      (FrameOutcome.returned (TrapReason := TrapReason) data) = some working := by
  rfl

@[simp] theorem resolved?_reverted
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolved? checkpoint working
      (FrameOutcome.reverted (TrapReason := TrapReason) data) =
        some ⟨checkpoint.rollback, working.trace⟩ := by
  rfl

@[simp] theorem resolved?_trapped
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason) :
    resolved? checkpoint working (.trapped reason) = none := by
  rfl

theorem resolved?_child_return_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentCheckpoint childCheckpoint childWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolved? childCheckpoint childWorking
      (FrameOutcome.returned (TrapReason := TrapReason) childData)).bind
        (fun childResolved => resolved? parentCheckpoint childResolved
          (FrameOutcome.reverted (TrapReason := TrapReason) parentData)) =
      some ⟨parentCheckpoint.rollback, childWorking.trace⟩ := by
  rfl

theorem resolved?_child_revert_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentCheckpoint childCheckpoint childWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolved? childCheckpoint childWorking
      (FrameOutcome.reverted (TrapReason := TrapReason) childData)).bind
        (fun childResolved => resolved? parentCheckpoint childResolved
          (FrameOutcome.reverted (TrapReason := TrapReason) parentData)) =
      some ⟨parentCheckpoint.rollback, childWorking.trace⟩ := by
  rfl

end Solcore.ContractRuntime.FrameEffectJournal
end

section
-- leanmerge: from Solcore.ContractRuntime.FrameTrace
/-! Finite chronological traces for opt-in frame-effect observations. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTraceProperties`
-/

/-! Observation and extension algebra for finite chronological frame traces. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace

universe u

@[simp] theorem toList_empty {Event : Type u} :
    (empty : FrameTrace Event).toList = [] := by
  rfl

@[simp] theorem toList_append {Event : Type u}
    (earlier later : FrameTrace Event) :
    (append earlier later).toList = earlier.toList ++ later.toList := by
  rfl

@[simp] theorem toList_record {Event : Type u}
    (trace : FrameTrace Event) (event : Event) :
    (record trace event).toList = trace.toList ++ [event] := by
  rfl

@[simp] theorem append_empty_right {Event : Type u}
    (trace : FrameTrace Event) :
    append trace empty = trace := by
  apply toList_injective
  change trace.toList ++ [] = trace.toList
  have appendNil : ∀ events : List Event, events ++ [] = events := by
    intro events
    induction events with
    | nil => rfl
    | cons head tail ih => exact congrArg (List.cons head) ih
  exact appendNil trace.toList

end Solcore.ContractRuntime.FrameTrace

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTracePrefix`
-/

/-! Non-strict prefix factorization for finite chronological frame traces. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTracePrefixProperties`
-/

/-! Canonical witnesses and transitivity for ordered trace prefixes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace

universe u

theorem empty_isPrefixOf {Event : Type u}
    (trace : FrameTrace Event) :
    IsPrefixOf empty trace :=
  ⟨trace, (append_empty_left trace).symm⟩

theorem isPrefixOf_refl {Event : Type u}
    (trace : FrameTrace Event) :
    IsPrefixOf trace trace :=
  ⟨empty, (append_empty_right trace).symm⟩

theorem isPrefixOf_append {Event : Type u}
    (earlier fragment : FrameTrace Event) :
    IsPrefixOf earlier (append earlier fragment) :=
  ⟨fragment, rfl⟩

theorem isPrefixOf_trans
    {Event : Type u} {first second third : FrameTrace Event}
    (firstSecond : IsPrefixOf first second)
    (secondThird : IsPrefixOf second third) :
    IsPrefixOf first third := by
  rcases firstSecond with ⟨middleFragment, rfl⟩
  rcases secondThird with ⟨lastFragment, rfl⟩
  exact ⟨append middleFragment lastFragment,
    append_assoc first middleFragment lastFragment⟩

end Solcore.ContractRuntime.FrameTrace

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTraceExtension`
-/

/-! Event-only incremental extension from one indexed earlier frame trace. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTraceExtensionProperties`
-/

/-! Observation laws for indexed incremental frame-trace extension. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace.ExtensionFrom

universe u

@[simp] theorem toTrace_start
    {Event : Type u} (earlier : FrameTrace Event) :
    (start earlier).toTrace = earlier := by
  change FrameTrace.append earlier FrameTrace.empty = earlier
  exact FrameTrace.append_empty_right earlier

end Solcore.ContractRuntime.FrameTrace.ExtensionFrom
end

section
-- leanmerge: from Solcore.ContractRuntime.FrameStateResolution
/-!
## Consolidated module: `Solcore.ContractRuntime.FrameStateResolutionProperties`
-/

set_option autoImplicit false

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameOutcome

universe u

@[simp] theorem resolvedWorldState?_returned
    {TrapReason : Type u}
    (checkpoint working : WorldState)
    (data : Bytes) :
    resolvedWorldState? checkpoint working
      (FrameOutcome.returned (TrapReason := TrapReason) data) = some working := by
  rfl

@[simp] theorem resolvedWorldState?_reverted
    {TrapReason : Type u}
    (checkpoint working : WorldState)
    (data : Bytes) :
    resolvedWorldState? checkpoint working
      (FrameOutcome.reverted (TrapReason := TrapReason) data) = some checkpoint := by
  rfl

@[simp] theorem resolvedWorldState?_trapped
    {TrapReason : Type u}
    (checkpoint working : WorldState)
    (reason : TrapReason) :
    resolvedWorldState? checkpoint working (.trapped reason) = none := by
  rfl

end Solcore.ContractRuntime.FrameOutcome
end

section
-- leanmerge: from Solcore.ContractRuntime.FrameRun
/-! Frame-run results, continuation, effect resolution, and their laws. -/

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResult`
-/

/-! The minimal state-and-outcome payload produced by one frame run. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResultProperties`
-/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u

@[simp] theorem resolvedWorldState?_returned
    {TrapReason : Type u}
    (checkpoint working : WorldState) (data : Bytes) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .returned data⟩ : FrameRunResult TrapReason) =
      some working := by
  rfl

@[simp] theorem resolvedWorldState?_reverted
    {TrapReason : Type u}
    (checkpoint working : WorldState) (data : Bytes) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .reverted data⟩ : FrameRunResult TrapReason) =
      some checkpoint := by
  rfl

@[simp] theorem resolvedWorldState?_trapped
    {TrapReason : Type u}
    (checkpoint working : WorldState) (reason : TrapReason) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .trapped reason⟩ : FrameRunResult TrapReason) = none := by
  rfl

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResultTrapReasonMap`
-/

/-! Working-state-preserving mapping of frame-run trap-reason types. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResultTrapReasonMapProperties`
-/

/-! Construction, projection, and composition laws for frame-result mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w

@[simp] theorem mapTrapReason_mk
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (working : WorldState) (outcome : FrameOutcome TrapReason) :
    mapTrapReason mapReason ⟨working, outcome⟩ =
      (⟨working, outcome.mapTrapReason mapReason⟩ :
        FrameRunResult MappedTrapReason) := by
  rfl

@[simp] theorem working_mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    (mapTrapReason mapReason result).working = result.working := by
  rfl

@[simp] theorem outcome_mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    (mapTrapReason mapReason result).outcome =
      result.outcome.mapTrapReason mapReason := by
  rfl

@[simp] theorem mapTrapReason_id
    {TrapReason : Type u} (result : FrameRunResult TrapReason) :
    mapTrapReason (fun reason => reason) result = result := by
  cases result with
  | mk working outcome =>
      rw [mapTrapReason_mk, FrameOutcome.mapTrapReason_id]

@[simp] theorem mapTrapReason_comp
    {TrapReason : Type u}
    {IntermediateTrapReason : Type v}
    {MappedTrapReason : Type w}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    mapTrapReason second (mapTrapReason first result) =
      mapTrapReason (fun reason => second (first reason)) result := by
  cases result with
  | mk working outcome =>
      rw [mapTrapReason_mk, mapTrapReason_mk, mapTrapReason_mk,
        FrameOutcome.mapTrapReason_comp]

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunEffectResolution`
-/

/-! Synchronized resolution of one frame's WorldState and effect journal. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunContinuation`
-/

/-! Caller-owned continuation after synchronized frame resolution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunContinuationProperties`
-/

/-! Constructor laws for caller-owned frame continuation. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w x

@[simp] theorem continueWithResolvedStateAndEffects?_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    continueWithResolvedStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) next =
      next (workingWorld, effectWorking) := by
  rfl

@[simp] theorem continueWithResolvedStateAndEffects?_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    continueWithResolvedStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) next =
      next (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩) := by
  rfl

@[simp] theorem continueWithResolvedStateAndEffects?_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    continueWithResolvedStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.trapped reason⟩ :
        FrameRunResult TrapReason) next = none := by
  rfl

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunEffectResolutionProperties`
-/

/-! Laws for synchronized frame state and effect resolution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w

@[simp] theorem resolvedWorldStateAndEffects?_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) =
      some (workingWorld, effectWorking) := by
  rfl

@[simp] theorem resolvedWorldStateAndEffects?_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) =
      some (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩) := by
  rfl

@[simp] theorem resolvedWorldStateAndEffects?_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.trapped reason⟩ : FrameRunResult TrapReason) =
      none := by
  rfl

theorem resolvedWorldStateAndEffects?_worldState
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option.map Prod.fst
      (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint
        effectWorking result) =
      result.resolvedWorldState? stateCheckpoint := by
  cases result with
  | mk working outcome => cases outcome <;> rfl

theorem resolvedWorldStateAndEffects?_effects
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option.map Prod.snd
      (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint
        effectWorking result) =
      FrameEffectJournal.resolved? effectCheckpoint effectWorking result.outcome := by
  cases result with
  | mk working outcome => cases outcome <;> rfl

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunEffectCompositionProperties`
-/

/-! Nested composition laws for synchronized frame state and effects. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w

theorem resolvedWorldStateAndEffects?_child_return_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentStateCheckpoint childStateCheckpoint childStateWorking : WorldState)
    (parentEffectCheckpoint childEffectCheckpoint childEffectWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolvedWorldStateAndEffects?
      childStateCheckpoint childEffectCheckpoint childEffectWorking
      (⟨childStateWorking, FrameOutcome.returned
        (TrapReason := TrapReason) childData⟩ : FrameRunResult TrapReason)).bind
        (fun childResolved => resolvedWorldStateAndEffects?
          parentStateCheckpoint parentEffectCheckpoint childResolved.2
          (⟨childResolved.1, FrameOutcome.reverted
            (TrapReason := TrapReason) parentData⟩ : FrameRunResult TrapReason)) =
      some (parentStateCheckpoint,
        ⟨parentEffectCheckpoint.rollback, childEffectWorking.trace⟩) := by
  rfl

theorem resolvedWorldStateAndEffects?_child_revert_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentStateCheckpoint childStateCheckpoint childStateWorking : WorldState)
    (parentEffectCheckpoint childEffectCheckpoint childEffectWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolvedWorldStateAndEffects?
      childStateCheckpoint childEffectCheckpoint childEffectWorking
      (⟨childStateWorking, FrameOutcome.reverted
        (TrapReason := TrapReason) childData⟩ : FrameRunResult TrapReason)).bind
        (fun childResolved => resolvedWorldStateAndEffects?
          parentStateCheckpoint parentEffectCheckpoint childResolved.2
          (⟨childResolved.1, FrameOutcome.reverted
            (TrapReason := TrapReason) parentData⟩ : FrameRunResult TrapReason)) =
      some (parentStateCheckpoint,
        ⟨parentEffectCheckpoint.rollback, childEffectWorking.trace⟩) := by
  rfl

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunEffectContinuationProperties`
-/

/-! Continuation laws for resolved synchronized frame state and effects. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w x

theorem resolvedWorldStateAndEffects?_returned_bind
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩ :
        FrameRunResult TrapReason)).bind next =
      next (workingWorld, effectWorking) := by
  rfl

theorem resolvedWorldStateAndEffects?_reverted_bind
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩ :
        FrameRunResult TrapReason)).bind next =
      next (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩) := by
  rfl

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunEffectTrapPropagationProperties`
-/

/-! Propagation of unresolved traps through synchronized frame continuations. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w x

/-- A trapped synchronized resolution cannot invoke or succeed through a continuation. -/
theorem resolvedWorldStateAndEffects?_trapped_bind
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.trapped reason⟩ :
        FrameRunResult TrapReason)).bind next = none := by
  rfl

end Solcore.ContractRuntime.FrameRunResult
end

section
-- leanmerge: from Solcore.ContractRuntime.FrameContinuationContext
/-! Nominal bundle for one completed frame's continuation inputs. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextProperties`
-/

/-! Coherence of the nominal frame continuation bundle. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x

theorem continue?_eq_continueWithResolvedStateAndEffects?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    context.continue? next =
      context.result.continueWithResolvedStateAndEffects?
        context.stateCheckpoint context.effectCheckpoint context.effectWorking
        next := by
  rfl

end Solcore.ContractRuntime.FrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextTrapReasonMap`
-/

/-! Checkpoint-preserving mapping of continuation-context trap reasons. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextTrapReasonMapProperties`
-/

/-! Construction, projection, and composition laws for context mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x y

@[simp] theorem mapTrapReason_mk
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    mapTrapReason mapReason
        (⟨stateCheckpoint, effectCheckpoint, effectWorking, result⟩ :
          FrameContinuationContext RollbackState TraceState TrapReason) =
      (⟨stateCheckpoint, effectCheckpoint, effectWorking,
        result.mapTrapReason mapReason⟩ :
          FrameContinuationContext RollbackState TraceState MappedTrapReason) := by
  rfl

@[simp] theorem stateCheckpoint_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).stateCheckpoint =
      context.stateCheckpoint := by
  rfl

@[simp] theorem effectCheckpoint_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).effectCheckpoint =
      context.effectCheckpoint := by
  rfl

@[simp] theorem effectWorking_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).effectWorking =
      context.effectWorking := by
  rfl

@[simp] theorem result_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).result =
      context.result.mapTrapReason mapReason := by
  rfl

@[simp] theorem mapTrapReason_id
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    mapTrapReason (fun reason => reason) context = context := by
  cases context with
  | mk stateCheckpoint effectCheckpoint effectWorking result =>
      rw [mapTrapReason_mk, FrameRunResult.mapTrapReason_id]

@[simp] theorem mapTrapReason_comp
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {IntermediateTrapReason : Type y}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    mapTrapReason second (mapTrapReason first context) =
      mapTrapReason (fun reason => second (first reason)) context := by
  cases context with
  | mk stateCheckpoint effectCheckpoint effectWorking result =>
      rw [mapTrapReason_mk, mapTrapReason_mk, mapTrapReason_mk,
        FrameRunResult.mapTrapReason_comp]

end Solcore.ContractRuntime.FrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextContinueTrapReasonMapProperties`
-/

/-! Invariance of continuation results under trap-reason mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x y

@[simp] theorem continue?_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    (mapTrapReason mapReason context).continue? next =
      context.continue? next := by
  cases context with
  | mk stateCheckpoint effectCheckpoint effectWorking result =>
      cases result with
      | mk working outcome =>
          cases outcome <;>
            simp [continue?_eq_continueWithResolvedStateAndEffects?]

end Solcore.ContractRuntime.FrameContinuationContext
end

section
-- leanmerge: from Solcore.ContractRuntime.FrameResolutionResult
/-! Total, first-order resolution of one completed frame. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameResolutionResultProperties`
-/

/-! Constructor laws for total frame resolution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w

@[simp] theorem resolve_returned
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    (⟨stateCheckpoint, effectCheckpoint, effectWorking,
      ⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩⟩ :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      FrameResolutionResult.returned workingWorld effectWorking data := by
  rfl

@[simp] theorem resolve_reverted
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    (⟨stateCheckpoint, effectCheckpoint, effectWorking,
      ⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩⟩ :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      FrameResolutionResult.reverted stateCheckpoint
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩ data := by
  rfl

@[simp] theorem resolve_trapped
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason) :
    (⟨stateCheckpoint, effectCheckpoint, effectWorking,
      ⟨workingWorld, FrameOutcome.trapped reason⟩⟩ :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      FrameResolutionResult.trapped reason := by
  rfl

end Solcore.ContractRuntime.FrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameResolutionResultContinuation`
-/

/-! Caller-owned non-trapping continuation of total frame resolution results. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameResolutionResultContinuationProperties`
-/

/-! Constructor laws for bytes-aware frame resolution continuation. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameResolutionResult

universe u v w x

/-- A returned result selects the return callback with every carried value. -/
@[simp] theorem continue?_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (FrameResolutionResult.returned
      (TrapReason := TrapReason) state effects data).continue?
        onReturned onReverted = onReturned (state, effects) data := by
  rfl

/-- A reverted result selects the revert callback with every carried value. -/
@[simp] theorem continue?_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (FrameResolutionResult.reverted
      (TrapReason := TrapReason) state effects data).continue?
        onReturned onReverted = onReverted (state, effects) data := by
  rfl

/-- A trapped result leaves both non-trapping callbacks unselected. -/
@[simp] theorem continue?_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (reason : TrapReason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (FrameResolutionResult.trapped
      (RollbackState := RollbackState) (TraceState := TraceState) reason).continue?
        onReturned onReverted = (none : Option Next) := by
  rfl

end Solcore.ContractRuntime.FrameResolutionResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameResolutionResultTrapReasonMap`
-/

/-! Caller-supplied pure mapping of total frame-resolution trap reasons. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameResolutionResultTrapReasonMapProperties`
-/

/-! Constructor and composition laws for total-resolution reason mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameResolutionResult

universe u v w x y

@[simp] theorem mapTrapReason_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    mapTrapReason mapReason
        (FrameResolutionResult.returned
          (TrapReason := TrapReason) state effects data) =
      FrameResolutionResult.returned
        (TrapReason := MappedTrapReason) state effects data := by
  rfl

@[simp] theorem mapTrapReason_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    mapTrapReason mapReason
        (FrameResolutionResult.reverted
          (TrapReason := TrapReason) state effects data) =
      FrameResolutionResult.reverted
        (TrapReason := MappedTrapReason) state effects data := by
  rfl

@[simp] theorem mapTrapReason_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (reason : TrapReason) :
    mapTrapReason mapReason
        (FrameResolutionResult.trapped
          (RollbackState := RollbackState) (TraceState := TraceState) reason) =
      FrameResolutionResult.trapped (mapReason reason) := by
  rfl

@[simp] theorem mapTrapReason_id
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (result : FrameResolutionResult RollbackState TraceState TrapReason) :
    mapTrapReason (fun reason => reason) result = result := by
  cases result <;> rfl

@[simp] theorem mapTrapReason_comp
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (result : FrameResolutionResult RollbackState TraceState TrapReason) :
    mapTrapReason second (mapTrapReason first result) =
      mapTrapReason (fun reason => second (first reason)) result := by
  cases result <;> rfl

end Solcore.ContractRuntime.FrameResolutionResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameResolutionResultContinueTrapReasonMapProperties`
-/

/-! Invariance of bytes-aware continuation under result reason mapping. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameResolutionResult

universe u v w x y

/-- Mapping a trapped reason leaves bytes-aware continuation results unchanged. -/
@[simp] theorem continue?_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameResolutionResult RollbackState TraceState TrapReason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (mapTrapReason mapReason result).continue?
        onReturned onReverted =
      result.continue? onReturned onReverted := by
  cases result <;> simp

end Solcore.ContractRuntime.FrameResolutionResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextResolveTrapReasonMapProperties`
-/

/-! Naturality of trap-reason mapping under total frame resolution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x

@[simp] theorem resolve_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    resolve (mapTrapReason mapReason context) =
      FrameResolutionResult.mapTrapReason mapReason (resolve context) := by
  cases context with
  | mk stateCheckpoint effectCheckpoint effectWorking result =>
      cases result with
      | mk working outcome =>
          cases outcome <;> simp

end Solcore.ContractRuntime.FrameContinuationContext

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextResolutionContinuationCoherenceProperties`
-/

/-! Coherence after erasing resolution-result branch and byte observations. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x

/-- Bytes-erasing identical result callbacks recover context continuation. -/
theorem resolve_continue?_ignoreBranchAndBytes
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    context.resolve.continue?
        (fun selected _ => next selected)
        (fun selected _ => next selected) =
      context.continue? next := by
  cases context with
  | mk stateCheckpoint effectCheckpoint effectWorking result =>
      cases result with
      | mk working outcome =>
          cases outcome <;> rfl

end Solcore.ContractRuntime.FrameContinuationContext
end

section
-- leanmerge: from Solcore.ContractRuntime.FrameCheckpointSnapshot
/-! Nominal representation of caller-supplied synchronized checkpoint values. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointSnapshotProperties`
-/

/-! Definitional projections of nominal frame checkpoint snapshots. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointSnapshot

universe u v

/-- Constructing a snapshot retains the caller-supplied state exactly. -/
@[simp] theorem state_fromWorkingPair
    {RollbackState : Type u} {TraceState : Type v}
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    (fromWorkingPair working).state = working.1 := by
  rfl

/-- Constructing a snapshot retains the caller-supplied effects exactly. -/
@[simp] theorem effects_fromWorkingPair
    {RollbackState : Type u} {TraceState : Type v}
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    (fromWorkingPair working).effects = working.2 := by
  rfl

end Solcore.ContractRuntime.FrameCheckpointSnapshot
end

section
-- leanmerge: from Solcore.ContractRuntime.FrameCheckpointedWorkingPair
/-! Structural pairing of one frame checkpoint with independent working values. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairStorageWrite`
-/

/-! Working-world storage writes for checkpointed frame values. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairStorageWriteProperties`
-/

/-! Branch laws for checkpointed working-world storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPair

universe u v

/-- A missing working account makes the lifted write unavailable. -/
@[simp] theorem writeWorkingStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot value : Core.Word)
    (absent : values.working.1.account? address = none) :
    values.writeWorkingStorage? address slot value = none := by
  simp [writeWorkingStorage?, WorldState.writeStorage?, absent]

/-- A present working account changes only the working world state. -/
@[simp] theorem writeWorkingStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (account : Account)
    (slot value : Core.Word)
    (present : values.working.1.account? address = some account) :
    values.writeWorkingStorage? address slot value =
      some ⟨values.checkpoint,
        (values.working.1.putAccount address
          (account.storageWrite slot value), values.working.2)⟩ := by
  simp [writeWorkingStorage?, WorldState.writeStorage?, present]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPair

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairStorageWriteAlgebraProperties`
-/

/-! Sequential storage-write algebra lifted to checkpointed working pairs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPair

universe u v

private theorem writeWorkingStorage?_bind_eq_map_bind
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (firstAddress : Address) (firstSlot firstValue : Core.Word)
    (secondAddress : Address) (secondSlot secondValue : Core.Word) :
    (values.writeWorkingStorage? firstAddress firstSlot firstValue).bind
        (fun next =>
          next.writeWorkingStorage? secondAddress secondSlot secondValue) =
      ((values.working.1.writeStorage?
          firstAddress firstSlot firstValue).bind
        (fun state =>
          state.writeStorage? secondAddress secondSlot secondValue)).map
        (fun state =>
          ⟨values.checkpoint, (state, values.working.2)⟩) := by
  simp only [writeWorkingStorage?, Option.bind_map, Option.map_bind]
  rfl

/-- A later write to the same address and slot supersedes an earlier write. -/
theorem writeWorkingStorage?_overwrite
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot first second : Core.Word) :
    (values.writeWorkingStorage? address slot first).bind
        (fun next => next.writeWorkingStorage? address slot second) =
      values.writeWorkingStorage? address slot second := by
  rw [writeWorkingStorage?_bind_eq_map_bind]
  simp [writeWorkingStorage?]

/-- Writes to distinct slots at one address commute. -/
theorem writeWorkingStorage?_commute_slots
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (values.writeWorkingStorage? address leftSlot leftValue).bind
        (fun next =>
          next.writeWorkingStorage? address rightSlot rightValue) =
      (values.writeWorkingStorage? address rightSlot rightValue).bind
        (fun next =>
          next.writeWorkingStorage? address leftSlot leftValue) := by
  rw [writeWorkingStorage?_bind_eq_map_bind]
  rw [writeWorkingStorage?_bind_eq_map_bind]
  rw [WorldState.writeStorage?_commute_slots
    values.working.1 address leftSlot leftValue rightSlot rightValue different]

/-- Writes to distinct addresses commute. -/
theorem writeWorkingStorage?_commute_addresses
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (leftAddress rightAddress : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftAddress ≠ rightAddress) :
    (values.writeWorkingStorage? leftAddress leftSlot leftValue).bind
        (fun next =>
          next.writeWorkingStorage? rightAddress rightSlot rightValue) =
      (values.writeWorkingStorage? rightAddress rightSlot rightValue).bind
        (fun next =>
          next.writeWorkingStorage? leftAddress leftSlot leftValue) := by
  rw [writeWorkingStorage?_bind_eq_map_bind]
  rw [writeWorkingStorage?_bind_eq_map_bind]
  rw [WorldState.writeStorage?_commute_addresses
    values.working.1 leftAddress rightAddress leftSlot leftValue
      rightSlot rightValue different]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPair
end

section
-- leanmerge: from Solcore.ContractRuntime.FrameContinuationContextFromCheckpointedWorkingPair
/-! Pure construction of continuation inputs from checkpointed working values. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextFromCheckpointedWorkingPairProperties`
-/

/-! Projections of continuation contexts built from checkpointed working values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w

/-- Construction retains the checkpoint state exactly. -/
@[simp] theorem stateCheckpoint_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).stateCheckpoint =
      values.checkpoint.state := by
  rfl

/-- Construction retains the checkpoint effects exactly. -/
@[simp] theorem effectCheckpoint_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).effectCheckpoint =
      values.checkpoint.effects := by
  rfl

/-- Construction retains the working effects exactly. -/
@[simp] theorem effectWorking_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).effectWorking =
      values.working.2 := by
  rfl

/-- Construction pairs the working state with the supplied outcome exactly. -/
@[simp] theorem result_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).result =
      ⟨values.working.1, outcome⟩ := by
  rfl

end Solcore.ContractRuntime.FrameContinuationContext
end

section
-- leanmerge: from Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress
/-! A caller-addressed storage boundary over checkpointed working values. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressProperties`
-/

/-! Branch laws for address-bound checkpointed working storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- An absent working account makes the address-bound write unavailable. -/
@[simp] theorem writeStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.writeStorage? slot value = none := by
  simp [writeStorage?,
    FrameCheckpointedWorkingPair.writeWorkingStorage?_of_absent,
    absent]

/-- A present working account updates only the addressed working storage. -/
@[simp] theorem writeStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account) (slot value : Core.Word)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.writeStorage? slot value =
      some
        ⟨context.storageAddress,
          ⟨context.values.checkpoint,
            (context.values.working.1.putAccount context.storageAddress
              (account.storageWrite slot value),
              context.values.working.2)⟩⟩ := by
  simp [writeStorage?,
    FrameCheckpointedWorkingPair.writeWorkingStorage?_of_present,
    present]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageRead`
-/

/-! Working-storage reads through a retained frame storage address. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageReadProperties`
-/

/-! Branch laws for address-bound working storage reads. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- An absent addressed working Account makes the read unavailable. -/
@[simp] theorem readStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot : Core.Word)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.readStorage? slot = none := by
  exact WorldState.readStorage?_of_absent context.values.working.1
    context.storageAddress slot absent

/-- A present addressed working Account supplies its zero-default slot read. -/
@[simp] theorem readStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account)
    (slot : Core.Word)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.readStorage? slot = some (account.storageRead slot) := by
  exact WorldState.readStorage?_of_present context.values.working.1
    context.storageAddress account slot present

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageReadWriteProperties`
-/

/-! Read-after-write laws for address-bound working storage. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- Reading the written slot observes the new value after a successful write. -/
@[simp] theorem readStorage?_writeStorage?_same
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.readStorage? slot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => some value) := by
  simp [writeStorage?, FrameCheckpointedWorkingPair.writeWorkingStorage?,
    readStorage?, Function.comp_def]

/-- Writing another slot preserves the selected working-storage read. -/
@[simp] theorem readStorage?_writeStorage?_other_slot
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage? writtenSlot value).map
        (fun next => next.readStorage? readSlot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.readStorage? readSlot) := by
  simp [writeStorage?, FrameCheckpointedWorkingPair.writeWorkingStorage?,
    readStorage?, Function.comp_def, different]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageWriteAlgebraProperties`
-/

/-! Sequential storage-write algebra through one retained storage address. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

private theorem writeStorage?_bind_eq_map_bind
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (firstSlot firstValue secondSlot secondValue : Core.Word) :
    (context.writeStorage? firstSlot firstValue).bind
        (fun next => next.writeStorage? secondSlot secondValue) =
      ((context.values.writeWorkingStorage?
          context.storageAddress firstSlot firstValue).bind
        (fun values =>
          values.writeWorkingStorage?
            context.storageAddress secondSlot secondValue)).map
        (fun values => ⟨context.storageAddress, values⟩) := by
  simp only [writeStorage?, Option.bind_map, Option.map_bind]
  rfl

/-- A later write to the retained address and slot supersedes an earlier one. -/
theorem writeStorage?_overwrite
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot first second : Core.Word) :
    (context.writeStorage? slot first).bind
        (fun next => next.writeStorage? slot second) =
      context.writeStorage? slot second := by
  rw [writeStorage?_bind_eq_map_bind]
  unfold writeStorage?
  rw [FrameCheckpointedWorkingPair.writeWorkingStorage?_overwrite]

/-- Writes to distinct slots at the retained address commute. -/
theorem writeStorage?_commute_slots
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (context.writeStorage? leftSlot leftValue).bind
        (fun next => next.writeStorage? rightSlot rightValue) =
      (context.writeStorage? rightSlot rightValue).bind
        (fun next => next.writeStorage? leftSlot leftValue) := by
  rw [writeStorage?_bind_eq_map_bind]
  rw [writeStorage?_bind_eq_map_bind]
  rw [FrameCheckpointedWorkingPair.writeWorkingStorage?_commute_slots
    context.values context.storageAddress leftSlot leftValue
      rightSlot rightValue different]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageWriteCoherenceProperties`
-/

/-! Values coherence for retained-address and address-parameterized writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- Forgetting the retained selector recovers the underlying values write. -/
@[simp] theorem values_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map (fun next => next.values) =
      context.values.writeWorkingStorage?
        context.storageAddress slot value := by
  cases result : context.values.writeWorkingStorage?
      context.storageAddress slot value <;>
    simp [writeStorage?, result]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageWritePreservationProperties`
-/

/-! Stage-preserving structural observations of address-bound storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- A conditional write retains the exact stored address in its success branch. -/
@[simp] theorem storageAddress_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.storageAddress) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.storageAddress) := by
  cases present :
      context.values.working.1.account? context.storageAddress <;>
    simp [present]

/-- A conditional write retains the exact checkpoint in its success branch. -/
@[simp] theorem checkpoint_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.values.checkpoint) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.values.checkpoint) := by
  cases present :
      context.values.working.1.account? context.storageAddress <;>
    simp [present]

/-- A conditional write retains the exact working effects in its success branch. -/
@[simp] theorem workingEffects_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.values.working.2) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.values.working.2) := by
  cases present :
      context.values.working.1.account? context.storageAddress <;>
    simp [present]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress
end

section
-- leanmerge: from Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
/-! Evidence that an address-bound working context contains its selected Account. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountProperties`
-/

/-! Branch laws for refining an address-bound context by working Account presence. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- A missing selected working Account makes refinement unavailable. -/
@[simp] theorem withPresentStorageAccount?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.withPresentStorageAccount? = none := by
  unfold withPresentStorageAccount?
  split <;> simp_all

/-- A present selected working Account produces its exact evidence carrier. -/
@[simp] theorem withPresentStorageAccount?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.withPresentStorageAccount? =
      some ⟨context, account, present⟩ := by
  unfold withPresentStorageAccount?
  split
  · simp_all
  · rename_i account' observed
    have same : account' = account :=
      Option.some.inj (observed.symm.trans present)
    subst account'
    rfl

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead`
-/

/-! Total storage reads from a proven-present selected working Account. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadProperties`
-/

/-! Coherence between proven-present total reads and address-bound optional reads. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- The underlying optional context read returns the total refined read. -/
@[simp] theorem context_readStorage?_eq_some_readStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) :
    context.context.readStorage? slot = some (context.readStorage slot) := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.readStorage?_of_present
      context.context context.storageAccount slot context.storageAccount_present

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite`
-/

/-! Total storage writes through a proven-present selected working Account. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadWriteProperties`
-/

/-! Read-after-write laws for proven-present total working storage. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Reading the written slot observes the new total-write value. -/
@[simp] theorem readStorage_writeStorage_same
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).readStorage slot = value := by
  exact Account.storageRead_storageWrite_same
    context.storageAccount slot value

/-- A total write to another slot preserves the prior total read. -/
@[simp] theorem readStorage_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).readStorage readSlot =
      context.readStorage readSlot := by
  exact Account.storageRead_storageWrite_other
    context.storageAccount writtenSlot value readSlot different

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProperties`
-/

/-! Coherence between proven-present total and address-bound optional writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- The underlying optional write returns the total write's updated context. -/
@[simp] theorem context_writeStorage?_eq_some_writeStorage_context
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    context.context.writeStorage? slot value =
      some (context.writeStorage slot value).context := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.writeStorage?_of_present
      context.context context.storageAccount slot value
      context.storageAccount_present

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteAlgebraProperties`
-/

/-! Algebraic laws for proven-present total working-storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A later total write to the same slot supersedes the earlier write. -/
@[simp] theorem writeStorage_overwrite
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot first second : Core.Word) :
    (context.writeStorage slot first).writeStorage slot second =
      context.writeStorage slot second := by
  simp [writeStorage]

/-- Total writes to distinct slots commute. -/
theorem writeStorage_commute_slots
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (context.writeStorage leftSlot leftValue).writeStorage
        rightSlot rightValue =
      (context.writeStorage rightSlot rightValue).writeStorage
        leftSlot leftValue := by
  simp [writeStorage,
    Account.storageWrite_commute context.storageAccount
      leftSlot leftValue rightSlot rightValue different]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjectionProperties`
-/

/-! Data projections of proven-present total working-storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A total write retains the exact storage selector. -/
@[simp] theorem storageAddress_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).context.storageAddress =
      context.context.storageAddress := by
  rfl

/-- A total write retains the exact checkpoint. -/
@[simp] theorem checkpoint_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).context.values.checkpoint =
      context.context.values.checkpoint := by
  rfl

/-- A total write retains the exact working effects. -/
@[simp] theorem workingEffects_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).context.values.working.2 =
      context.context.values.working.2 := by
  rfl

/-- A total write stores the exact lower-level Account update. -/
@[simp] theorem storageAccount_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).storageAccount =
      context.storageAccount.storageWrite slot value := by
  rfl

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteIsolationProperties`
-/

/-! Non-selected working Account isolation for proven-present total writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A total storage write preserves every non-selected working Account. -/
@[simp] theorem workingAccount?_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (otherAddress : Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    (context.writeStorage slot value).context.values.working.1.account?
        otherAddress =
      context.context.values.working.1.account? otherAddress := by
  exact WorldState.account?_putAccount_other
    context.context.values.working.1 context.context.storageAddress otherAddress
    (context.storageAccount.storageWrite slot value) different

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWritePresenceProperties`
-/

/-! Sparse storage presence after proven-present total writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Writing zero removes the selected sparse-storage entry. -/
theorem storageValue?_writeStorage_zero
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) :
    (context.writeStorage slot Core.Word.zero).storageAccount.storageValue?
        slot = none := by
  rw [storageAccount_writeStorage]
  exact Account.storageValue?_storageWrite_zero context.storageAccount slot

/-- Writing a nonzero word creates the corresponding sparse-storage entry. -/
theorem storageValue?_writeStorage_nonzero
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (nonzero : value ≠ Core.Word.zero) :
    (context.writeStorage slot value).storageAccount.storageValue? slot =
      some value := by
  rw [storageAccount_writeStorage]
  exact Account.storageValue?_storageWrite_nonzero
    context.storageAccount slot value nonzero

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteCodeProperties`
-/

/-! Checked-code preservation across total working-storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A storage write preserves checked code at every working-state address. -/
@[simp] theorem workingCode?_writeStorage
    {RollbackState : Type u}
    {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (codeAddress : Address) :
    (context.writeStorage slot value).context.values.working.1.code?
        codeAddress =
      context.context.values.working.1.code? codeAddress := by
  change
    ((context.context.values.working.1.putAccount
        context.context.storageAddress
        (context.storageAccount.storageWrite slot value)).account?
      codeAddress).bind (fun account => account.code?) =
    (context.context.values.working.1.account? codeAddress).bind
      (fun account => account.code?)
  by_cases same : codeAddress = context.context.storageAddress
  · subst codeAddress
    rw [WorldState.account?_putAccount_same]
    rw [context.storageAccount_present]
    simp
  · rw [WorldState.account?_putAccount_other _ _ _ _ same]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteSparsePreservationProperties`
-/

/-! Distinct-slot sparse-storage preservation for proven-present total writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A total write preserves the optional sparse entry at every other slot. -/
theorem storageValue?_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value otherSlot : Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).storageAccount.storageValue?
        otherSlot =
      context.storageAccount.storageValue? otherSlot := by
  rw [storageAccount_writeStorage]
  exact Account.storageValue?_storageWrite_other
    context.storageAccount writtenSlot value otherSlot different

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteRefinementCoherenceProperties`
-/

/-! Canonical refinement coherence for proven-present optional storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Optional write followed by refinement recovers the total write result. -/
theorem context_writeStorage?_bind_withPresentStorageAccount?_eq_some_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.context.writeStorage? slot value).bind
        FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount? =
      some (context.writeStorage slot value) := by
  rw [context_writeStorage?_eq_some_writeStorage_context]
  simp only [Option.bind_some]
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_present
      (context.writeStorage slot value).context
      (context.writeStorage slot value).storageAccount
      (context.writeStorage slot value).storageAccount_present

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
end
