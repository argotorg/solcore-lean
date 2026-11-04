import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.WorldState
import Solcore.Core.Syntax

/-!
# Frames

One contract frame. `FrameOutcome` is how it halts and `FrameRunResult` its result.
`FrameEffectJournal` splits its effects into what a rollback undoes and what survives, and
`FrameTrace` holds the observations. `FrameContinuationContext` and `FrameResolutionResult` resolve
a finished frame against its checkpoint.

`FrameCheckpointSnapshot` and `FrameCheckpointedWorkingPair` are the checkpoint and working values.
`FrameCheckpointedWorkingPairWithStorageAddress` and
`FrameCheckpointedWorkingPairWithPresentStorageAccount` add what storage access needs.
-/

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameOutcome
/-! Internal, syntax-independent outcomes produced when one contract frame halts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

/-- The three ways in which execution of one contract frame can halt. -/
inductive FrameHaltKind where
  | returned
  | reverted
  | trapped
  deriving Repr, BEq, DecidableEq

/--
The result of halting one contract frame. Successful return data, revert data,
and a trap reason are kept in distinct constructors so invalid combinations
cannot be represented.
-/
inductive FrameOutcome (TrapReason : Type u) : Type u where
  | returned (returndata : Bytes)
  | reverted (revertdata : Bytes)
  | trapped (reason : TrapReason)
  deriving BEq, DecidableEq

namespace FrameOutcome

/-- Classify an outcome without inspecting its payload. -/
def kind {TrapReason : Type u} : FrameOutcome TrapReason → FrameHaltKind
  | .returned _ => .returned
  | .reverted _ => .reverted
  | .trapped _ => .trapped

/-- Return the successful return data, and `none` for other halt kinds. -/
def returndata? {TrapReason : Type u} : FrameOutcome TrapReason → Option Bytes
  | .returned data => some data
  | .reverted _
  | .trapped _ => none

/-- Return the revert data, and `none` for other halt kinds. -/
def revertdata? {TrapReason : Type u} : FrameOutcome TrapReason → Option Bytes
  | .reverted data => some data
  | .returned _
  | .trapped _ => none

/-- Return the trap reason, and `none` for returned or reverted outcomes. -/
def trapReason? {TrapReason : Type u} :
    FrameOutcome TrapReason → Option TrapReason
  | .trapped reason => some reason
  | .returned _
  | .reverted _ => none

end FrameOutcome

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameOutcomeProperties`
-/

/-! Focused laws for syntax-independent contract frame halt outcomes. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameOutcomeTrapReasonMap`
-/

/-! Caller-supplied pure mapping of frame trap-reason types. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameOutcome

universe u v

/-- Preserve halt kind and byte payload while mapping only trapped reasons. -/
def mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (outcome : FrameOutcome TrapReason) :
    FrameOutcome MappedTrapReason :=
  match outcome with
  | .returned data => .returned data
  | .reverted data => .reverted data
  | .trapped reason => .trapped (mapReason reason)

end Solcore.ContractRuntime.FrameOutcome
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameEffectJournal
/-! Generic rollback-scoped state and revert-surviving trace policy. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

/-- Opaque rollback-scoped state paired with an accumulated trace snapshot. -/
structure FrameEffectJournal
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  rollback : RollbackState
  trace : TraceState

namespace FrameEffectJournal

/-- Resolve return and revert journals while leaving trap disposition open. -/
def resolved?
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    Option (FrameEffectJournal RollbackState TraceState) :=
  match outcome with
  | .returned _ => some working
  | .reverted _ => some ⟨checkpoint.rollback, working.trace⟩
  | .trapped _ => none

end FrameEffectJournal

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameTrace
/-! Finite chronological traces for opt-in frame-effect observations. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

/-- A finite chronological sequence built through explicit extension operations. -/
structure FrameTrace (Event : Type u) : Type u where private mk ::
  private events : List Event

namespace FrameTrace

/-- The trace containing no events. -/
def empty {Event : Type u} : FrameTrace Event :=
  ⟨[]⟩

/-- Observe events from earliest to latest. -/
def toList {Event : Type u} (trace : FrameTrace Event) : List Event :=
  trace.events

/-- Place every event in the earlier trace before every event in the later trace. -/
def append {Event : Type u}
    (earlier later : FrameTrace Event) : FrameTrace Event :=
  ⟨earlier.events ++ later.events⟩

/-- Record one event after every event already in the trace. -/
def record {Event : Type u}
    (trace : FrameTrace Event) (event : Event) : FrameTrace Event :=
  ⟨trace.events ++ [event]⟩

end FrameTrace

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTraceProperties`
-/

/-! Observation and extension algebra for finite chronological frame traces. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace

universe u

theorem toList_injective {Event : Type u} :
    Function.Injective (toList : FrameTrace Event → List Event) := by
  intro left right same
  cases left
  cases right
  simp only [toList] at same
  congr

@[simp] theorem append_empty_left {Event : Type u}
    (trace : FrameTrace Event) :
    append empty trace = trace := by
  cases trace
  rfl

theorem append_assoc {Event : Type u}
    (first second third : FrameTrace Event) :
    append (append first second) third = append first (append second third) := by
  apply toList_injective
  change (first.toList ++ second.toList) ++ third.toList =
    first.toList ++ (second.toList ++ third.toList)
  have appendAssoc : ∀ left middle right : List Event,
      (left ++ middle) ++ right = left ++ (middle ++ right) := by
    intro left middle right
    induction left with
    | nil => rfl
    | cons head tail ih => exact congrArg (List.cons head) ih
  exact appendAssoc first.toList second.toList third.toList

end Solcore.ContractRuntime.FrameTrace

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTracePrefix`
-/

/-! Non-strict prefix factorization for finite chronological frame traces. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace

universe u

/-- An earlier trace whose ordered extension equals the later trace. -/
def IsPrefixOf {Event : Type u}
    (earlier later : FrameTrace Event) : Prop :=
  ∃ fragment, later = append earlier fragment

end Solcore.ContractRuntime.FrameTrace

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTracePrefixProperties`
-/

/-! Canonical witnesses and transitivity for ordered trace prefixes. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTraceExtension`
-/

/-! Event-only incremental extension from one indexed earlier frame trace. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace

universe u

/-- An incremental trace fragment whose earlier trace is fixed by its type. -/
structure ExtensionFrom
    {Event : Type u} (earlier : FrameTrace Event) : Type u where private mk ::
  private fragment : FrameTrace Event

namespace ExtensionFrom

/-- Begin an extension without adding an event. -/
def start {Event : Type u}
    (earlier : FrameTrace Event) : ExtensionFrom earlier :=
  ⟨FrameTrace.empty⟩

/-- Observe the fixed earlier trace followed by every recorded event. -/
def toTrace {Event : Type u} {earlier : FrameTrace Event}
    (extension : ExtensionFrom earlier) : FrameTrace Event :=
  FrameTrace.append earlier extension.fragment

/-- Record one event at the chronological tail of the extension. -/
def record {Event : Type u} {earlier : FrameTrace Event}
    (extension : ExtensionFrom earlier) (event : Event) :
    ExtensionFrom earlier :=
  ⟨FrameTrace.record extension.fragment event⟩

/-- The fixed earlier trace is a prefix of every observed extension. -/
theorem earlier_isPrefixOf_toTrace
    {Event : Type u} {earlier : FrameTrace Event}
    (extension : ExtensionFrom earlier) :
    FrameTrace.IsPrefixOf earlier extension.toTrace :=
  ⟨extension.fragment, rfl⟩

end ExtensionFrom

end Solcore.ContractRuntime.FrameTrace

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTraceExtensionProperties`
-/

/-! Observation laws for indexed incremental frame-trace extension. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace.ExtensionFrom

universe u

@[simp] theorem toTrace_record
    {Event : Type u} {earlier : FrameTrace Event}
    (extension : ExtensionFrom earlier) (event : Event) :
    (extension.record event).toTrace =
      FrameTrace.record extension.toTrace event := by
  refine ExtensionFrom.rec (motive := fun extension =>
    (extension.record event).toTrace =
      FrameTrace.record extension.toTrace event) ?_ extension
  intro fragment
  change FrameTrace.append earlier
      (FrameTrace.append fragment (FrameTrace.record FrameTrace.empty event)) =
    FrameTrace.append (FrameTrace.append earlier fragment)
      (FrameTrace.record FrameTrace.empty event)
  exact (FrameTrace.append_assoc earlier fragment
    (FrameTrace.record FrameTrace.empty event)).symm

end Solcore.ContractRuntime.FrameTrace.ExtensionFrom
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameStateResolution
set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

namespace FrameOutcome

/-- Resolve return and revert states while leaving trap disposition open. -/
def resolvedWorldState?
    {TrapReason : Type u}
    (checkpoint working : WorldState)
    (outcome : FrameOutcome TrapReason) : Option WorldState :=
  match outcome with
  | .returned _ => some working
  | .reverted _ => some checkpoint
  | .trapped _ => none

end FrameOutcome

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameRun
/-! Frame-run results, continuation, effect resolution, and their laws. -/

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResult`
-/

/-! The minimal state-and-outcome payload produced by one frame run. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u

/-- A speculative working state paired with the frame outcome it produced. -/
structure FrameRunResult (TrapReason : Type u) : Type u where
  working : WorldState
  outcome : FrameOutcome TrapReason

namespace FrameRunResult

/-- Resolve a frame result against a checkpoint still owned by the caller. -/
def resolvedWorldState?
    {TrapReason : Type u}
    (checkpoint : WorldState)
    (result : FrameRunResult TrapReason) : Option WorldState :=
  FrameOutcome.resolvedWorldState?
    checkpoint result.working result.outcome

end FrameRunResult

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResultProperties`
-/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResultTrapReasonMap`
-/

/-! Working-state-preserving mapping of frame-run trap-reason types. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v

/-- Preserve the working state while mapping only the result's trapped reason. -/
def mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    FrameRunResult MappedTrapReason :=
  ⟨result.working, result.outcome.mapTrapReason mapReason⟩

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunResultTrapReasonMapProperties`
-/

/-! Construction, projection, and composition laws for frame-result mapping. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunEffectResolution`
-/

/-! Synchronized resolution of one frame's WorldState and effect journal. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w

/-- Resolve state and effects from the same outcome without choosing trap policy. -/
def resolvedWorldStateAndEffects?
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option (WorldState × FrameEffectJournal RollbackState TraceState) :=
  match result.outcome with
  | .returned _ => some (result.working, effectWorking)
  | .reverted _ =>
      some (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩)
  | .trapped _ => none

end Solcore.ContractRuntime.FrameRunResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameRunContinuation`
-/

/-! Caller-owned continuation after synchronized frame resolution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v w x

/-- Resolve caller-supplied state and effects before invoking a continuation. -/
def continueWithResolvedStateAndEffects?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    Option Next :=
  (result.resolvedWorldStateAndEffects?
    stateCheckpoint effectCheckpoint effectWorking).bind next

end Solcore.ContractRuntime.FrameRunResult
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameContinuationContext
/-! Nominal bundle for one completed frame's continuation inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w x

/-- Caller-owned inputs needed to continue after one completed frame. -/
structure FrameContinuationContext
    (RollbackState : Type u) (TraceState : Type v)
    (TrapReason : Type w) : Type (max u v w) where
  stateCheckpoint : WorldState
  effectCheckpoint : FrameEffectJournal RollbackState TraceState
  effectWorking : FrameEffectJournal RollbackState TraceState
  result : FrameRunResult TrapReason

namespace FrameContinuationContext

/-- Continue through the bundled inputs using synchronized frame resolution. -/
def continue?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    Option Next :=
  context.result.continueWithResolvedStateAndEffects?
    context.stateCheckpoint context.effectCheckpoint context.effectWorking next

end FrameContinuationContext

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextProperties`
-/

/-! Coherence of the nominal frame continuation bundle. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameContinuationContextTrapReasonMap`
-/

/-! Checkpoint-preserving mapping of continuation-context trap reasons. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w x

/-- Preserve caller-owned inputs while mapping only the completed result. -/
def mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContext RollbackState TraceState TrapReason) :
    FrameContinuationContext RollbackState TraceState MappedTrapReason :=
  {
    stateCheckpoint := context.stateCheckpoint
    effectCheckpoint := context.effectCheckpoint
    effectWorking := context.effectWorking
    result := context.result.mapTrapReason mapReason
  }

end Solcore.ContractRuntime.FrameContinuationContext
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameResolutionResult
/-! Total, first-order resolution of one completed frame. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

/-- The branch-complete result of resolving one completed frame. -/
inductive FrameResolutionResult
    (RollbackState : Type u) (TraceState : Type v)
    (TrapReason : Type w) : Type (max u v w) where
  | returned
      (state : WorldState)
      (effects : FrameEffectJournal RollbackState TraceState)
      (data : Bytes)
  | reverted
      (state : WorldState)
      (effects : FrameEffectJournal RollbackState TraceState)
      (data : Bytes)
  | trapped (reason : TrapReason)

namespace FrameContinuationContext

/-- Resolve every frame branch without selecting a continuation. -/
def resolve
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    FrameResolutionResult RollbackState TraceState TrapReason :=
  match context.result.outcome with
  | .returned data =>
      .returned context.result.working context.effectWorking data
  | .reverted data =>
      .reverted context.stateCheckpoint
        ⟨context.effectCheckpoint.rollback, context.effectWorking.trace⟩ data
  | .trapped reason => .trapped reason

end FrameContinuationContext

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameResolutionResultProperties`
-/

/-! Constructor laws for total frame resolution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameResolutionResultContinuation`
-/

/-! Caller-owned non-trapping continuation of total frame resolution results. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameResolutionResult

universe u v w x

/-- Continue a resolved return or revert with its synchronized pair and bytes. -/
def continue?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (result : FrameResolutionResult RollbackState TraceState TrapReason)
    (onReturned :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next)
    (onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    Option Next :=
  match result with
  | .returned state effects data => onReturned (state, effects) data
  | .reverted state effects data => onReverted (state, effects) data
  | .trapped _ => none

end Solcore.ContractRuntime.FrameResolutionResult

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameResolutionResultContinuationProperties`
-/

/-! Constructor laws for bytes-aware frame resolution continuation. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameResolutionResultTrapReasonMap`
-/

/-! Caller-supplied pure mapping of total frame-resolution trap reasons. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameResolutionResult

universe u v w x

/-- Preserve resolved return/revert data while mapping only trapped reasons. -/
def mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (result :
      FrameResolutionResult RollbackState TraceState TrapReason) :
    FrameResolutionResult RollbackState TraceState MappedTrapReason :=
  match result with
  | .returned state effects data => .returned state effects data
  | .reverted state effects data => .reverted state effects data
  | .trapped reason => .trapped (mapReason reason)

end Solcore.ContractRuntime.FrameResolutionResult
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameCheckpointSnapshot
/-! Nominal representation of caller-supplied synchronized checkpoint values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/-- Caller-designated synchronized values represented as a frame checkpoint. -/
structure FrameCheckpointSnapshot
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  state : WorldState
  effects : FrameEffectJournal RollbackState TraceState

namespace FrameCheckpointSnapshot

/-- Represent one caller-supplied synchronized working pair as a checkpoint. -/
def fromWorkingPair
    {RollbackState : Type u} {TraceState : Type v}
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    FrameCheckpointSnapshot RollbackState TraceState :=
  ⟨working.1, working.2⟩

end FrameCheckpointSnapshot

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameCheckpointedWorkingPair
/-! Structural pairing of one frame checkpoint with independent working values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/-- One checkpoint snapshot paired with independent state-and-effects working values. -/
structure FrameCheckpointedWorkingPair
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  checkpoint : FrameCheckpointSnapshot RollbackState TraceState
  working : WorldState × FrameEffectJournal RollbackState TraceState

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairStorageWrite`
-/

/-! Working-world storage writes for checkpointed frame values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPair

universe u v

/-- Conditionally update storage in only the working world state. -/
def writeWorkingStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot value : Core.Word) :
    Option (FrameCheckpointedWorkingPair RollbackState TraceState) :=
  (values.working.1.writeStorage? address slot value).map fun state =>
    ⟨values.checkpoint, (state, values.working.2)⟩

end Solcore.ContractRuntime.FrameCheckpointedWorkingPair
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameContinuationContextFromCheckpointedWorkingPair
/-! Pure construction of continuation inputs from checkpointed working values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameContinuationContext

universe u v w

/-- Build continuation inputs from checkpointed working values and an outcome. -/
def fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    FrameContinuationContext RollbackState TraceState TrapReason :=
  {
    stateCheckpoint := values.checkpoint.state
    effectCheckpoint := values.checkpoint.effects
    effectWorking := values.working.2
    result := ⟨values.working.1, outcome⟩
  }

end Solcore.ContractRuntime.FrameContinuationContext
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameCheckpointedWorkingPairWithStorageAddress
/-! A caller-addressed storage boundary over checkpointed working values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/-- A checkpointed working pair with one caller-supplied storage address. -/
structure FrameCheckpointedWorkingPairWithStorageAddress
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  storageAddress : Address
  values : FrameCheckpointedWorkingPair RollbackState TraceState

namespace FrameCheckpointedWorkingPairWithStorageAddress

/-- Write one slot at the stored address in only the working world state. -/
def writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    Option
      (FrameCheckpointedWorkingPairWithStorageAddress
        RollbackState TraceState) :=
  (context.values.writeWorkingStorage?
    context.storageAddress slot value).map fun values =>
      ⟨context.storageAddress, values⟩

end FrameCheckpointedWorkingPairWithStorageAddress

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressProperties`
-/

/-! Branch laws for address-bound checkpointed working storage writes. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageRead`
-/

/-! Working-storage reads through a retained frame storage address. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- Read one slot from the stored address in the working WorldState. -/
def readStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot : Core.Word) : Option Core.Word :=
  context.values.working.1.readStorage? context.storageAddress slot

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsFrameCheckpointedWorkingPairWithPresentStorageAccount
/-! Evidence that an address-bound working context contains its selected Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/-- An address-bound working context paired with its present selected Account. -/
structure FrameCheckpointedWorkingPairWithPresentStorageAccount
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  context :
    FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState
  storageAccount : Account
  storageAccount_present :
    context.values.working.1.account? context.storageAddress =
      some storageAccount

namespace FrameCheckpointedWorkingPairWithStorageAddress

/-- Refine a context exactly when its selected working Account is present. -/
def withPresentStorageAccount?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState) :
    Option
      (FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState) :=
  match present :
      context.values.working.1.account? context.storageAddress with
  | none => none
  | some account => some ⟨context, account, present⟩

end FrameCheckpointedWorkingPairWithStorageAddress

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountProperties`
-/

/-! Branch laws for refining an address-bound context by working Account presence. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead`
-/

/-! Total storage reads from a proven-present selected working Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Read one slot from the proven-present selected working Account. -/
def readStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) : Core.Word :=
  context.storageAccount.storageRead slot

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadProperties`
-/

/-! Coherence between proven-present total reads and address-bound optional reads. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite`
-/

/-! Total storage writes through a proven-present selected working Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Update the selected Account and its working-state entry in lockstep. -/
def writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    FrameCheckpointedWorkingPairWithPresentStorageAccount
      RollbackState TraceState :=
  let storageAccount := context.storageAccount.storageWrite slot value
  let nextContext :
      FrameCheckpointedWorkingPairWithStorageAddress
        RollbackState TraceState :=
    ⟨context.context.storageAddress,
      ⟨context.context.values.checkpoint,
        (context.context.values.working.1.putAccount
          context.context.storageAddress storageAccount,
          context.context.values.working.2)⟩⟩
  ⟨nextContext, storageAccount, by
    simp [nextContext, WorldState.putAccount, WorldState.account?]⟩

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
end
