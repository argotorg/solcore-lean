import Solcore.ContractRuntime.FrameContinuationContext

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
