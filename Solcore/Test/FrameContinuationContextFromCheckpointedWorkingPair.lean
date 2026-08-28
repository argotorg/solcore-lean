import Solcore.Semantics.FrameContinuationContextFromCheckpointedWorkingPair

/-! Definition-only compile regressions for continuation-context construction. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

universe u v w

private example
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    FrameContinuationContext.fromCheckpointedWorkingPair values outcome =
      ({
        stateCheckpoint := values.checkpoint.state
        effectCheckpoint := values.checkpoint.effects
        effectWorking := values.working.2
        result := ⟨values.working.1, outcome⟩
      } : FrameContinuationContext RollbackState TraceState TrapReason) := by
  rfl

private inductive Reason where
  | marker
  | other

private def address : Address := ⟨0x12, by decide⟩
private def slot : Core.Word := ⟨0x34, by decide⟩
private def checkpointValue : Core.Word := ⟨0x56, by decide⟩
private def workingValue : Core.Word := ⟨0x78, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address
    (Account.empty.storageWrite slot value)

private def checkpointState : WorldState := stateWith checkpointValue
private def workingState : WorldState := stateWith workingValue

private def checkpointEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨10, [1]⟩

private def workingEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨20, [1, 2]⟩

private def values : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨⟨checkpointState, checkpointEffects⟩, (workingState, workingEffects)⟩

private def outcome : FrameOutcome Reason :=
  .returned [0x12, 0xff].toByteArray

private def context : FrameContinuationContext Nat (List Nat) Reason :=
  FrameContinuationContext.fromCheckpointedWorkingPair values outcome

private example :
    (context.stateCheckpoint, context.effectCheckpoint, context.effectWorking) =
      (checkpointState, checkpointEffects, workingEffects) := by
  rfl

private example :
    context.result =
      ⟨workingState, FrameOutcome.returned [0x12, 0xff].toByteArray⟩ := by
  rfl

end Tests
