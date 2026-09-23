import Solcore.ContractRuntime.FrameCheckpointedWorkingPair

/-! Definition-only compile regressions for checkpointed working pairs. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

universe u v

private example
    {RollbackState : Type u} {TraceState : Type v}
    (checkpoint : FrameCheckpointSnapshot RollbackState TraceState)
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    (⟨checkpoint, working⟩ :
      FrameCheckpointedWorkingPair RollbackState TraceState) =
      FrameCheckpointedWorkingPair.mk checkpoint working := by
  rfl

private def address : Address := ⟨0x12, by decide⟩
private def slot : Core.Word := ⟨0x34, by decide⟩
private def checkpointValue : Core.Word := ⟨0x56, by decide⟩
private def workingValue : Core.Word := ⟨0x78, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address
    (Account.empty.storageWrite slot value)

private def checkpoint : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨stateWith checkpointValue, ⟨10, [1]⟩⟩

private def working : WorldState × FrameEffectJournal Nat (List Nat) :=
  (stateWith workingValue, ⟨20, [1, 2]⟩)

private def concrete : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint, working⟩

private example :
    concrete.checkpoint =
      (⟨stateWith checkpointValue, ⟨10, [1]⟩⟩ :
        FrameCheckpointSnapshot Nat (List Nat)) := by
  rfl

private example :
    concrete.working =
      (stateWith workingValue,
        (⟨20, [1, 2]⟩ : FrameEffectJournal Nat (List Nat))) := by
  rfl

end Tests
