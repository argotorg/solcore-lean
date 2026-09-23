import Solcore.ContractRuntime.FrameCheckpointedWorkingPair

/-! Runtime regressions for checkpointed working-world storage writes. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0x12, by decide⟩
private def addressB : Address := ⟨0x34, by decide⟩
private def slotA : Core.Word := ⟨0x56, by decide⟩
private def slotB : Core.Word := ⟨0x78, by decide⟩
private def checkpointValue : Core.Word := ⟨0x9a, by decide⟩
private def oldValue : Core.Word := ⟨0xbc, by decide⟩
private def replacement : Core.Word := ⟨0xde, by decide⟩
private def otherSlotValue : Core.Word := ⟨0xf0, by decide⟩
private def otherAccountValue : Core.Word := ⟨0x11, by decide⟩

private def checkpointState : WorldState :=
  WorldState.empty.putAccount addressA
    (Account.empty.storageWrite slotA checkpointValue)

private def workingState : WorldState :=
  WorldState.empty
    |>.putAccount addressA
      (Account.empty.storageWrite slotA oldValue
        |>.storageWrite slotB otherSlotValue)
    |>.putAccount addressB
      (Account.empty.storageWrite slotB otherAccountValue)

private def checkpoint : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨checkpointState, ⟨7, [8]⟩⟩

private def workingEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨9, [10, 11]⟩

private def presentValues : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint, (workingState, workingEffects)⟩

private def absentValues : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint, (WorldState.empty, workingEffects)⟩

private def accountSlotEq
    (state : WorldState) (address : Address)
    (slot expected : Core.Word) : Bool :=
  match state.account? address with
  | none => false
  | some account => account.storageValue? slot == some expected

private def accountSlotAbsentButPresent
    (state : WorldState) (address : Address) (slot : Core.Word) : Bool :=
  match state.account? address with
  | none => false
  | some account =>
      account.storageValue? slot == none &&
        account.storageRead slot == Core.Word.zero

private def preserved
    (values : FrameCheckpointedWorkingPair Nat (List Nat)) : Bool :=
  accountSlotEq values.checkpoint.state addressA slotA checkpointValue &&
    values.checkpoint.effects.rollback == 7 &&
    values.checkpoint.effects.trace == [8] &&
    values.working.2.rollback == 9 &&
    values.working.2.trace == [10, 11] &&
    accountSlotEq values.working.1 addressA slotB otherSlotValue &&
    accountSlotEq values.working.1 addressB slotB otherAccountValue

def testFrameCheckpointedWorkingPairStorageWrite : IO Unit := do
  assertTrue
    (accountSlotEq absentValues.checkpoint.state addressA slotA
        checkpointValue &&
      (absentValues.writeWorkingStorage?
        addressA slotA replacement).isNone)
    "a checkpoint account must not rescue an absent working account"
  assertTrue
    (match presentValues.writeWorkingStorage? addressA slotA replacement with
      | none => false
      | some updated =>
          accountSlotEq updated.working.1 addressA slotA replacement &&
            preserved updated)
    "a nonzero write must update only the selected working storage slot"
  assertTrue
    (match presentValues.writeWorkingStorage?
        addressA slotA Core.Word.zero with
      | none => false
      | some updated =>
          accountSlotAbsentButPresent updated.working.1 addressA slotA &&
            preserved updated)
    "a zero write must delete only the selected working storage slot"

end Tests
