import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-! Runtime regressions for address-bound working storage reads. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0x21, by decide⟩
private def addressB : Address := ⟨0x43, by decide⟩
private def slotA : Core.Word := ⟨0x65, by decide⟩
private def slotB : Core.Word := ⟨0x87, by decide⟩
private def checkpointA : Core.Word := ⟨0x91, by decide⟩
private def checkpointB : Core.Word := ⟨0x92, by decide⟩
private def workingAA : Core.Word := ⟨0xa1, by decide⟩
private def workingAB : Core.Word := ⟨0xa2, by decide⟩
private def workingBA : Core.Word := ⟨0xb1, by decide⟩
private def workingBB : Core.Word := ⟨0xb2, by decide⟩

private def accountWith (valueA valueB : Core.Word) : Account :=
  Account.empty
    |>.storageWrite slotA valueA
    |>.storageWrite slotB valueB

private def checkpointState : WorldState :=
  WorldState.empty
    |>.putAccount addressA (Account.empty.storageWrite slotA checkpointA)
    |>.putAccount addressB (Account.empty.storageWrite slotA checkpointB)

private def checkpoint : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨checkpointState, ⟨7, [8]⟩⟩

private def effects : FrameEffectJournal Nat (List Nat) :=
  ⟨9, [10, 11]⟩

private def pairWith
    (state : WorldState) : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint, (state, effects)⟩

private def onlyB : WorldState :=
  WorldState.empty.putAccount addressB (accountWith workingBA workingBB)

private def emptyAWithB : WorldState :=
  onlyB.putAccount addressA Account.empty

private def full : WorldState :=
  onlyB.putAccount addressA (accountWith workingAA workingAB)

private def contextAt
    (address : Address) (state : WorldState) :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨address, pairWith state⟩

private def checkpointSlotA : Option Core.Word := do
  let account ← checkpoint.state.account? addressA
  some (account.storageRead slotA)

def testFrameCheckpointedWorkingPairWithStorageAddressStorageRead : IO Unit := do
  assertTrue
    (checkpointSlotA == some checkpointA &&
      (contextAt addressA onlyB).readStorage? slotA == none &&
      (contextAt addressB onlyB).readStorage? slotA == some workingBA)
    "a checkpoint value and unrelated working Account must not rescue a read"
  assertTrue
    (checkpointSlotA == some checkpointA &&
      (contextAt addressA emptyAWithB).readStorage? slotA ==
        some Core.Word.zero &&
      (contextAt addressB emptyAWithB).readStorage? slotA == some workingBA)
    "a present empty working Account must return zero, not checkpoint data"
  assertTrue
    ((contextAt addressA full).readStorage? slotA == some workingAA &&
      (contextAt addressA full).readStorage? slotB == some workingAB &&
      (contextAt addressB full).readStorage? slotA == some workingBA &&
      (contextAt addressB full).readStorage? slotB == some workingBB)
    "stored address and slot must select exact values from one working state"

end Tests
