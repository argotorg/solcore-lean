import Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

/-! Runtime regressions for address-bound checkpointed working storage writes. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0x21, by decide⟩
private def addressB : Address := ⟨0x43, by decide⟩
private def slot : Core.Word := ⟨0x65, by decide⟩
private def checkpointA : Core.Word := ⟨0x81, by decide⟩
private def checkpointB : Core.Word := ⟨0x82, by decide⟩
private def oldA : Core.Word := ⟨0x91, by decide⟩
private def oldB : Core.Word := ⟨0x92, by decide⟩
private def newA : Core.Word := ⟨0xa1, by decide⟩
private def newB : Core.Word := ⟨0xa2, by decide⟩

private def stateWithTwo (valueA valueB : Core.Word) : WorldState :=
  WorldState.empty
    |>.putAccount addressA (Account.empty.storageWrite slot valueA)
    |>.putAccount addressB (Account.empty.storageWrite slot valueB)

private def checkpoint : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨stateWithTwo checkpointA checkpointB, ⟨17, [18]⟩⟩

private def effects : FrameEffectJournal Nat (List Nat) :=
  ⟨27, [28, 29]⟩

private def base : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint, (stateWithTwo oldA oldB, effects)⟩

private def onlyB : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint,
    (WorldState.empty.putAccount addressB
      (Account.empty.storageWrite slot oldB), effects)⟩

private def slotEq
    (state : WorldState) (address : Address)
    (expected : Core.Word) : Bool :=
  match state.account? address with
  | none => false
  | some account => account.storageValue? slot == some expected

private def framePreserved
    (values : FrameCheckpointedWorkingPair Nat (List Nat)) : Bool :=
  slotEq values.checkpoint.state addressA checkpointA &&
    slotEq values.checkpoint.state addressB checkpointB &&
    values.checkpoint.effects.rollback == 17 &&
    values.checkpoint.effects.trace == [18] &&
    values.working.2.rollback == 27 &&
    values.working.2.trace == [28, 29]

def testFrameCheckpointedWorkingPairWithStorageAddress : IO Unit := do
  let missing :=
    FrameCheckpointedWorkingPairWithStorageAddress.mk addressA onlyB
  let targetA :=
    FrameCheckpointedWorkingPairWithStorageAddress.mk addressA base
  let targetB :=
    FrameCheckpointedWorkingPairWithStorageAddress.mk addressB base
  assertTrue
    ((missing.values.working.1.account? addressA).isNone &&
      slotEq missing.values.working.1 addressB oldB &&
      slotEq missing.values.checkpoint.state addressA checkpointA &&
      framePreserved missing.values &&
      (missing.writeStorage? slot newA).isNone)
    "an unrelated account and checkpoint account must not rescue the target"
  assertTrue
    (match targetA.writeStorage? slot newA with
      | none => false
      | some updated =>
          updated.storageAddress == addressA &&
            slotEq updated.values.working.1 addressA newA &&
            slotEq updated.values.working.1 addressB oldB &&
            framePreserved updated.values)
    "the first stored address must select and retain only the first account"
  assertTrue
    (match targetB.writeStorage? slot newB with
      | none => false
      | some updated =>
          updated.storageAddress == addressB &&
            slotEq updated.values.working.1 addressB newB &&
            slotEq updated.values.working.1 addressA oldA &&
            framePreserved updated.values)
    "the second stored address must select and retain only the second account"

end Tests
