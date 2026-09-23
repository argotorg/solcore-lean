import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite

/-! Runtime regressions for total writes through a present selected working Account. -/

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
private def checkpointValue : Core.Word := ⟨0x91, by decide⟩
private def unrelatedA : Core.Word := ⟨0xb1, by decide⟩
private def unrelatedB : Core.Word := ⟨0xb2, by decide⟩
private def oldValue : Core.Word := ⟨0xc1, by decide⟩
private def firstValue : Core.Word := ⟨0xd1, by decide⟩
private def secondValue : Core.Word := ⟨0xd2, by decide⟩
private def otherValue : Core.Word := ⟨0xe1, by decide⟩

private def accountWith (valueA valueB : Core.Word) : Account :=
  Account.empty.storageWrite slotA valueA |>.storageWrite slotB valueB

private def checkpoint : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨WorldState.empty.putAccount addressA
      (Account.empty.storageWrite slotA checkpointValue),
    ⟨17, [18]⟩⟩

private def effects : FrameEffectJournal Nat (List Nat) := ⟨27, [28, 29]⟩

private def contextAt (working : WorldState) :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨addressA, ⟨checkpoint, (working, effects)⟩⟩

private def unrelatedAccount : Account := accountWith unrelatedA unrelatedB

private def withSelected (account : Account) : WorldState :=
  WorldState.empty
    |>.putAccount addressB unrelatedAccount
    |>.putAccount addressA account

private def storageReadEq
    (state : WorldState) (address : Address)
    (slot expected : Core.Word) : Bool :=
  match state.account? address with
  | none => false
  | some account => account.storageRead slot == expected

private def storageValueMissing
    (state : WorldState) (address : Address) (slot : Core.Word) : Bool :=
  match state.account? address with
  | none => false
  | some account => (account.storageValue? slot).isNone

private def contextPreserved
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat)) : Bool :=
  context.storageAddress == addressA &&
    storageReadEq context.values.checkpoint.state
      addressA slotA checkpointValue &&
    (context.values.checkpoint.state.account? addressB).isNone &&
    context.values.checkpoint.effects.rollback == 17 &&
    context.values.checkpoint.effects.trace == [18] &&
    storageReadEq context.values.working.1 addressB slotA unrelatedA &&
    storageReadEq context.values.working.1 addressB slotB unrelatedB &&
    context.values.working.2.rollback == 27 &&
    context.values.working.2.trace == [28, 29]

def testFrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite :
    IO Unit := do
  assertTrue
    (match (contextAt
        (withSelected Account.empty)).withPresentStorageAccount? with
      | none => false
      | some refined =>
          let written := refined.writeStorage slotA firstValue
          written.storageAccount.storageRead slotA == firstValue &&
            storageReadEq written.context.values.working.1
              addressA slotA firstValue &&
            contextPreserved written.context)
    "a nonzero write must synchronize the Account and retained context"
  assertTrue
    (match (contextAt (withSelected
        (Account.empty.storageWrite slotA oldValue))).withPresentStorageAccount? with
      | none => false
      | some refined =>
          let written := refined.writeStorage slotA Core.Word.zero
          (written.storageAccount.storageValue? slotA).isNone &&
            written.storageAccount.storageRead slotA == Core.Word.zero &&
            storageValueMissing written.context.values.working.1 addressA slotA &&
            contextPreserved written.context)
    "a zero write must delete the slot without deleting the selected Account"
  assertTrue
    (match (contextAt (withSelected
        (Account.empty.storageWrite slotB otherValue))).withPresentStorageAccount? with
      | none => false
      | some refined =>
          let first := refined.writeStorage slotA firstValue
          let second := first.writeStorage slotA secondValue
          first.storageAccount.storageRead slotA == firstValue &&
            storageReadEq first.context.values.working.1
              addressA slotA firstValue &&
            second.storageAccount.storageRead slotA == secondValue &&
            second.storageAccount.storageRead slotB == otherValue &&
            storageReadEq second.context.values.working.1
              addressA slotA secondValue &&
            storageReadEq second.context.values.working.1
              addressA slotB otherValue &&
            contextPreserved second.context)
    "sequential overwrite must retain the other slot and frame context"

end Tests
