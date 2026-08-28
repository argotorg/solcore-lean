import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-! Runtime regressions for selected working Account refinement. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0x21, by decide⟩
private def addressB : Address := ⟨0x43, by decide⟩
private def slotA : Core.Word := ⟨0x65, by decide⟩
private def slotB : Core.Word := ⟨0x87, by decide⟩
private def checkpointValue : Core.Word := ⟨0x91, by decide⟩
private def workingAA : Core.Word := ⟨0xa1, by decide⟩
private def workingAB : Core.Word := ⟨0xa2, by decide⟩
private def workingBA : Core.Word := ⟨0xb1, by decide⟩
private def workingBB : Core.Word := ⟨0xb2, by decide⟩

private def accountWith (valueA valueB : Core.Word) : Account :=
  Account.empty.storageWrite slotA valueA |>.storageWrite slotB valueB

private def checkpoint : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨WorldState.empty.putAccount addressA
      (Account.empty.storageWrite slotA checkpointValue),
    ⟨17, [18]⟩⟩

private def effects : FrameEffectJournal Nat (List Nat) := ⟨27, [28, 29]⟩

private def contextAt (address : Address) (working : WorldState) :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨address, ⟨checkpoint, (working, effects)⟩⟩

private def onlyB : WorldState :=
  WorldState.empty.putAccount addressB (accountWith workingBA workingBB)

private def emptyAWithB : WorldState := onlyB.putAccount addressA Account.empty

private def full : WorldState :=
  onlyB.putAccount addressA (accountWith workingAA workingAB)

private def storageReadEq
    (state : WorldState) (address : Address)
    (slot expected : Core.Word) : Bool :=
  match state.account? address with
  | none => false
  | some account => account.storageRead slot == expected

private def contextPreserved
    (refined :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat))
    (address : Address) (workingA workingB : Core.Word) : Bool :=
  refined.context.storageAddress == address &&
    storageReadEq refined.context.values.checkpoint.state
      addressA slotA checkpointValue &&
    (refined.context.values.checkpoint.state.account? addressB).isNone &&
    refined.context.values.checkpoint.effects.rollback == 17 &&
    refined.context.values.checkpoint.effects.trace == [18] &&
    storageReadEq refined.context.values.working.1
      addressA slotA workingA &&
    storageReadEq refined.context.values.working.1
      addressB slotA workingB &&
    refined.context.values.working.2.rollback == 27 &&
    refined.context.values.working.2.trace == [28, 29]

def testFrameCheckpointedWorkingPairWithPresentStorageAccount : IO Unit := do
  assertTrue
    ((contextAt addressA onlyB).withPresentStorageAccount?.isNone &&
      (contextAt addressB onlyB).withPresentStorageAccount?.isSome)
    "checkpoint presence and an unrelated working account must not rescue the target"
  assertTrue
    (match (contextAt addressA emptyAWithB).withPresentStorageAccount? with
      | none => false
      | some refined =>
          contextPreserved refined addressA Core.Word.zero workingBA &&
            refined.storageAccount.storageRead slotA == Core.Word.zero &&
            refined.storageAccount.storageRead slotB == Core.Word.zero)
    "a present empty working account must refine without changing its context"
  assertTrue
    (match (contextAt addressA full).withPresentStorageAccount?,
        (contextAt addressB full).withPresentStorageAccount? with
      | some refinedA, some refinedB =>
          contextPreserved refinedA addressA workingAA workingBA &&
            contextPreserved refinedB addressB workingAA workingBA &&
            refinedA.storageAccount.storageRead slotA == workingAA &&
            refinedA.storageAccount.storageRead slotB == workingAB &&
            refinedB.storageAccount.storageRead slotA == workingBA &&
            refinedB.storageAccount.storageRead slotB == workingBB
      | _, _ => false)
    "two selectors must recover exact Accounts and preserve their shared context"

end Tests
