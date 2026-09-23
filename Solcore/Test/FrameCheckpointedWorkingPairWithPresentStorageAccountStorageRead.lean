import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead

/-! Runtime regressions for total reads from a present selected working Account. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0x31, by decide⟩
private def addressB : Address := ⟨0x53, by decide⟩
private def slotA : Core.Word := ⟨0x75, by decide⟩
private def slotB : Core.Word := ⟨0x97, by decide⟩
private def checkpointA : Core.Word := ⟨0xc1, by decide⟩
private def checkpointB : Core.Word := ⟨0xc2, by decide⟩
private def workingAA : Core.Word := ⟨0xa1, by decide⟩
private def workingAB : Core.Word := ⟨0xa2, by decide⟩
private def workingBA : Core.Word := ⟨0xb1, by decide⟩
private def workingBB : Core.Word := ⟨0xb2, by decide⟩

private def accountWith (valueA valueB : Core.Word) : Account :=
  Account.empty.storageWrite slotA valueA |>.storageWrite slotB valueB

private def checkpoint : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨WorldState.empty
      |>.putAccount addressA (accountWith checkpointA checkpointB)
      |>.putAccount addressB (accountWith checkpointB checkpointA),
    ⟨37, [38]⟩⟩

private def effects : FrameEffectJournal Nat (List Nat) := ⟨47, [48, 49]⟩

private def contextAt (state : WorldState) (address : Address) :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨address, ⟨checkpoint, (state, effects)⟩⟩

private def emptyA : WorldState :=
  WorldState.empty
    |>.putAccount addressA Account.empty
    |>.putAccount addressB (accountWith workingBA workingBB)

private def full : WorldState :=
  emptyA.putAccount addressA (accountWith workingAA workingAB)

private def readRefined?
    (state : WorldState) (address : Address) (slot : Core.Word) :
    Option Core.Word :=
  (contextAt state address).withPresentStorageAccount?.map
    (fun refined => refined.readStorage slot)

def testFrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead :
    IO Unit := do
  assertTrue
    (readRefined? emptyA addressA slotA == some Core.Word.zero)
    "a present empty working Account must return the zero slot default"
  assertTrue
    (readRefined? full addressA slotA == some workingAA &&
      readRefined? full addressA slotB == some workingAB)
    "selector A must read both of its exact working slot values"
  assertTrue
    (readRefined? full addressB slotA == some workingBA &&
      readRefined? full addressB slotB == some workingBB)
    "selector B must read both values without cross-address confusion"

end Tests
