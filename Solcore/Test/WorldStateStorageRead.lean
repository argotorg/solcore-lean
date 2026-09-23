import Solcore.ContractRuntime.WorldStateStorageRead

/-! Runtime regressions for conditional WorldState storage reads. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0x31, by decide⟩
private def addressB : Address := ⟨0x52, by decide⟩
private def slotA : Core.Word := ⟨0x73, by decide⟩
private def slotB : Core.Word := ⟨0x94, by decide⟩
private def valueA : Core.Word := ⟨0xb5, by decide⟩
private def valueB : Core.Word := ⟨0xd6, by decide⟩
private def otherSlotValue : Core.Word := ⟨0xf7, by decide⟩

private def accountA : Account :=
  Account.empty
    |>.storageWrite slotA valueA
    |>.storageWrite slotB otherSlotValue

private def accountB : Account :=
  Account.empty.storageWrite slotA valueB

private def stateWithB : WorldState :=
  WorldState.empty.putAccount addressB accountB

private def stateWithEmptyA : WorldState :=
  stateWithB.putAccount addressA Account.empty

private def stateWithBoth : WorldState :=
  stateWithB.putAccount addressA accountA

def testWorldStateStorageRead : IO Unit := do
  assertTrue
    ((stateWithB.readStorage? addressA slotA).isNone &&
      stateWithB.readStorage? addressB slotA == some valueB)
    "an unrelated present Account must not rescue an absent read target"
  assertTrue
    (stateWithEmptyA.readStorage? addressA slotA == some Core.Word.zero &&
      stateWithEmptyA.readStorage? addressB slotA == some valueB)
    "a missing slot in a present Account must read as an available zero"
  assertTrue
    (stateWithBoth.readStorage? addressA slotA == some valueA &&
      stateWithBoth.readStorage? addressA slotB == some otherSlotValue &&
      stateWithBoth.readStorage? addressB slotA == some valueB)
    "a stored read must select the exact address and slot"

end Tests
