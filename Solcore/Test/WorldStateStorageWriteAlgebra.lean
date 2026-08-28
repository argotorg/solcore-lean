import Solcore.Semantics.WorldState

/-! Executable composition tests for partial WorldState storage writes. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0, by decide⟩
private def addressB : Address := ⟨1, by decide⟩
private def slotA : Core.Word := ⟨0x11, by decide⟩
private def slotB : Core.Word := ⟨0x22, by decide⟩
private def valueA : Core.Word := ⟨0xaa, by decide⟩
private def valueB : Core.Word := ⟨0xbb, by decide⟩
private def replacement : Core.Word := ⟨0xcc, by decide⟩

private def writeThen?
    (state : WorldState)
    (firstAddress : Address) (firstSlot firstValue : Core.Word)
    (secondAddress : Address) (secondSlot secondValue : Core.Word) :
    Option WorldState := do
  let next ← state.writeStorage? firstAddress firstSlot firstValue
  next.writeStorage? secondAddress secondSlot secondValue

private def observedValue?
    (state? : Option WorldState) (address : Address) (slot : Core.Word) :
    Option Core.Word := do
  let state ← state?
  let account ← state.account? address
  account.storageValue? slot

private def accountWithOtherSlot : Account :=
  Account.empty.storageWrite slotA valueA |>.storageWrite slotB valueB

private def presentA : WorldState :=
  WorldState.empty.putAccount addressA accountWithOtherSlot

def testWorldStateStorageWriteAlgebra : IO Unit := do
  let overwritten :=
    writeThen? presentA addressA slotA valueA addressA slotA replacement
  let absentSequence :=
    writeThen? WorldState.empty addressA slotA valueA addressA slotA replacement
  assertTrue
    (observedValue? overwritten addressA slotA == some replacement &&
      absentSequence.isNone &&
      (WorldState.empty.writeStorage? addressA slotA replacement).isNone)
    "same-slot writes must keep the last value when present and fail when absent"
  let oneAccount := WorldState.empty.putAccount addressA Account.empty
  let slotsLeft :=
    writeThen? oneAccount addressA slotA valueA addressA slotB valueB
  let slotsRight :=
    writeThen? oneAccount addressA slotB valueB addressA slotA valueA
  assertTrue
    (observedValue? slotsLeft addressA slotA == some valueA &&
      observedValue? slotsLeft addressA slotB == some valueB &&
      observedValue? slotsRight addressA slotA == some valueA &&
      observedValue? slotsRight addressA slotB == some valueB)
    "writes to distinct slots at one address must agree in both orders"
  let bothAccounts := oneAccount.putAccount addressB Account.empty
  let addressesLeft :=
    writeThen? bothAccounts addressA slotA valueA addressB slotB valueB
  let addressesRight :=
    writeThen? bothAccounts addressB slotB valueB addressA slotA valueA
  let missingLeft :=
    writeThen? oneAccount addressA slotA valueA addressB slotB valueB
  let missingRight :=
    writeThen? oneAccount addressB slotB valueB addressA slotA valueA
  assertTrue
    (observedValue? addressesLeft addressA slotA == some valueA &&
      observedValue? addressesLeft addressB slotB == some valueB &&
      observedValue? addressesRight addressA slotA == some valueA &&
      observedValue? addressesRight addressB slotB == some valueB &&
      missingLeft.isNone && missingRight.isNone)
    "distinct-address writes must commute when present and fail if one is absent"
  assertTrue
    (match presentA.writeStorage? addressA slotA Core.Word.zero with
      | some updated =>
          match updated.account? addressA with
          | some account =>
              account.storageValue? slotA == none &&
              account.storageRead slotA == Core.Word.zero &&
              account.storageValue? slotB == some valueB
          | none => false
      | none => false)
    "a successful zero write must delete only its slot and keep the Account present"

end Tests
