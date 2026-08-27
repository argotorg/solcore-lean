import Solcore.Semantics.WorldState

/-! Executable boundary tests for minimal accounts and word storage. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0, by decide⟩
private def addressB : Address := ⟨1, by decide⟩

private def keyA : Core.Word := ⟨0x11, by decide⟩
private def keyB : Core.Word := ⟨0x22, by decide⟩
private def valueA : Core.Word := ⟨0xaa, by decide⟩
private def valueB : Core.Word := ⟨0xbb, by decide⟩

private def accountB : Account :=
  Account.empty.storageWrite keyB valueB

private def stateWithB : WorldState :=
  WorldState.empty.putAccount addressB accountB

def testWorldState : IO Unit := do
  assertTrue (WorldState.empty.account? addressA == none)
    "an empty world must report every address as absent"
  assertTrue
    ((WorldState.empty.putAccount addressA Account.empty).account? addressA ==
      some Account.empty)
    "putting an empty account must make its address explicitly present"
  assertTrue
    ((stateWithB.putAccount addressA Account.empty).account? addressB == some accountB)
    "putting one address must preserve the account at another address"
  assertTrue (Account.empty.storageValue? keyA == none)
    "an empty account must contain no physical storage entry"
  assertTrue (Account.empty.storageRead keyA == Core.Word.zero)
    "reading missing storage in an empty account must return zero"
  assertTrue
    ((Account.empty.storageWrite keyA valueA).storageRead keyA == valueA)
    "reading a nonzero value immediately after writing it must return that value"
  let deleted :=
    (Account.empty.storageWrite keyA valueA).storageWrite keyA Core.Word.zero
  assertTrue (deleted.storageValue? keyA == none)
    "writing zero must physically delete the selected storage entry"
  assertTrue
    ((Account.empty.storageWrite keyA valueA).storageValue? keyA == some valueA)
    "writing a nonzero value must create a physical storage entry"
  assertTrue
    ((accountB.storageWrite keyA valueA).storageRead keyB == valueB)
    "writing one storage key must preserve the value at another key"
  assertTrue
    (WorldState.empty.writeStorage? addressA keyA valueA == none)
    "writing storage at an absent address must fail without creating an account"
  assertTrue
    (match (WorldState.empty.putAccount addressA Account.empty).writeStorage?
        addressA keyA valueA with
      | some updated =>
          updated.account? addressA == some (Account.empty.storageWrite keyA valueA)
      | none => false)
    "writing storage at a present address must update and preserve that account"
  assertTrue
    (match (stateWithB.putAccount addressA Account.empty).writeStorage?
        addressA keyA valueA with
      | some updated => updated.account? addressB == some accountB
      | none => false)
    "writing storage at one address must preserve an account at another address"

end Tests
