import Solcore.ContractRuntime.FrameResolutionResultContinuation

/-! Executable branch and payload tests for frame resolution continuation. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive Reason where
  | marker
  | other

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def address : Address := ⟨0x12, by decide⟩
private def slot : Core.Word := ⟨0x34, by decide⟩
private def returnedValue : Core.Word := ⟨0x56, by decide⟩
private def revertedValue : Core.Word := ⟨0x78, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address
    (Account.empty.storageWrite slot value)

private def returnedState : WorldState := stateWith returnedValue
private def revertedState : WorldState := stateWith revertedValue

private def returnedEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨10, [1]⟩

private def revertedEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨20, [2, 3]⟩

private def returnedBytes : Bytes := [0, 0x12].toByteArray
private def revertedBytes : Bytes := [0x34, 0xff].toByteArray

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def onReturned
    (selected : WorldState × FrameEffectJournal Nat (List Nat))
    (data : Bytes) : Option Nat :=
  if observedValue? selected.1 == some returnedValue &&
      selected.2.rollback == 10 && selected.2.trace == [1] &&
      data == returnedBytes then
    some 11
  else
    some 91

private def onReverted
    (selected : WorldState × FrameEffectJournal Nat (List Nat))
    (data : Bytes) : Option Nat :=
  if observedValue? selected.1 == some revertedValue &&
      selected.2.rollback == 20 && selected.2.trace == [2, 3] &&
      data == revertedBytes then
    some 22
  else
    some 92

def testFrameResolutionResultContinuation : IO Unit := do
  let returned : FrameResolutionResult Nat (List Nat) Reason :=
    .returned returnedState returnedEffects returnedBytes
  assertTrue
    (returned.continue? onReturned onReverted == some 11)
    "return continuation must receive exact state, effects, and bytes"

  let reverted : FrameResolutionResult Nat (List Nat) Reason :=
    .reverted revertedState revertedEffects revertedBytes
  assertTrue
    (reverted.continue? onReturned onReverted == some 22)
    "revert continuation must receive exact state, effects, and bytes"

  let trapped : FrameResolutionResult Nat (List Nat) Reason := .trapped .marker
  assertTrue
    ((trapped.continue? onReturned onReverted).isNone)
    "trap continuation must select neither non-trapping callback"

end Tests
