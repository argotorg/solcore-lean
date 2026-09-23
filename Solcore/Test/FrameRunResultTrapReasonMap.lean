import Solcore.ContractRuntime.FrameRun

/-! Definition-only tests for frame-run trap-reason mapping. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive LocalTrapReason where
  | marker
  | other

private inductive MappedTrapReason where
  | mapped
  | other

private def mapReason : LocalTrapReason → MappedTrapReason
  | .marker => .mapped
  | .other => .other

private def address : Address := ⟨0, by decide⟩
private def slot : Core.Word := ⟨0x11, by decide⟩
private def returnWorkingValue : Core.Word := ⟨0xaa, by decide⟩
private def revertWorkingValue : Core.Word := ⟨0xbb, by decide⟩
private def trapWorkingValue : Core.Word := ⟨0xcc, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def returnBytes : Bytes :=
  [0x12, 0x00].toByteArray

private def revertBytes : Bytes :=
  [0x34, 0xff].toByteArray

private def matchesReturned : FrameRunResult MappedTrapReason → Bool
  | ⟨state, .returned data⟩ =>
      observedValue? state == some returnWorkingValue && data == returnBytes
  | _ => false

private def matchesReverted : FrameRunResult MappedTrapReason → Bool
  | ⟨state, .reverted data⟩ =>
      observedValue? state == some revertWorkingValue && data == revertBytes
  | _ => false

private def matchesMappedTrap : FrameRunResult MappedTrapReason → Bool
  | ⟨state, .trapped .mapped⟩ =>
      observedValue? state == some trapWorkingValue
  | _ => false

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testFrameRunResultTrapReasonMap : IO Unit := do
  assertTrue
    (matchesReturned
      (FrameRunResult.mapTrapReason mapReason
        (⟨stateWith returnWorkingValue, .returned returnBytes⟩ :
          FrameRunResult LocalTrapReason)))
    "return mapping must preserve its working state and exact bytes"

  assertTrue
    (matchesReverted
      (FrameRunResult.mapTrapReason mapReason
        (⟨stateWith revertWorkingValue, .reverted revertBytes⟩ :
          FrameRunResult LocalTrapReason)))
    "revert mapping must preserve its distinct working state and exact bytes"

  assertTrue
    (matchesMappedTrap
      (FrameRunResult.mapTrapReason mapReason
        ⟨stateWith trapWorkingValue, .trapped LocalTrapReason.marker⟩))
    "trap mapping must preserve its working state and map the exact reason"

end Tests
