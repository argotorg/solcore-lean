import Solcore.Semantics.FrameStateResolution

/-! Executable tests for resolving frame outcomes against state snapshots. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private inductive TestTrapReason where
  | invalidOperation

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def address : Address := ⟨0, by decide⟩
private def slot : Core.Word := ⟨0x11, by decide⟩
private def checkpointValue : Core.Word := ⟨0xaa, by decide⟩
private def workingValue : Core.Word := ⟨0xbb, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def checkpoint : WorldState := stateWith checkpointValue
private def working : WorldState := stateWith workingValue

private def observedValue? (state? : Option WorldState) : Option Core.Word := do
  let state ← state?
  let account ← state.account? address
  account.storageValue? slot

def testFrameStateResolution : IO Unit := do
  let returned : FrameOutcome TestTrapReason :=
    .returned [0x12, 0].toByteArray
  let reverted : FrameOutcome TestTrapReason :=
    .reverted [].toByteArray
  let trapped : FrameOutcome TestTrapReason :=
    .trapped .invalidOperation
  assertTrue
    (observedValue? (returned.resolvedWorldState? checkpoint working) ==
      some workingValue)
    "a returned frame with nonempty data must select the working state"
  assertTrue
    (observedValue? (reverted.resolvedWorldState? checkpoint working) ==
      some checkpointValue)
    "a reverted frame with empty data must select the checkpoint state"
  assertTrue (trapped.resolvedWorldState? checkpoint working).isNone
    "a trapped frame with a concrete reason must leave state resolution open"

end Tests
