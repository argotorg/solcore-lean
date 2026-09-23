import Solcore.ContractRuntime.FrameRun

/-! Executable boundary tests for state-and-outcome frame results. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive RunTrapReason where
  | invalidOperation
  deriving BEq, DecidableEq

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

def testFrameRunResult : IO Unit := do
  let returnData := [0x12, 0].toByteArray
  let revertData := [].toByteArray
  let returned : FrameRunResult RunTrapReason := {
    working
    outcome := .returned returnData
  }
  let reverted : FrameRunResult RunTrapReason := {
    working
    outcome := .reverted revertData
  }
  let trapped : FrameRunResult RunTrapReason := {
    working
    outcome := .trapped .invalidOperation
  }
  assertTrue
    (observedValue? (returned.resolvedWorldState? checkpoint) == some workingValue &&
      observedValue? (some returned.working) == some workingValue &&
      returned.outcome.returndata? == some returnData)
    "a returned result must expose its nonempty data and select its working state"
  assertTrue
    (observedValue? (reverted.resolvedWorldState? checkpoint) == some checkpointValue &&
      observedValue? (some reverted.working) == some workingValue &&
      reverted.outcome.revertdata? == some revertData &&
      reverted.outcome.revertdata? != none)
    "a reverted result must retain working state and empty data but resolve to checkpoint"
  assertTrue
    ((trapped.resolvedWorldState? checkpoint).isNone &&
      observedValue? (some trapped.working) == some workingValue &&
      trapped.outcome.trapReason? == some .invalidOperation)
    "a trapped result must retain working state and its reason while resolution stays open"

end Tests
