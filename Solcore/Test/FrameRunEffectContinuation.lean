import Solcore.ContractRuntime.FrameRun

/-! Executable tests for resolved synchronized frame continuations. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive ContinuationTrapReason where
  | marker

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def address : Address := ⟨0, by decide⟩
private def slot : Core.Word := ⟨0x11, by decide⟩
private def checkpointValue : Core.Word := ⟨0xaa, by decide⟩
private def workingValue : Core.Word := ⟨0xbb, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def stateCheckpoint : WorldState := stateWith checkpointValue
private def workingWorld : WorldState := stateWith workingValue

private def effectCheckpoint : FrameEffectJournal Nat Nat := ⟨10, 100⟩
private def effectWorking : FrameEffectJournal Nat Nat := ⟨20, 200⟩

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def observeSelected
    (selected : WorldState × FrameEffectJournal Nat Nat) :
    Option (Option Core.Word × Nat × Nat) :=
  some (observedValue? selected.1, selected.2.rollback, selected.2.trace)

def testFrameRunEffectContinuation : IO Unit := do
  let returned : FrameRunResult ContinuationTrapReason :=
    ⟨workingWorld, .returned [0x12].toByteArray⟩
  let returnedObserved :=
    (returned.resolvedWorldStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking).bind observeSelected
  assertTrue
    (returnedObserved == some (some workingValue, 20, 200))
    "return continuation must receive working state, rollback, and trace"

  let reverted : FrameRunResult ContinuationTrapReason :=
    ⟨workingWorld, .reverted [].toByteArray⟩
  let revertedObserved :=
    (reverted.resolvedWorldStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking).bind observeSelected
  assertTrue
    (revertedObserved == some (some checkpointValue, 10, 200))
    "revert continuation must receive checkpoint state and rollback with working trace"

end Tests
