import Solcore.ContractRuntime.FrameRunContinuation

/-! Executable tests for caller-owned frame continuation. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive ContinuationReason where
  | marker

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def isMarker? : FrameOutcome ContinuationReason → Bool
  | .trapped .marker => true
  | _ => false

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

def testFrameRunContinuation : IO Unit := do
  let returned : FrameRunResult ContinuationReason :=
    ⟨workingWorld, .returned [0x12].toByteArray⟩
  let returnedObserved := returned.continueWithResolvedStateAndEffects?
    stateCheckpoint effectCheckpoint effectWorking observeSelected
  assertTrue
    (returnedObserved == some (some workingValue, 20, 200))
    "return must continue with working state, rollback, and trace"

  let reverted : FrameRunResult ContinuationReason :=
    ⟨workingWorld, .reverted [].toByteArray⟩
  let revertedObserved := reverted.continueWithResolvedStateAndEffects?
    stateCheckpoint effectCheckpoint effectWorking observeSelected
  assertTrue
    (revertedObserved == some (some checkpointValue, 10, 200))
    "revert must continue with checkpoint state and rollback plus working trace"

  let trapped : FrameRunResult ContinuationReason :=
    ⟨workingWorld, .trapped .marker⟩
  let trappedObserved := trapped.continueWithResolvedStateAndEffects?
    stateCheckpoint effectCheckpoint effectWorking observeSelected
  assertTrue
    (isMarker? trapped.outcome && trappedObserved.isNone)
    "trap must preserve its concrete input and skip the sentinel continuation"

end Tests
