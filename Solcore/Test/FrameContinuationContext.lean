import Solcore.Semantics.FrameContinuationContext

/-! Executable tests for the caller-owned frame continuation context. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private inductive ContextReason where
  | marker

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def isReturnedPayload? : FrameOutcome ContextReason → Bool
  | .returned data => data == [0x12].toByteArray
  | _ => false

private def isEmptyRevert? : FrameOutcome ContextReason → Bool
  | .reverted data => data.isEmpty
  | _ => false

private def isMarker? : FrameOutcome ContextReason → Bool
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

private def contextWith
    (outcome : FrameOutcome ContextReason) :
    FrameContinuationContext Nat Nat ContextReason :=
  ⟨stateCheckpoint, effectCheckpoint, effectWorking,
    ⟨workingWorld, outcome⟩⟩

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def observeSelected
    (selected : WorldState × FrameEffectJournal Nat Nat) :
    Option (Option Core.Word × Nat × Nat) :=
  some (observedValue? selected.1, selected.2.rollback, selected.2.trace)

def testFrameContinuationContext : IO Unit := do
  let returnedContext := contextWith (.returned [0x12].toByteArray)
  let returnedObserved := returnedContext.continue? observeSelected
  assertTrue
    (observedValue? returnedContext.stateCheckpoint == some checkpointValue &&
      returnedContext.effectCheckpoint.rollback == 10 &&
      returnedContext.effectCheckpoint.trace == 100 &&
      returnedContext.effectWorking.rollback == 20 &&
      returnedContext.effectWorking.trace == 200 &&
      observedValue? returnedContext.result.working == some workingValue &&
      isReturnedPayload? returnedContext.result.outcome &&
      returnedObserved == some (some workingValue, 20, 200))
    "return context must expose its inputs and continue with the working pair"

  let revertedContext := contextWith (.reverted [].toByteArray)
  let revertedObserved := revertedContext.continue? observeSelected
  assertTrue
    (isEmptyRevert? revertedContext.result.outcome &&
      revertedObserved == some (some checkpointValue, 10, 200))
    "revert context must restore checkpoint state and rollback with working trace"

  let trappedContext := contextWith (.trapped .marker)
  let trappedObserved := trappedContext.continue? observeSelected
  assertTrue
    (isMarker? trappedContext.result.outcome && trappedObserved.isNone)
    "trap context must preserve its reason and skip the sentinel continuation"

end Tests
