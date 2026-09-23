import Solcore.ContractRuntime.FrameResolutionResult

/-! Executable tests for total frame resolution. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive ResolutionReason where
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

private def contextWith
    (outcome : FrameOutcome ResolutionReason) :
    FrameContinuationContext Nat Nat ResolutionReason :=
  ⟨stateCheckpoint, effectCheckpoint, effectWorking,
    ⟨workingWorld, outcome⟩⟩

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def matchesReturn? :
    FrameResolutionResult Nat Nat ResolutionReason → Bool
  | .returned state effects data =>
      observedValue? state == some workingValue &&
        effects.rollback == 20 && effects.trace == 200 &&
        data == [0x12].toByteArray
  | _ => false

private def matchesRevert? :
    FrameResolutionResult Nat Nat ResolutionReason → Bool
  | .reverted state effects data =>
      observedValue? state == some checkpointValue &&
        effects.rollback == 10 && effects.trace == 200 &&
        data == [0x34].toByteArray
  | _ => false

private def matchesTrap? :
    FrameResolutionResult Nat Nat ResolutionReason → Bool
  | .trapped .marker => true
  | _ => false

def testFrameResolutionResult : IO Unit := do
  assertTrue
    (matchesReturn? (contextWith (.returned [0x12].toByteArray)).resolve)
    "return resolution must preserve working state, effects, and payload"

  assertTrue
    (matchesRevert? (contextWith (.reverted [0x34].toByteArray)).resolve)
    "revert resolution must select checkpoint rollback and working trace"

  assertTrue
    (matchesTrap? (contextWith (.trapped .marker)).resolve)
    "trap resolution must preserve only the concrete reason"

end Tests
