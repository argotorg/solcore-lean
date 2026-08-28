import Solcore.Semantics.FrameRunEffectResolution

/-! Executable tests for synchronized frame state and effect resolution. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private inductive RunEffectTrapReason where
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

private def stateCheckpoint : WorldState := stateWith checkpointValue
private def workingWorld : WorldState := stateWith workingValue

private def effectCheckpoint : FrameEffectJournal Nat Nat := ⟨10, 100⟩
private def effectWorking : FrameEffectJournal Nat Nat := ⟨20, 200⟩

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def matches?
    (resolved? : Option (WorldState × FrameEffectJournal Nat Nat))
    (value : Core.Word) (rollback trace : Nat) : Bool :=
  match resolved? with
  | some resolved =>
      observedValue? resolved.1 == some value &&
        resolved.2.rollback == rollback && resolved.2.trace == trace
  | none => false

def testFrameRunEffectResolution : IO Unit := do
  let returned : FrameRunResult RunEffectTrapReason :=
    ⟨workingWorld, .returned [0x12, 0].toByteArray⟩
  let reverted : FrameRunResult RunEffectTrapReason :=
    ⟨workingWorld, .reverted [].toByteArray⟩
  let trapped : FrameRunResult RunEffectTrapReason :=
    ⟨workingWorld, .trapped .invalidOperation⟩
  assertTrue
    (matches? (returned.resolvedWorldStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking) workingValue 20 200)
    "return must keep both working state and working effect snapshots"
  assertTrue
    (matches? (reverted.resolvedWorldStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking) checkpointValue 10 200)
    "revert must restore checkpoint state and rollback while preserving trace"
  assertTrue
    ((trapped.resolvedWorldStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking).isNone)
    "trap must leave synchronized state and effect resolution open"

end Tests
