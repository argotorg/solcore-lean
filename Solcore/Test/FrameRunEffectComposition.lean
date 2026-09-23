import Solcore.ContractRuntime.FrameRunEffectResolution

/-! Executable tests for synchronized child-frame composition. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive CompositionTrapReason where
  | marker

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def address : Address := ⟨0, by decide⟩
private def slot : Core.Word := ⟨0x11, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def parentStateCheckpoint : WorldState := stateWith ⟨0xaa, by decide⟩
private def childStateCheckpoint : WorldState := stateWith ⟨0xbb, by decide⟩
private def childStateWorking : WorldState := stateWith ⟨0xcc, by decide⟩

private def parentEffectCheckpoint : FrameEffectJournal Nat Nat := ⟨10, 100⟩
private def childEffectCheckpoint : FrameEffectJournal Nat Nat := ⟨20, 200⟩
private def childEffectWorking : FrameEffectJournal Nat Nat := ⟨30, 300⟩

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

private def parentRevertAfter?
    (childResolved? : Option (WorldState × FrameEffectJournal Nat Nat)) :
    Option (WorldState × FrameEffectJournal Nat Nat) :=
  childResolved?.bind fun childResolved =>
    let parentResult : FrameRunResult CompositionTrapReason :=
      ⟨childResolved.1, .reverted [].toByteArray⟩
    parentResult.resolvedWorldStateAndEffects?
      parentStateCheckpoint parentEffectCheckpoint childResolved.2

def testFrameRunEffectComposition : IO Unit := do
  let childReturned : FrameRunResult CompositionTrapReason :=
    ⟨childStateWorking, .returned [0x12].toByteArray⟩
  let returnedIntermediate := childReturned.resolvedWorldStateAndEffects?
    childStateCheckpoint childEffectCheckpoint childEffectWorking
  assertTrue
    (matches? returnedIntermediate ⟨0xcc, by decide⟩ 30 300 &&
      matches? (parentRevertAfter? returnedIntermediate) ⟨0xaa, by decide⟩ 10 300)
    "returned child must be adopted before parent revert restores parent rollback and preserves child trace"

  let childReverted : FrameRunResult CompositionTrapReason :=
    ⟨childStateWorking, .reverted [].toByteArray⟩
  let revertedIntermediate := childReverted.resolvedWorldStateAndEffects?
    childStateCheckpoint childEffectCheckpoint childEffectWorking
  assertTrue
    (matches? revertedIntermediate ⟨0xbb, by decide⟩ 20 300 &&
      matches? (parentRevertAfter? revertedIntermediate) ⟨0xaa, by decide⟩ 10 300)
    "reverted child must restore its checkpoint before parent revert restores the parent checkpoint and preserves child trace"

end Tests
