import Solcore.ContractRuntime.FrameContinuationContextTrapReasonMap

/-! Definition-only tests for continuation-context trap-reason mapping. -/

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

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def returnCheckpointValue : Core.Word := ⟨0x10, by decide⟩
private def returnWorkingValue : Core.Word := ⟨0x11, by decide⟩
private def revertCheckpointValue : Core.Word := ⟨0x20, by decide⟩
private def revertWorkingValue : Core.Word := ⟨0x21, by decide⟩
private def trapCheckpointValue : Core.Word := ⟨0x30, by decide⟩
private def trapWorkingValue : Core.Word := ⟨0x31, by decide⟩

private def returnEffectCheckpoint : FrameEffectJournal Nat Nat := ⟨10, 100⟩
private def returnEffectWorking : FrameEffectJournal Nat Nat := ⟨11, 101⟩
private def revertEffectCheckpoint : FrameEffectJournal Nat Nat := ⟨20, 200⟩
private def revertEffectWorking : FrameEffectJournal Nat Nat := ⟨21, 201⟩
private def trapEffectCheckpoint : FrameEffectJournal Nat Nat := ⟨30, 300⟩
private def trapEffectWorking : FrameEffectJournal Nat Nat := ⟨31, 301⟩

private def returnBytes : Bytes :=
  [0x12, 0x00].toByteArray

private def revertBytes : Bytes :=
  [0x34, 0xff].toByteArray

private def contextWith
    (checkpointValue workingValue : Core.Word)
    (effectCheckpoint effectWorking : FrameEffectJournal Nat Nat)
    (outcome : FrameOutcome LocalTrapReason) :
    FrameContinuationContext Nat Nat LocalTrapReason :=
  ⟨stateWith checkpointValue, effectCheckpoint, effectWorking,
    ⟨stateWith workingValue, outcome⟩⟩

private def matchesReturned :
    FrameContinuationContext Nat Nat MappedTrapReason → Bool
  | ⟨checkpoint, effectCheckpoint, effectWorking,
      ⟨working, .returned data⟩⟩ =>
      observedValue? checkpoint == some returnCheckpointValue &&
        effectCheckpoint.rollback == 10 && effectCheckpoint.trace == 100 &&
        effectWorking.rollback == 11 && effectWorking.trace == 101 &&
        observedValue? working == some returnWorkingValue && data == returnBytes
  | _ => false

private def matchesReverted :
    FrameContinuationContext Nat Nat MappedTrapReason → Bool
  | ⟨checkpoint, effectCheckpoint, effectWorking,
      ⟨working, .reverted data⟩⟩ =>
      observedValue? checkpoint == some revertCheckpointValue &&
        effectCheckpoint.rollback == 20 && effectCheckpoint.trace == 200 &&
        effectWorking.rollback == 21 && effectWorking.trace == 201 &&
        observedValue? working == some revertWorkingValue && data == revertBytes
  | _ => false

private def matchesMappedTrap :
    FrameContinuationContext Nat Nat MappedTrapReason → Bool
  | ⟨checkpoint, effectCheckpoint, effectWorking,
      ⟨working, .trapped .mapped⟩⟩ =>
      observedValue? checkpoint == some trapCheckpointValue &&
        effectCheckpoint.rollback == 30 && effectCheckpoint.trace == 300 &&
        effectWorking.rollback == 31 && effectWorking.trace == 301 &&
        observedValue? working == some trapWorkingValue
  | _ => false

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testFrameContinuationContextTrapReasonMap : IO Unit := do
  assertTrue
    (matchesReturned
      (FrameContinuationContext.mapTrapReason mapReason
        (contextWith returnCheckpointValue returnWorkingValue
          returnEffectCheckpoint returnEffectWorking (.returned returnBytes))))
    "return mapping must preserve every context field and exact bytes"

  assertTrue
    (matchesReverted
      (FrameContinuationContext.mapTrapReason mapReason
        (contextWith revertCheckpointValue revertWorkingValue
          revertEffectCheckpoint revertEffectWorking (.reverted revertBytes))))
    "revert mapping must preserve distinct context fields and exact bytes"

  assertTrue
    (matchesMappedTrap
      (FrameContinuationContext.mapTrapReason mapReason
        (contextWith trapCheckpointValue trapWorkingValue
          trapEffectCheckpoint trapEffectWorking (.trapped .marker))))
    "trap mapping must preserve every context field and map the exact reason"

end Tests
