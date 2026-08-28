import Solcore.Semantics.FrameResolutionResultTrapReasonMap

/-! Definition-only tests for total-resolution trap-reason mapping. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

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
private def returnStateValue : Core.Word := ⟨0xaa, by decide⟩
private def revertStateValue : Core.Word := ⟨0xbb, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address (Account.empty.storageWrite slot value)

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def returnEffects : FrameEffectJournal Nat Nat := ⟨10, 100⟩
private def revertEffects : FrameEffectJournal Nat Nat := ⟨20, 200⟩

private def returnBytes : Bytes :=
  [0x12, 0x00].toByteArray

private def revertBytes : Bytes :=
  [0x34, 0xff].toByteArray

private def matchesReturned :
    FrameResolutionResult Nat Nat MappedTrapReason → Bool
  | .returned state effects data =>
      observedValue? state == some returnStateValue &&
        effects.rollback == 10 && effects.trace == 100 && data == returnBytes
  | _ => false

private def matchesReverted :
    FrameResolutionResult Nat Nat MappedTrapReason → Bool
  | .reverted state effects data =>
      observedValue? state == some revertStateValue &&
        effects.rollback == 20 && effects.trace == 200 && data == revertBytes
  | _ => false

private def matchesMappedTrap :
    FrameResolutionResult Nat Nat MappedTrapReason → Bool
  | .trapped .mapped => true
  | _ => false

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testFrameResolutionResultTrapReasonMap : IO Unit := do
  assertTrue
    (matchesReturned
      (FrameResolutionResult.mapTrapReason mapReason
        (FrameResolutionResult.returned
          (TrapReason := LocalTrapReason)
          (stateWith returnStateValue) returnEffects returnBytes)))
    "return mapping must preserve exact state, effects, and bytes"

  assertTrue
    (matchesReverted
      (FrameResolutionResult.mapTrapReason mapReason
        (FrameResolutionResult.reverted
          (TrapReason := LocalTrapReason)
          (stateWith revertStateValue) revertEffects revertBytes)))
    "revert mapping must preserve distinct state, effects, and bytes"

  assertTrue
    (matchesMappedTrap
      (FrameResolutionResult.mapTrapReason mapReason
        (FrameResolutionResult.trapped
          (RollbackState := Nat) (TraceState := Nat) LocalTrapReason.marker)))
    "trap mapping must produce the exact target reason"

end Tests
