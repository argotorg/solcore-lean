import Solcore.ContractRuntime.FrameOutcomeTrapReasonMap

/-! Definition-only tests for heterogeneous frame trap-reason mapping. -/

set_option autoImplicit false

namespace Tests

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

private def returnBytes : Bytes :=
  [0x12, 0x00].toByteArray

private def revertBytes : Bytes :=
  [0x34, 0xff].toByteArray

private def matchesReturned : FrameOutcome MappedTrapReason → Bool
  | .returned data => data == returnBytes
  | _ => false

private def matchesReverted : FrameOutcome MappedTrapReason → Bool
  | .reverted data => data == revertBytes
  | _ => false

private def matchesMappedTrap : FrameOutcome MappedTrapReason → Bool
  | .trapped .mapped => true
  | _ => false

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testFrameOutcomeTrapReasonMap : IO Unit := do
  assertTrue
    (matchesReturned
      (FrameOutcome.mapTrapReason mapReason
        (FrameOutcome.returned (TrapReason := LocalTrapReason) returnBytes)))
    "return bytes must survive trap-reason mapping"

  assertTrue
    (matchesReverted
      (FrameOutcome.mapTrapReason mapReason
        (FrameOutcome.reverted (TrapReason := LocalTrapReason) revertBytes)))
    "revert bytes must survive trap-reason mapping"

  assertTrue
    (matchesMappedTrap
      (FrameOutcome.mapTrapReason mapReason
        (FrameOutcome.trapped LocalTrapReason.marker)))
    "a trapped reason must map to the exact target constructor"

end Tests
