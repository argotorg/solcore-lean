import Solcore.ContractRuntime.WorldStateStorageRead

/-! Compile-only regressions for stage-preserving storage read/write laws. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    (state : WorldState) (address : Address)
    (slot value : Core.Word) :
    (state.writeStorage? address slot value).map
        (fun next => next.readStorage? address slot) =
      (state.account? address).map (fun _ => some value) := by
  simp

private example
    (state : WorldState) (address : Address)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (state.writeStorage? address writtenSlot value).map
        (fun next => next.readStorage? address readSlot) =
      (state.account? address).map
        (fun _ => state.readStorage? address readSlot) := by
  simp [different]

private example
    (state : WorldState)
    (writtenAddress readAddress : Address)
    (writtenSlot value readSlot : Core.Word)
    (different : readAddress ≠ writtenAddress) :
    (state.writeStorage? writtenAddress writtenSlot value).map
        (fun next => next.readStorage? readAddress readSlot) =
      (state.account? writtenAddress).map
        (fun _ => state.readStorage? readAddress readSlot) := by
  simp [different]

end Tests
