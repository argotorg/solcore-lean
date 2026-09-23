import Solcore.ContractRuntime.FrameRunEffectResolution

/-! Executable test for unresolved trap propagation through Option bind. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive TrapPropagationReason where
  | fault

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def isFault? : FrameOutcome TrapPropagationReason → Bool
  | .trapped .fault => true
  | _ => false

def testFrameRunEffectTrapPropagation : IO Unit := do
  let trapped : FrameRunResult TrapPropagationReason :=
    ⟨WorldState.empty, .trapped .fault⟩
  let checkpoint : FrameEffectJournal Nat Nat := ⟨10, 100⟩
  let working : FrameEffectJournal Nat Nat := ⟨20, 200⟩
  let unresolved := trapped.resolvedWorldStateAndEffects?
    WorldState.empty checkpoint working
  let continued : Option Nat := unresolved.bind fun _ => some 7
  assertTrue
    (isFault? trapped.outcome && unresolved.isNone && continued.isNone)
    "concrete trap input must resolve to none and skip the sentinel continuation"

end Tests
