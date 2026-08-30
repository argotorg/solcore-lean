import Solcore.Synthesis.CoreV3.Seed

/-! Focused replay-contract regressions for Core v3 synthesis seeds. -/

set_option autoImplicit false

namespace Tests.CoreV3SynthesisSeed

open Solcore.Synthesis.CoreV3

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def drawValues : Nat → Seed → List UInt64
  | 0, _ => []
  | count + 1, seed =>
      let (value, next) := seed.draw
      value :: drawValues count next

private def chooseValues : List Nat → Seed → List Nat × Seed
  | [], seed => ([], seed)
  | bound :: bounds, seed =>
      let (value, next) := seed.choose bound
      let (values, finalSeed) := chooseValues bounds next
      (value :: values, finalSeed)

private def seedZeroVector : List UInt64 := [
  1442695040888963407,
  1876011003808476466,
  11166244414315200793,
  7401132627792533940,
  7076646890315895283,
  10346034117385188870
]

example : drawValues 6 (Seed.ofNat 0) = seedZeroVector := by
  native_decide

example :
    (Seed.ofNat 42).choose 0 =
      (0, Seed.ofUInt64 10481999410520546993) := by
  native_decide

private def replayBounds : List Nat := [1, 2, 3, 17, 0, 65537]

private def replayFrom42 : List Nat × Seed :=
  chooseValues replayBounds (Seed.ofNat 42)

example :
    replayFrom42 =
      ([0, 0, 2, 12, 0, 19656], Seed.ofUInt64 483838003013946848) := by
  native_decide

def testCoreV3SynthesisSeed : IO Unit := do
  assertTrue
    (drawValues 6 (Seed.ofNat 0) == seedZeroVector)
    "the lcg64-v1 exact draw vector changed"
  assertTrue
    ((Seed.ofNat 42).choose 0 ==
      (0, Seed.ofUInt64 10481999410520546993))
    "a zero-bound choice did not consume exactly one draw"
  assertTrue
    (replayFrom42 ==
      ([0, 0, 2, 12, 0, 19656], Seed.ofUInt64 483838003013946848))
    "the lcg64-v1 bounded-choice vector changed"

end Tests.CoreV3SynthesisSeed
