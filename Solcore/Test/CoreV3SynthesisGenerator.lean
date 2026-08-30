import Solcore.Synthesis.CoreV3.Generator

/-! Focused executable regressions for deterministic checked Core generation. -/

set_option autoImplicit false

namespace Tests.CoreV3SynthesisGenerator

open Solcore.Core.Wire
open Solcore.Synthesis.CoreV3

private def request (seed bound : Nat) : GenerationRequest := {
  seed := Seed.ofNat seed
  maxProgramNodes := bound
}

private def rejectsSmallBound (bound : Nat) : Bool :=
  match generate (request 0 bound) with
  | .error .budgetTooSmall => true
  | _ => false

private def minimumBoundIsExact : Bool :=
  match generate (request 0 minimumProgramNodes) with
  | .ok generated =>
      generated.nodeCount == minimumProgramNodes &&
        generated.program.check &&
        accepts .word generated.program.body
  | .error _ => false

private def sameInputIsExact : Bool :=
  match generate (request 37 64), generate (request 37 64) with
  | .ok first, .ok second =>
      first.initialSeed == second.initialSeed &&
        first.finalSeed == second.finalSeed &&
        first.maxProgramNodes == second.maxProgramNodes &&
        V3.encodeProgram first.program == V3.encodeProgram second.program &&
        first.features == second.features
  | _, _ => false

private def bounds : List Nat :=
  [3, 4, 5, 8, 16, 32, 64]

private def corpusIsCheckedAndBounded : Bool :=
  (List.range 128).all fun seedValue =>
    bounds.all fun bound =>
      match generate (request seedValue bound) with
      | .ok generated =>
          generated.initialSeed == Seed.ofNat seedValue &&
            generated.maxProgramNodes == bound &&
            generated.nodeCount ≤ bound &&
            generated.program.check &&
            accepts .word generated.program.body
      | .error _ => false

private def generatedLocalBinder : Bool :=
  (List.range 512).any fun seedValue =>
    match generate (request seedValue 64) with
    | .ok generated =>
        generated.features.contains .letE &&
          generated.features.contains .local
    | .error _ => false

private def allChecks : Bool :=
  rejectsSmallBound 0 && rejectsSmallBound 1 && rejectsSmallBound 2 &&
    minimumBoundIsExact && sameInputIsExact &&
    corpusIsCheckedAndBounded && generatedLocalBinder

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testCoreV3SynthesisGenerator : IO Unit := do
  unless allChecks do
    throw (IO.userError "Core v3 checked generator changed")

end Tests.CoreV3SynthesisGenerator
