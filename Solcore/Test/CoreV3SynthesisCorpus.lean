import Solcore.Synthesis.CoreV3.Case

/-!
Executable corpus regressions for reproducible checked Core v3 synthesis.

The corpus deliberately runs in `IO`: evaluating 256 Oracle requests is a
runtime regression, not a kernel reduction obligation.
-/

set_option autoImplicit false

namespace Tests.CoreV3SynthesisCorpus

open Solcore.Core.Wire
open Solcore.Oracle.V5
open Solcore.Synthesis.CoreV3

private def nodeBound : Nat := 64

private def evaluationSteps : Nat := Limits.default.evaluationSteps

private def replaySeed : Nat := 37

private def request (seedValue bound : Nat) : GenerationRequest := {
  seed := Seed.ofNat seedValue
  maxProgramNodes := bound
}

private def failureContext
    (seedLabel : String)
    (bound fuel : Nat)
    (requestText : String) : String :=
  "generatorVersion=" ++ generatorVersion ++
    "\nseed=" ++ seedLabel ++
    "\nnodeBound=" ++ toString bound ++
    "\nfuel=" ++ toString fuel ++
    "\nrequestText=" ++ requestText

private def fail {α : Type}
    (message seedLabel : String)
    (bound fuel : Nat)
    (requestText : String) : IO α :=
  throw <| IO.userError <| message ++ "\n" ++
    failureContext seedLabel bound fuel requestText

private def require
    (condition : Bool)
    (message seedLabel : String)
    (bound fuel : Nat)
    (requestText : String) : IO Unit := do
  unless condition do
    fail message seedLabel bound fuel requestText

private def responseReturned (response : Response) : Bool :=
  match response.body with
  | .execute (.executed observation) =>
      match observation.value.outcome with
      | .returned _ => true
      | _ => false
  | _ => false

private def addFeatures
    (seen found : List Feature) : List Feature :=
  found.foldl (fun accumulated feature =>
    if accumulated.contains feature then accumulated
    else feature :: accumulated) seen

private def checkResponseCanonical
    (seedLabel : String)
    (generatedCase : GeneratedCase)
    (response : Response) : IO Unit := do
  let responseText := Wire.encodeResponseText response
  match Wire.decodeResponseText responseText with
  | .error error =>
      fail ("canonical response failed to decode: " ++
          Wire.encodeProtocolErrorText error)
        seedLabel nodeBound evaluationSteps generatedCase.requestText
  | .ok decoded =>
      require (decoded == response)
        "canonical response decoded to a different typed response"
        seedLabel nodeBound evaluationSteps generatedCase.requestText
      require (Wire.encodeResponseText decoded == responseText)
        "decoded response did not re-encode canonically"
        seedLabel nodeBound evaluationSteps generatedCase.requestText
      match Wire.canonicalizeResponseText responseText with
      | .error error =>
          fail ("canonical response normalization failed: " ++
              Wire.encodeProtocolErrorText error)
            seedLabel nodeBound evaluationSteps generatedCase.requestText
      | .ok canonical =>
          require (canonical == responseText)
            "encoded response was not the canonical response spelling"
            seedLabel nodeBound evaluationSteps generatedCase.requestText

private def checkReplay
    (seedValue : Nat)
    (first : GeneratedCase)
    (firstDirect firstDispatched : Response) : IO Unit := do
  let seedLabel := toString seedValue
  match make (request seedValue nodeBound) evaluationSteps with
  | .error error =>
      fail ("replay generation failed: " ++ reprStr error)
        seedLabel nodeBound evaluationSteps first.requestText
  | .ok second =>
      require (first.request == second.request &&
          first.requestText == second.requestText)
        "same generator input produced a different Oracle request"
        seedLabel nodeBound evaluationSteps first.requestText
      match second.runDirect, second.runDispatched with
      | .ok secondDirect, .ok secondDispatched =>
          require (firstDirect == secondDirect &&
              firstDispatched == secondDispatched &&
              Wire.encodeResponseText firstDirect ==
                Wire.encodeResponseText secondDirect)
            "same generator input produced a different Oracle response"
            seedLabel nodeBound evaluationSteps first.requestText
      | .error error, _ =>
          fail ("replayed direct execution failed: " ++
              Wire.encodeProtocolErrorText error)
            seedLabel nodeBound evaluationSteps first.requestText
      | _, .error error =>
          fail ("replayed dispatched execution failed: " ++
              Wire.encodeProtocolErrorText error)
            seedLabel nodeBound evaluationSteps first.requestText

private def checkSeed
    (seedValue : Nat)
    (seen : List Feature) : IO (List Feature) := do
  let seedLabel := toString seedValue
  match make (request seedValue nodeBound) evaluationSteps with
  | .error error =>
      fail ("corpus generation failed: " ++ reprStr error)
        seedLabel nodeBound evaluationSteps "<unavailable: generation failed>"
  | .ok generatedCase =>
      let generated := generatedCase.generated
      require (generated.initialSeed == Seed.ofNat seedValue &&
          generated.maxProgramNodes == nodeBound &&
          generated.program.check &&
          accepts .word generated.program.body &&
          decide (generated.nodeCount ≤ nodeBound))
        "generated program violated its checked fragment or node bound"
        seedLabel nodeBound evaluationSteps generatedCase.requestText
      match generatedCase.runDirect, generatedCase.runDispatched with
      | .ok direct, .ok dispatched =>
          require (direct == dispatched)
            "direct and dispatched Oracle execution disagreed"
            seedLabel nodeBound evaluationSteps generatedCase.requestText
          require (responseReturned direct)
            "generated case did not execute to a returned outcome"
            seedLabel nodeBound evaluationSteps generatedCase.requestText
          checkResponseCanonical seedLabel generatedCase direct
          if seedValue == replaySeed then
            checkReplay seedValue generatedCase direct dispatched
          pure (addFeatures seen generated.features)
      | .error error, _ =>
          fail ("direct Oracle execution failed: " ++
              Wire.encodeProtocolErrorText error)
            seedLabel nodeBound evaluationSteps generatedCase.requestText
      | _, .error error =>
          fail ("dispatched Oracle execution failed: " ++
              Wire.encodeProtocolErrorText error)
            seedLabel nodeBound evaluationSteps generatedCase.requestText

private def checkCorpus : List Nat → List Feature → IO (List Feature)
  | [], seen => pure seen
  | seedValue :: remaining, seen => do
      let seen ← checkSeed seedValue seen
      checkCorpus remaining seen

private def goldenProgramText : String :=
  "{\"body\":{\"tag\":\"word\",\"value\":\"0x1a08ee1184ba6d329af678222e72811966b61ae97f2099b462354cda6226d1f3\"},\"dataDefinitions\":[],\"resultType\":\"word\",\"schema\":\"solcore-semantic-core/v3\"}"

private def checkMinimumGolden : IO Unit := do
  let bound := minimumProgramNodes
  let seedLabel := "0"
  match make (request 0 bound) evaluationSteps with
  | .error error =>
      fail ("minimum golden generation failed: " ++ reprStr error)
        seedLabel bound evaluationSteps "<unavailable: generation failed>"
  | .ok generatedCase =>
      let generated := generatedCase.generated
      let programText := (V3.encodeProgram generated.program).compress
      require (Seed.toNat generated.finalSeed == 7076646890315895283)
        "minimum golden final seed changed"
        seedLabel bound evaluationSteps generatedCase.requestText
      require (programText == goldenProgramText)
        "minimum golden canonical Program changed"
        seedLabel bound evaluationSteps generatedCase.requestText

def testCoreV3SynthesisCorpus : IO Unit := do
  checkMinimumGolden
  let seen ← checkCorpus (List.range 256) []
  let missing := Feature.catalog.toList.filter fun feature =>
    !seen.contains feature
  require (Feature.catalog.size == 29 && missing.isEmpty)
    ("fixed corpus missed synthesis features: " ++ reprStr missing)
    "0..255" nodeBound evaluationSteps "<corpus aggregate>"

end Tests.CoreV3SynthesisCorpus
