import Solcore.Oracle.Stream
import Solcore.Synthesis.CoreV3.Generator

/-!
Reproducible generated Core v3 programs packaged as minimal Oracle v5 cases.
-/

set_option autoImplicit false

namespace Solcore.Synthesis.CoreV3

private def requestId : Solcore.Oracle.V5.RequestId :=
  ⟨"g0", by decide⟩

private def target : Solcore.ContractRuntime.Address :=
  ⟨1, by decide⟩

private def caller : Solcore.ContractRuntime.Address :=
  ⟨2, by decide⟩

/-- Conservative public Program cap for cases using fixed default Oracle budgets. -/
def maximumCaseProgramNodes : Nat :=
  Solcore.Oracle.V5.Limits.default.coreDepth

/-- Failures that can occur before a generated case reaches the total Oracle. -/
inductive CaseError where
  | generation (error : GenerationError)
  | programBudgetTooLarge
  | generatedProgramExceedsDefaultCoreLimits
  deriving Repr, BEq, DecidableEq

/-- Build the fixed minimal scenario for any checker-sealed G0 Word program. -/
def minimalScenario (checkedProgram : CheckedWordProgram) :
    Solcore.Oracle.V5.Scenario := {
  contracts := [{
    id := "generated"
    spec := .checkedCore checkedProgram.program
  }]
  world := { accounts := [{
    address := target
    balance := Solcore.Core.Word.zero
    nonce := Solcore.Core.Word.zero
    storage := []
    code := some "generated"
  }] }
  environment := {
    callRegistry := []
    creationTemplates := []
    creationAddressPolicy := {
      routes := []
      defaultAddress := target
    }
  }
  invocation := {
    target
    caller
    callValue := Solcore.Core.Word.zero
    calldata := ByteArray.empty
    probes := [.code target]
  }
}

/-- Build the canonical execution request used by generated and shrunk cases. -/
def executionRequest
    (checkedProgram : CheckedWordProgram)
    (evaluationSteps : Nat) : Solcore.Oracle.V5.Request := {
  id := requestId
  limits := { Solcore.Oracle.V5.Limits.default with evaluationSteps }
  query := .execute (minimalScenario checkedProgram)
}

/-- Execute any sealed G0 Word program through the strict v5 text boundary. -/
def runCheckedDirect
    (checkedProgram : CheckedWordProgram)
    (evaluationSteps : Nat) :
    Except Solcore.Oracle.V5.ValidProtocolError Solcore.Oracle.V5.Response :=
  Solcore.Oracle.V5.handleText <|
    Solcore.Oracle.V5.Wire.encodeRequestText <|
      executionRequest checkedProgram evaluationSteps

/-- Execute the same sealed Program through the command-line record dispatcher. -/
def runCheckedDispatched
    (checkedProgram : CheckedWordProgram)
    (evaluationSteps : Nat) :
    Except Solcore.Oracle.V5.ValidProtocolError Solcore.Oracle.V5.Response :=
  let requestText := Solcore.Oracle.V5.Wire.encodeRequestText <|
    executionRequest checkedProgram evaluationSteps
  Solcore.Oracle.V5.Wire.decodeResponseText
    (Solcore.Oracle.processJsonLine requestText).compress

/-- A generated checked program and its canonical executable Oracle request. -/
structure GeneratedCase where
  private mk ::
  generated : GeneratedProgram
  evaluationSteps : Nat
  request : Solcore.Oracle.V5.Request
  requestText : String

/-- Generate a checked program and package it in the fixed minimal scenario. -/
def make
    (generation : GenerationRequest)
    (evaluationSteps : Nat) : Except CaseError GeneratedCase := do
  if generation.maxProgramNodes > maximumCaseProgramNodes then
    throw .programBudgetTooLarge
  let generated ← (generate generation).mapError .generation
  if generated.nodeCount > Solcore.Oracle.V5.Limits.default.coreNodes ||
      Solcore.Core.Wire.V3.programDepth generated.program >
        Solcore.Oracle.V5.Limits.default.coreDepth then
    throw .generatedProgramExceedsDefaultCoreLimits
  let request := executionRequest generated.checkedProgram evaluationSteps
  pure ⟨generated, evaluationSteps, request,
    Solcore.Oracle.V5.Wire.encodeRequestText request⟩

namespace GeneratedCase

/-- Execute through the duplicate-rejecting Oracle v5 text handler. -/
def runDirect (generatedCase : GeneratedCase) :
    Except Solcore.Oracle.V5.ValidProtocolError Solcore.Oracle.V5.Response :=
  Solcore.Oracle.V5.handleText generatedCase.requestText

/-- Execute the identical request through the public version dispatcher. -/
def runDispatched (generatedCase : GeneratedCase) :
    Except Solcore.Oracle.V5.ValidProtocolError Solcore.Oracle.V5.Response :=
  Solcore.Oracle.V5.Wire.decodeResponseText
    (Solcore.Oracle.processJsonLine generatedCase.requestText).compress

end GeneratedCase

end Solcore.Synthesis.CoreV3
