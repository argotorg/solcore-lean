import Solcore.Synthesis.CoreV3.Case

/-! Focused regressions for generated Core v3 Oracle cases. -/

set_option autoImplicit false

namespace Tests.CoreV3SynthesisCase

open Solcore.Core.Wire
open Solcore.Oracle.V5
open Solcore.Semantics
open Solcore.Synthesis.CoreV3

private def generation : GenerationRequest := {
  seed := Seed.ofNat 17
  maxProgramNodes := 64
}

private def target : Address := ⟨1, by decide⟩
private def caller : Address := ⟨2, by decide⟩
private def requestId : RequestId := ⟨"g0", by decide⟩
private def contractId : ContractId := ⟨"generated", by decide⟩

private def expectedScenario (program : V3.Program) : Scenario := {
  contracts := [{
    id := "generated"
    spec := .checkedCore program
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

private def expectedRequest (program : V3.Program) : Request := {
  id := requestId
  limits := Limits.default
  query := .execute (expectedScenario program)
}

private def scenarioIsExact (generatedCase : GeneratedCase) : Bool :=
  generatedCase.generated.initialSeed == generation.seed &&
    generatedCase.generated.maxProgramNodes == generation.maxProgramNodes &&
    generatedCase.evaluationSteps == Limits.default.evaluationSteps &&
    generatedCase.request == expectedRequest generatedCase.generated.program

private def requestRoundTrips (generatedCase : GeneratedCase) : Bool :=
  generatedCase.requestText == Wire.encodeRequestText generatedCase.request &&
    match Wire.decodeText generatedCase.requestText with
    | .ok (.request decoded) =>
        decoded.value == generatedCase.request &&
          Wire.encodeRequestText decoded.value == generatedCase.requestText
    | _ => false

private def returnedExactly (response : Response) : Bool :=
  response.id == requestId &&
    match response.body with
    | .execute (.executed observation) =>
        match observation.value.outcome, observation.value.state.probes with
        | .returned _, [.code address initial committed] =>
            address == target && initial == some contractId &&
              committed == some contractId
        | _, _ => false
    | _ => false

private def sameSuccessfulResponse
    (left right : Except ValidProtocolError Response) : Bool :=
  match left, right with
  | .ok left, .ok right => left == right
  | _, _ => false

private def executionsAgree (generatedCase : GeneratedCase) : Bool :=
  match generatedCase.runDirect, generatedCase.runDispatched with
  | .ok direct, .ok dispatched =>
      returnedExactly direct && direct == dispatched &&
        Wire.encodeResponseText direct == Wire.encodeResponseText dispatched &&
        match Wire.decodeResponseText (Wire.encodeResponseText direct) with
        | .ok decoded => decoded == direct
        | .error _ => false
  | _, _ => false

private def replayIsExact (first : GeneratedCase) : Bool :=
  match make generation Limits.default.evaluationSteps with
  | .error _ => false
  | .ok second =>
      first.request == second.request &&
        first.requestText == second.requestText &&
        sameSuccessfulResponse first.runDirect second.runDirect &&
        sameSuccessfulResponse first.runDispatched second.runDispatched

private def allChecks : Bool :=
  match make generation Limits.default.evaluationSteps with
  | .error _ => false
  | .ok generatedCase =>
      scenarioIsExact generatedCase && requestRoundTrips generatedCase &&
        executionsAgree generatedCase && replayIsExact generatedCase

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testCoreV3SynthesisCase : IO Unit := do
  unless allChecks do
    throw (IO.userError "generated Core v3 Oracle case changed")

end Tests.CoreV3SynthesisCase
