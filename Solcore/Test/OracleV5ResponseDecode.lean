import Solcore.Oracle.V5.Wire.ResponseDecode

/-! End-to-end strict-decoding tests for typed Oracle v5 responses. -/

set_option autoImplicit false

namespace Tests.OracleV5ResponseDecode

open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire

private def requestId : RequestId := ⟨"response-id", by decide⟩

private def preflight : PreflightExhaustion :=
  ⟨.jsonDepth, 1, 2, by decide⟩

private def coreDiagnostic : Diagnostic := {
  code := "core.check.expected-bool"
  phase := .coreChecking
  path := ["program", "ifCondition"]
  arguments := .mkObj [("actual", "word")]
}

private def coreRejection : CoreCheckRejection :=
  (CoreCheckRejection.of? coreDiagnostic).get (by native_decide)

private def address : String :=
  "0x0000000000000000000000000000000000000001"

private def executeDiagnostic : Diagnostic := {
  code := "oracle.v5.root.target-absent"
  phase := .rootInstallation
  path := ["world", "accounts", address]
  arguments := .mkObj [("target", address)]
}

private def executeRejection : ExecuteRejection :=
  (ExecuteRejection.of? executeDiagnostic).get (by native_decide)

private def emptyObservation : ExecutionObservation := {
  outcome := .preflightRejected .senderAbsent
  journal := { logs := [], createdAddresses := [] }
  state := { probes := [] }
}

private def validObservation : ValidExecutionObservation :=
  (ValidExecutionObservation.of? emptyObservation).get (by native_decide)

private def response (body : ResponseBody) : Response := { id := requestId, body }

private def capabilityAcceptedResponse : Response :=
  response (.capabilities (.accepted capabilityReport))

private def responses : List Response := [
  capabilityAcceptedResponse,
  response (.capabilities (.inconclusive preflight)),
  response (.capabilities (.internalError .oracleResponseInvariant)),
  response (.coreCheck (.accepted { resultType := .word })),
  response (.coreCheck (.rejected coreRejection)),
  response (.coreCheck (.inconclusive preflight)),
  response (.coreCheck (.internalError .coreWireProjectionFailed)),
  response (.execute (.rejected executeRejection)),
  response (.execute (.inconclusive (.preflight preflight))),
  response (.execute (.inconclusive (.evaluationSteps 7))),
  response (.execute (.executed validObservation)),
  response (.execute (.internalError .worldCodeReferenceInvariant))
]

private def roundTrips : Bool :=
  responses.all fun expected =>
    match decodeResponseValue (encodeResponse expected) with
    | .ok actual => actual == expected
    | .error _ => false

private def errorAt {α : Type}
    (result : DecodeResult α)
    (pointer : String)
    (code : DecodeErrorCode) : Bool :=
  match result with
  | .error (.oracle path actualCode _) =>
      path.toPointer == pointer && actualCode == code
  | _ => false

private def publicErrorAt {α : Type}
    (result : Except ValidProtocolError α)
    (pointer code : String) : Bool :=
  match result with
  | .error error => error.path == pointer && error.code == code
  | .ok _ => false

private def envelopePrecedence : Bool :=
  let encoded := encodeResponse capabilityAcceptedResponse
  let rootUnknown := encoded.setObjVal! "aaa" true
  let idBeforeProfile := (encoded.setObjVal! "id" "")
    |>.setObjVal! "profile" (.mkObj [])
  let profileBeforeQuery := (encoded.setObjVal! "profile" (.mkObj []))
    |>.setObjVal! "query" "future"
  let queryBeforeSchema := (encoded.setObjVal! "query" "future")
    |>.setObjVal! "schema" "future"
  errorAt (decodeResponseValue rootUnknown) "/aaa" .unknownField &&
    errorAt (decodeResponseValue idBeforeProfile) "/id" .invalidRequestId &&
    errorAt (decodeResponseValue profileBeforeQuery)
      "/profile/digest" .missingField &&
    errorAt (decodeResponseValue queryBeforeSchema) "/query" .invalidTag

private def crossQueryRejection : Bool :=
  let capability := encodeResponse capabilityAcceptedResponse
  let core := encodeResponse <| response
    (.coreCheck (.accepted { resultType := .word }))
  let executed := encodeResponse <| response (.execute (.executed validObservation))
  let capabilityAsExecute := capability.setObjVal! "query" "execute"
  let coreAsCapability := core.setObjVal! "query" "capabilities"
  let executeAsCore := executed.setObjVal! "query" "coreCheck"
  errorAt (decodeResponseValue capabilityAsExecute)
      "/verdict/result" .unknownField &&
    errorAt (decodeResponseValue coreAsCapability)
      "/verdict/phase" .invalidTag &&
    errorAt (decodeResponseValue executeAsCore)
      "/verdict/observation" .unknownField

private def unknownFieldBeforeKind : Bool :=
  let encoded := encodeResponse capabilityAcceptedResponse
  let verdict := (encoded.getObjValD "verdict")
    |>.setObjVal! "kind" "future"
    |>.setObjVal! "zzz" true
  errorAt (decodeResponseValue <| encoded.setObjVal! "verdict" verdict)
    "/verdict/zzz" .unknownField

private def commonPhaseBeforeKind : Bool :=
  let capability := encodeResponse capabilityAcceptedResponse
  let capabilityVerdict := capability.getObjValD "verdict"
  let capabilityMissing := capability.setObjVal! "verdict" <| .mkObj [
    ("kind", "future"),
    ("result", capabilityVerdict.getObjValD "result")]
  let core := encodeResponse <| response
    (.coreCheck (.accepted { resultType := .word }))
  let coreVerdict := core.getObjValD "verdict"
  let coreMissing := core.setObjVal! "verdict" <| .mkObj [
    ("kind", "future"), ("result", coreVerdict.getObjValD "result")]
  errorAt (decodeResponseValue capabilityMissing)
      "/verdict/phase" .missingField &&
    errorAt (decodeResponseValue coreMissing)
      "/verdict/phase" .missingField

private def rejectedPrecedenceAndPhase : Bool :=
  let encoded := encodeResponse <| response (.coreCheck (.rejected coreRejection))
  let verdict := encoded.getObjValD "verdict"
  let diagnostic := match verdict.getObjValD "diagnostics" with
    | .arr values => values[0]!
    | _ => .null
  let arguments := diagnostic.getObjValD "arguments"
  let badDiagnostic := diagnostic.setObjVal! "arguments" <|
    arguments.setObjVal! "actual" false
  let badArguments := encoded.setObjVal! "verdict" <|
    (verdict.setObjVal! "diagnostics" (.arr #[badDiagnostic]))
      |>.setObjVal! "phase" "contractAdmission"
  let badPhase := encoded.setObjVal! "verdict" <|
    verdict.setObjVal! "phase" "contractAdmission"
  let emptyDiagnostics := encoded.setObjVal! "verdict" <|
    verdict.setObjVal! "diagnostics" (.arr #[])
  let coreFirst := match decodeResponseValue badArguments with
    | .error (.core error) =>
        error.path.toPointer == "/verdict/diagnostics/0/arguments/actual"
    | _ => false
  coreFirst && errorAt (decodeResponseValue badPhase)
      "/verdict/phase" .invalidTag &&
    errorAt (decodeResponseValue emptyDiagnostics)
      "/verdict/diagnostics" .invalidTag

private def rollbackObservationRejected : Bool :=
  let encoded := encodeResponse <| response (.execute (.executed validObservation))
  let verdict := encoded.getObjValD "verdict"
  let observation := verdict.getObjValD "observation"
  let value := observation.getObjValD "value"
  let journal := value.getObjValD "journal"
  let badJournal := journal.setObjVal! "createdAddresses" (.arr #[address])
  let badValue := value.setObjVal! "journal" badJournal
  let badObservation := observation.setObjVal! "value" badValue
  let bad := encoded.setObjVal! "verdict" <|
    verdict.setObjVal! "observation" badObservation
  errorAt (decodeResponseValue bad)
    "/verdict/observation/value/journal/createdAddresses" .invalidTag

private def canonicalizesNaturalsAndText : Bool :=
  let expected := response (.coreCheck (.inconclusive preflight))
  let encoded := encodeResponse expected
  let verdict := encoded.getObjValD "verdict"
  let decimalTwo : Lean.Json := .num { mantissa := 20, exponent := 1 }
  let noncanonical := encoded.setObjVal! "verdict" <|
    verdict.setObjVal! "consumed" decimalTwo
  let jsonExact := match decodeResponseValue noncanonical with
    | .ok actual => encodeResponse actual == encoded
    | .error _ => false
  let textExact := match canonicalizeResponseText
      (" \n" ++ encodeResponseText expected ++ " \n") with
    | .ok canonical => canonical == encodeResponseText expected
    | .error _ => false
  jsonExact && textExact

private def publicBoundaryRecoversId : Bool :=
  let bad := (encodeResponse capabilityAcceptedResponse).setObjVal!
    "query" "future"
  match decodeResponseJson bad with
  | .error error =>
      error.id == some requestId && error.path == "/query" &&
        error.code == "oracle.wire.invalid-tag"
  | .ok _ => false

private def allChecks : Bool :=
  roundTrips && envelopePrecedence && crossQueryRejection &&
    unknownFieldBeforeKind && commonPhaseBeforeKind &&
    rejectedPrecedenceAndPhase &&
    rollbackObservationRejected && canonicalizesNaturalsAndText &&
    publicBoundaryRecoversId

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ResponseDecode : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 response decoding changed")

end Tests.OracleV5ResponseDecode
