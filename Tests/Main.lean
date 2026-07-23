import Solcore

set_option autoImplicit false

open Solcore
open Solcore.Oracle

namespace Tests

def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    throw (IO.userError message)

def assertJsonRoundTrip {α : Type} [Lean.ToJson α] [Lean.FromJson α]
    (name : String) (value : α) : IO Unit := do
  let encoded := Lean.toJson value
  match (Lean.fromJson? encoded : Except String α) with
  | .error error =>
      throw (IO.userError s!"{name} did not decode: {error}")
  | .ok decoded =>
      assertTrue (Lean.toJson decoded == encoded) s!"{name} changed during JSON round-trip"

def isError {ε α : Type} : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

def validWorkspace : Workspace := {
  entry := "main.solc"
  sources := #[{
    path := "main.solc"
    content := "def main = 0"
  }]
}

def requestFor (kind : QueryKind) : Request := {
  schema := schemaVersion
  id := "test-request"
  spec := draftLanguage.id
  profile := {
    id := draftCoreProfile.id
    digest := draftCoreProfileDigest
  }
  workspace := if kind == .capabilities then none else some validWorkspace
  query := { kind }
}

def testProfile : IO Unit := do
  assertTrue draftCoreProfile.validationErrors.isEmpty
    s!"draft profile is invalid: {draftCoreProfile.validationErrors}"
  assertTrue (canonicalStd.files.size == 6) "canonical std must contain six .solc files"
  assertTrue
    (canonicalStd.manifestSha256 ==
      "3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22")
    "canonical std manifest digest changed"
  assertJsonRoundTrip "draft profile" draftCoreProfile
  let profileText ← IO.FS.readFile "profiles/solcore-0.1.0-draft.1-core.json"
  let profileJson ←
    match Lean.Json.parse profileText with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"profile JSON is invalid: {error}")
  assertTrue (profileJson == Lean.toJson draftCoreProfile)
    "checked-in profile JSON differs from the Lean profile"
  assertTrue rustStdCompatibilitySnapshot.validationErrors.isEmpty
    "Rust compatibility std snapshot metadata is invalid"

def testFeatureMatrix : IO Unit := do
  assertTrue featureMatrixIsComplete
    "feature matrix must contain every feature exactly once"
  assertTrue (featureMatrixRespectsProfile draftCoreProfile)
    "implemented features must be enabled and normative"

def testOracle : IO Unit := do
  assertJsonRoundTrip "request" (requestFor .check)
  assertJsonRoundTrip "capability report" capabilityReport
  for kind in QueryKind.all do
    let response ←
      match handle (requestFor kind) with
      | .ok response => pure response
      | .error error =>
          throw (IO.userError s!"valid {reprStr kind} request failed: {error.display}")
    let expected := if kind == .capabilities then VerdictKind.accepted else .unsupported
    assertTrue (response.verdict.kind == expected)
      s!"unexpected verdict for {reprStr kind}"
    assertTrue (response.profile == (requestFor kind).profile)
      "response must identify the exact request profile"
    assertTrue (response.query == kind) "response must identify the query"
    assertTrue (response.verdict.validationErrorsFor kind).isEmpty
      s!"invalid verdict for {reprStr kind}: {response.verdict.validationErrorsFor kind}"
    assertJsonRoundTrip s!"{reprStr kind} response" response
    match decodeResponse (Lean.toJson response) with
    | .ok _ => pure ()
    | .error error => throw (IO.userError s!"strict response decode failed: {error}")
  let malformedPathRequest : Request := {
    requestFor .check with
    workspace := some {
      entry := "../main.solc"
      sources := #[{
        path := "../main.solc"
        content := ""
      }]
    }
  }
  assertTrue (isError (handle malformedPathRequest))
    "parent-relative workspace paths must be protocol errors"
  let unknownSchema := { requestFor .capabilities with schema := "solcore-oracle/v999" }
  assertTrue (isError (handle unknownSchema)) "unknown schemas must be protocol errors"
  let requestWithUnknownField :=
    (Lean.toJson (requestFor .capabilities)).setObjVal! "surprise" true
  assertTrue (isError (decodeRequest requestWithUnknownField))
    "unknown request fields must be protocol errors"
  let requestWithoutLimits :=
    (Lean.toJson (requestFor .capabilities)).setObjVal! "limits" .null
  assertTrue (isError (decodeRequest requestWithoutLimits))
    "null limits must not be accepted"
  let diagnostic : Diagnostic := {
    code := "test-error"
    severity := .error
    phase := .checking
    primary := {
      source := "main.solc"
      startByte := 0
      endByte := 1
    }
  }
  let verdicts : Array (QueryKind × Verdict) := #[
    (.capabilities, .accepted .protocol {
      schema := capabilitiesSchema
      value := Lean.toJson capabilityReport
    }),
    (.check, .rejected .checking diagnostic #[]),
    (.elaborate, .unsupported .elaboration #[.modules]),
    (.eval, .inconclusive .evaluation .evaluationSteps 10 (some 10)),
    (.eval, .executed {
      schema := "solcore-value-observation/v1"
      value := .null
    }),
    (.check, .internalError (some .checking) "test-invariant")
  ]
  for (query, verdict) in verdicts do
    assertTrue (verdict.validationErrorsFor query).isEmpty
      s!"sample verdict is invalid: {verdict.validationErrorsFor query}"
    assertJsonRoundTrip "verdict" verdict
  let capabilityResponse ←
    match handle (requestFor .capabilities) with
    | .ok response => pure response
    | .error error =>
        throw (IO.userError s!"valid capabilities request failed: {error.display}")
  let capabilityResponseJson := Lean.toJson capabilityResponse
  assertTrue
    (isError (decodeResponse (capabilityResponseJson.setObjVal! "id" "")))
    "empty response ids must be rejected"
  let capabilityVerdictJson := capabilityResponseJson.getObjValD "verdict"
  let capabilityResultJson := capabilityVerdictJson.getObjValD "result"
  let resultWithUnknownField := capabilityResultJson.setObjVal! "surprise" true
  let verdictWithUnknownResultField :=
    capabilityVerdictJson.setObjVal! "result" resultWithUnknownField
  assertTrue
    (isError (decodeResponse
      (capabilityResponseJson.setObjVal! "verdict" verdictWithUnknownResultField)))
    "unknown result payload fields must be rejected"
  let resultWithNullValue := capabilityResultJson.setObjVal! "value" .null
  let verdictWithNullCapability :=
    capabilityVerdictJson.setObjVal! "result" resultWithNullValue
  assertTrue
    (isError (decodeResponse
      (capabilityResponseJson.setObjVal! "verdict" verdictWithNullCapability)))
    "capabilities result values must decode as CapabilityReport"
  let reportWithUnknownField :=
    (capabilityResultJson.getObjValD "value").setObjVal! "surprise" true
  let resultWithUnknownReportField :=
    capabilityResultJson.setObjVal! "value" reportWithUnknownField
  let verdictWithUnknownReportField :=
    capabilityVerdictJson.setObjVal! "result" resultWithUnknownReportField
  assertTrue
    (isError (decodeResponse
      (capabilityResponseJson.setObjVal! "verdict" verdictWithUnknownReportField)))
    "unknown capability report fields must be rejected"
  let checkResponse ←
    match handle (requestFor .check) with
    | .ok response => pure response
    | .error error =>
        throw (IO.userError s!"valid check request failed: {error.display}")
  let diagnosticWithUnknownField :=
    (Lean.toJson diagnostic).setObjVal! "surprise" true
  let rejectedWithUnknownDiagnostic := Lean.Json.mkObj [
    ("kind", Lean.toJson VerdictKind.rejected),
    ("phase", Lean.toJson Phase.checking),
    ("diagnostics", Lean.Json.arr #[diagnosticWithUnknownField])
  ]
  assertTrue
    (isError (decodeResponse
      ((Lean.toJson checkResponse).setObjVal! "verdict" rejectedWithUnknownDiagnostic)))
    "unknown diagnostic fields must be rejected"
  let spanWithUnknownField :=
    (Lean.toJson diagnostic.primary).setObjVal! "surprise" true
  let diagnosticWithUnknownSpan :=
    (Lean.toJson diagnostic).setObjVal! "primary" spanWithUnknownField
  let rejectedWithUnknownSpan := Lean.Json.mkObj [
    ("kind", Lean.toJson VerdictKind.rejected),
    ("phase", Lean.toJson Phase.checking),
    ("diagnostics", Lean.Json.arr #[diagnosticWithUnknownSpan])
  ]
  assertTrue
    (isError (decodeResponse
      ((Lean.toJson checkResponse).setObjVal! "verdict" rejectedWithUnknownSpan)))
    "unknown source span fields must be rejected"
  let evalResponse ←
    match handle (requestFor .eval) with
    | .ok response => pure response
    | .error error =>
        throw (IO.userError s!"valid eval request failed: {error.display}")
  let observationWithUnknownField :=
    (Lean.toJson (show ObservationPayload from {
      schema := "solcore-value-observation/v1"
      value := .null
    })).setObjVal! "surprise" true
  let executedWithUnknownObservation := Lean.Json.mkObj [
    ("kind", Lean.toJson VerdictKind.executed),
    ("observation", observationWithUnknownField)
  ]
  assertTrue
    (isError (decodeResponse
      ((Lean.toJson evalResponse).setObjVal! "verdict" executedWithUnknownObservation)))
    "unknown observation payload fields must be rejected"
  let malformedOutput := processJsonLine "{"
  assertTrue (malformedOutput.getObjValD "kind" == "protocolError")
    "malformed JSON must produce a protocolError record"
  let recoveredOutput :=
    processJsonLine (Lean.toJson (requestFor .capabilities)).compress
  let recoveredVerdict := recoveredOutput.getObjValD "verdict"
  assertTrue (recoveredVerdict.getObjValD "kind" == "accepted")
    "a valid record after a malformed record must still be accepted"
  let encodedRequest := (Lean.toJson (requestFor .capabilities)).compress
  let duplicateIdRequest :=
    encodedRequest.replace
      "\"id\":\"test-request\""
      "\"id\":\"first\",\"id\":\"second\""
  let duplicateIdOutput := processJsonLine duplicateIdRequest
  assertTrue (duplicateIdOutput.getObjValD "kind" == "protocolError")
    "duplicate JSON object keys must be rejected"
  let shapeErrorOutput := processJsonLine requestWithUnknownField.compress
  assertTrue (shapeErrorOutput.getObjValD "id" == "test-request")
    "shape errors must preserve a usable request id"
  for unsafePath in
      ["/main.solc", "../main.solc", "a/./main.solc", "a//main.solc", "C:/main.solc",
        "a\\main.solc"] do
    assertTrue (!isSafeSourcePath unsafePath) s!"unsafe path was accepted: {unsafePath}"

def testSchemaJson : IO Unit := do
  for path in
      ["schema/oracle-v1.schema.json", "metadata/baselines.json",
        "metadata/standard-library.json", "profiles/manifest.json",
        "Tests/golden/wire-manifest.json"] do
    let text ← IO.FS.readFile path
    match Lean.Json.parse text with
    | .ok _ => pure ()
    | .error error => throw (IO.userError s!"{path} is invalid JSON: {error}")
  let requestText ← IO.FS.readFile "Tests/golden/check-request.ndjson"
  let requestJson ←
    match StrictJson.parse requestText.trimAscii.copy with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"golden request is invalid: {error}")
  match decodeRequest requestJson with
  | .ok _ => pure ()
  | .error error => throw (IO.userError s!"golden request violates the wire contract: {error}")
  let responseText ← IO.FS.readFile "Tests/golden/check-response.ndjson"
  let responseJson ←
    match StrictJson.parse responseText.trimAscii.copy with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"golden response is invalid: {error}")
  match decodeResponse responseJson with
  | .ok response =>
      assertTrue (Lean.toJson response == responseJson)
        "golden response is not the canonical Lean encoding"
  | .error error => throw (IO.userError s!"golden response violates the wire contract: {error}")

def run : IO Unit := do
  testProfile
  testFeatureMatrix
  testOracle
  testSchemaJson

end Tests

def main : IO UInt32 := do
  Tests.run
  IO.println "solcore-lean M0 tests passed"
  return 0
