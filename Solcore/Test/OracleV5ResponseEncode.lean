import Solcore.Oracle.V5.Wire.ResponseEncode

/-! Exact-wire regressions for canonical Oracle v5 response encoding. -/

set_option autoImplicit false

namespace Tests.OracleV5ResponseEncode

open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire

private def requestId : RequestId := ⟨"request-id", by decide⟩

private def exactObject (json : Lean.Json) (fields : List String) : Bool :=
  match ensureExactObject .root json fields fields with
  | .ok _ => true
  | .error _ => false

private def fieldEq
    (json : Lean.Json)
    (name : String)
    (expected : Lean.Json) : Bool :=
  match json.getObjVal? name with
  | .ok actual => actual == expected
  | .error _ => false

private def phaseAndResourceTagsExact : Bool :=
  (Lean.Json.arr <| #[
    Phase.protocol, .requestPreflight, .coreDecoding, .coreChecking,
    .contractAdmission, .worldValidation, .environmentValidation,
    .probeValidation, .rootInstallation, .contractExecution,
    .observationEncoding
  ].map encodePhase).compress ==
    "[\"protocol\",\"requestPreflight\",\"coreDecoding\",\"coreChecking\"," ++
    "\"contractAdmission\",\"worldValidation\",\"environmentValidation\"," ++
    "\"probeValidation\",\"rootInstallation\",\"contractExecution\"," ++
    "\"observationEncoding\"]" &&
  (Lean.Json.arr <| #[
    ResourceKind.jsonDepth, .jsonNodes, .coreDepth, .coreNodes,
    .scenarioEntries, .identifierBytes, .calldataBytes, .evaluationSteps
  ].map encodeResourceKind).compress ==
    "[\"jsonDepth\",\"jsonNodes\",\"coreDepth\",\"coreNodes\"," ++
    "\"scenarioEntries\",\"identifierBytes\",\"calldataBytes\"," ++
    "\"evaluationSteps\"]"

private def diagnostic : Diagnostic := {
  code := "oracle.v5.root.target-absent"
  phase := .rootInstallation
  path := ["world", "accounts",
    "0x0000000000000000000000000000000000000001"]
  arguments := .mkObj [
    ("target", "0x0000000000000000000000000000000000000001")
  ]
}

private def diagnosticAndRejectionExact : Bool :=
  (encodeDiagnostic diagnostic).compress ==
    "{\"arguments\":{\"target\":\"0x0000000000000000000000000000000000000001\"}," ++
    "\"code\":\"oracle.v5.root.target-absent\",\"display\":null," ++
    "\"path\":[\"world\",\"accounts\",\"0x0000000000000000000000000000000000000001\"]," ++
    "\"phase\":\"rootInstallation\",\"severity\":\"error\"}" &&
  (encodeExecuteVerdict (.rejected diagnostic)).compress ==
    "{\"diagnostics\":[" ++ (encodeDiagnostic diagnostic).compress ++
    "],\"kind\":\"rejected\",\"phase\":\"rootInstallation\"}"

private def coreAccepted : Response := {
  id := requestId
  body := .coreCheck (.accepted { resultType := .word })
}

private def coreAcceptedEnvelopeExact : Bool :=
  encodeResponseText coreAccepted ==
    "{\"id\":\"request-id\",\"profile\":{" ++
    "\"digest\":\"sha256:da3d49b830d25705634cfda568691f1f12fe5a7d038bd0b7ca5839134c1073d5\"," ++
    "\"id\":\"contract-m3a-v1\"},\"query\":\"coreCheck\"," ++
    "\"schema\":\"solcore-oracle/v5\",\"spec\":\"solcore/0.1.0-draft.5\"," ++
    "\"verdict\":{\"kind\":\"accepted\",\"phase\":\"coreChecking\"," ++
    "\"result\":{\"schema\":\"solcore-core-check-result/v3\"," ++
    "\"value\":{\"resultType\":\"word\"}}}}"

private def preflightExhaustion : Exhaustion :=
  .preflight ⟨.jsonDepth, 5, 6, by decide⟩

private def inconclusiveVerdictsExact : Bool :=
  (encodeCoreCheckVerdict (.inconclusive preflightExhaustion)).compress ==
      "{\"consumed\":6,\"kind\":\"inconclusive\",\"limit\":5," ++
      "\"phase\":\"requestPreflight\",\"resource\":\"jsonDepth\"}" &&
    (encodeExecuteVerdict
      (.inconclusive (.evaluationSteps 12))).compress ==
      "{\"consumed\":12,\"kind\":\"inconclusive\",\"limit\":12," ++
      "\"phase\":\"contractExecution\",\"resource\":\"evaluationSteps\"}"

private def internalErrorsExact : Bool :=
  (Lean.Json.arr #[
    encodeCoreCheckVerdict (.internalError .coreWireProjectionFailed),
    encodeExecuteVerdict (.internalError .worldCodeReferenceInvariant),
    encodeCapabilitiesVerdict (.internalError .oracleResponseInvariant)
  ]).compress ==
    "[{\"code\":\"core-wire-projection-failed\",\"kind\":\"internalError\"," ++
    "\"phase\":\"observationEncoding\"},{\"code\":" ++
    "\"world-code-reference-invariant\",\"kind\":\"internalError\"," ++
    "\"phase\":\"observationEncoding\"},{\"code\":" ++
    "\"oracle-response-invariant\",\"kind\":\"internalError\",\"phase\":null}]"

private def capabilityFields : List String := [
  "schema", "spec", "profile", "profileDigest", "coreSchema",
  "checkResultSchema", "executionSchema", "stateObservationSchema",
  "contractProfiles", "abiProfiles", "implementedQueries",
  "maxNestedCallDepth", "observationKinds", "defaultLimits",
  "baselines", "features"
]

private def capabilityReportExact : Bool :=
  let encoded := encodeCapabilityReport capabilityReport
  exactObject encoded capabilityFields &&
    fieldEq encoded "schema" capabilitiesSchema &&
    fieldEq encoded "spec" Solcore.m3aLanguage.id &&
    fieldEq encoded "profile" (Lean.toJson Solcore.m3aContractProfile) &&
    fieldEq encoded "profileDigest" Solcore.m3aContractProfileDigest &&
    fieldEq encoded "coreSchema" Solcore.Core.Wire.V3.schemaVersion &&
    fieldEq encoded "checkResultSchema" checkResultSchema &&
    fieldEq encoded "executionSchema" executionSchema &&
    fieldEq encoded "stateObservationSchema" stateObservationSchema &&
    fieldEq encoded "contractProfiles" (.arr #["returnWord", "wordOutcomeV1"]) &&
    fieldEq encoded "abiProfiles" (.arr #["staticWordAbiV1"]) &&
    fieldEq encoded "implementedQueries"
      (.arr #["capabilities", "coreCheck", "execute"]) &&
    fieldEq encoded "maxNestedCallDepth" 1 &&
    fieldEq encoded "observationKinds"
      (.arr #["accountPresence", "storage", "balance", "nonce", "code"]) &&
    fieldEq encoded "defaultLimits" (encodeLimits Limits.default) &&
    fieldEq encoded "baselines" (Lean.toJson Solcore.implementationBaselines) &&
    fieldEq encoded "features" (Lean.toJson Solcore.m3aContractFeatureMatrix)

private def emptyObservation : ExecutionObservation := {
  outcome := .preflightRejected .senderAbsent
  journal := { logs := [], createdAddresses := [] }
  state := { probes := [] }
}

private def executedObservationExact : Bool :=
  (encodeExecuteVerdict (.executed emptyObservation)).compress ==
    "{\"kind\":\"executed\",\"observation\":{" ++
    "\"schema\":\"solcore-contract-execution/v1\",\"value\":{" ++
    "\"journal\":{\"createdAddresses\":[],\"logs\":[]}," ++
    "\"outcome\":{\"kind\":\"preflightRejected\",\"reason\":\"senderAbsent\"}," ++
    "\"state\":{\"probes\":[],\"schema\":\"solcore-world-state-observation/v1\"}}}}"

private def protocolErrorsExact : Bool :=
  let error : Solcore.Oracle.V5.ProtocolError := {
    code := "oracle.wire.unknown-field"
    path := "/query/future"
    arguments := .mkObj [("field", "future")]
    display := "invalid Oracle v5 value"
  }
  encodeProtocolErrorText error ==
    "{\"arguments\":{\"field\":\"future\"}," ++
    "\"code\":\"oracle.wire.unknown-field\"," ++
    "\"display\":\"invalid Oracle v5 value\",\"id\":null," ++
    "\"kind\":\"protocolError\",\"path\":\"/query/future\"," ++
    "\"schema\":\"solcore-oracle/v5\"}" &&
  encodeProtocolErrorText { error with id := some requestId } ==
    "{\"arguments\":{\"field\":\"future\"}," ++
    "\"code\":\"oracle.wire.unknown-field\"," ++
    "\"display\":\"invalid Oracle v5 value\",\"id\":\"request-id\"," ++
    "\"kind\":\"protocolError\",\"path\":\"/query/future\"," ++
    "\"schema\":\"solcore-oracle/v5\"}"

private def allChecks : Bool :=
  phaseAndResourceTagsExact && diagnosticAndRejectionExact &&
    coreAcceptedEnvelopeExact && inconclusiveVerdictsExact &&
    internalErrorsExact && capabilityReportExact &&
    executedObservationExact && protocolErrorsExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ResponseEncode : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 response JSON encoder changed")

end Tests.OracleV5ResponseEncode
