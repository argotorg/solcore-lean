import Solcore.Oracle.V5.Capabilities
import Solcore.Oracle.V5.ObservationCodec
import Solcore.Oracle.V5.Wire.Encode

/-! Canonical JSON encoding for typed Oracle v5 responses. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

private def jsonArray (values : List Lean.Json) : Lean.Json :=
  .arr values.toArray

private def encodeStrings (values : Array String) : Lean.Json :=
  .arr <| values.map Lean.Json.str

def encodeQueryKind : QueryKind → Lean.Json
  | .capabilities => "capabilities"
  | .coreCheck => "coreCheck"
  | .execute => "execute"

def encodePhase : Phase → Lean.Json
  | .protocol => "protocol"
  | .requestPreflight => "requestPreflight"
  | .coreDecoding => "coreDecoding"
  | .coreChecking => "coreChecking"
  | .contractAdmission => "contractAdmission"
  | .worldValidation => "worldValidation"
  | .environmentValidation => "environmentValidation"
  | .probeValidation => "probeValidation"
  | .rootInstallation => "rootInstallation"
  | .contractExecution => "contractExecution"
  | .observationEncoding => "observationEncoding"

def encodeResourceKind : ResourceKind → Lean.Json
  | .jsonDepth => "jsonDepth"
  | .jsonNodes => "jsonNodes"
  | .coreDepth => "coreDepth"
  | .coreNodes => "coreNodes"
  | .scenarioEntries => "scenarioEntries"
  | .identifierBytes => "identifierBytes"
  | .calldataBytes => "calldataBytes"
  | .evaluationSteps => "evaluationSteps"

private def encodeOptionalPhase : Option Phase → Lean.Json
  | none => .null
  | some phase => encodePhase phase

def encodeDiagnostic (diagnostic : Diagnostic) : Lean.Json :=
  .mkObj [
    ("code", diagnostic.code),
    ("severity", diagnostic.severity),
    ("phase", encodePhase diagnostic.phase),
    ("path", jsonArray <| diagnostic.path.map Lean.Json.str),
    ("arguments", diagnostic.arguments),
    ("display", .null)
  ]

def encodeInternalError (error : InternalError) : Lean.Json :=
  .mkObj [
    ("phase", encodeOptionalPhase error.phase),
    ("code", error.code)
  ]

private def encodeQueryKinds (values : Array QueryKind) : Lean.Json :=
  .arr <| values.map encodeQueryKind

/-- The capability payload is completely derived from the canonical marker. -/
def encodeCapabilityReport (report : CapabilityReport) : Lean.Json :=
  .mkObj [
    ("schema", report.schema),
    ("spec", report.spec),
    ("profile", Lean.toJson report.profile),
    ("profileDigest", report.profileDigest),
    ("coreSchema", report.coreSchema),
    ("checkResultSchema", report.checkResultSchema),
    ("executionSchema", report.executionSchema),
    ("stateObservationSchema", report.stateObservationSchema),
    ("contractProfiles", encodeStrings report.contractProfiles),
    ("abiProfiles", encodeStrings report.abiProfiles),
    ("implementedQueries", encodeQueryKinds report.implementedQueries),
    ("maxNestedCallDepth", report.maxNestedCallDepth),
    ("observationKinds", encodeStrings report.observationKinds),
    ("defaultLimits", encodeLimits report.defaultLimits),
    ("baselines", Lean.toJson report.baselines),
    ("features", Lean.toJson report.features)
  ]

def encodeCapabilityResult (report : CapabilityReport) : Lean.Json :=
  .mkObj [
    ("schema", capabilitiesSchema),
    ("value", encodeCapabilityReport report)
  ]

def encodeCoreCheckResult (result : CoreCheckResult) : Lean.Json :=
  .mkObj [
    ("schema", checkResultSchema),
    ("value", .mkObj [
      ("resultType", Solcore.Core.Wire.V3.encodeType result.resultType)
    ])
  ]

private def encodeInconclusive (exhaustion : Exhaustion) : Lean.Json :=
  .mkObj [
    ("kind", "inconclusive"),
    ("phase", encodePhase exhaustion.phase),
    ("resource", encodeResourceKind exhaustion.resource),
    ("limit", exhaustion.limit),
    ("consumed", exhaustion.consumed)
  ]

private def encodeInternalErrorVerdict
    (error : InternalError) : Lean.Json :=
  .mkObj [
    ("kind", "internalError"),
    ("phase", encodeOptionalPhase error.phase),
    ("code", error.code)
  ]

private def encodeRejected (diagnostic : Diagnostic) : Lean.Json :=
  .mkObj [
    ("kind", "rejected"),
    ("phase", encodePhase diagnostic.phase),
    ("diagnostics", .arr #[encodeDiagnostic diagnostic])
  ]

def encodeCapabilitiesVerdict : CapabilitiesVerdict → Lean.Json
  | .accepted report => .mkObj [
      ("kind", "accepted"),
      ("phase", "protocol"),
      ("result", encodeCapabilityResult report)
    ]
  | .inconclusive exhaustion => encodeInconclusive (.preflight exhaustion)
  | .internalError error => encodeInternalErrorVerdict error

def encodeCoreCheckVerdict : CoreCheckVerdict → Lean.Json
  | .accepted result => .mkObj [
      ("kind", "accepted"),
      ("phase", "coreChecking"),
      ("result", encodeCoreCheckResult result)
    ]
  | .rejected rejection => encodeRejected rejection.diagnostic
  | .inconclusive exhaustion => encodeInconclusive (.preflight exhaustion)
  | .internalError error => encodeInternalErrorVerdict error

def encodeExecuteVerdict : ExecuteVerdict → Lean.Json
  | .rejected rejection => encodeRejected rejection.diagnostic
  | .inconclusive exhaustion => encodeInconclusive exhaustion
  | .executed observation => .mkObj [
      ("kind", "executed"),
      ("observation",
        Solcore.Oracle.V5.encodeExecutionObservation observation)
    ]
  | .internalError error => encodeInternalErrorVerdict error

def encodeResponseBody : ResponseBody → Lean.Json
  | .capabilities verdict => encodeCapabilitiesVerdict verdict
  | .coreCheck verdict => encodeCoreCheckVerdict verdict
  | .execute verdict => encodeExecuteVerdict verdict

/-- Encode a query-compatible typed response with the fixed v5 envelope. -/
def encodeResponse (response : Response) : Lean.Json :=
  .mkObj [
    ("schema", response.schema),
    ("id", encodeRequestId response.id),
    ("spec", response.spec),
    ("profile", encodeProfile response.profile),
    ("query", encodeQueryKind response.queryKind),
    ("verdict", encodeResponseBody response.body)
  ]

def encodeResponseText (response : Response) : String :=
  (encodeResponse response).compress

def encodeProtocolError
    (error : Solcore.Oracle.V5.ProtocolError) : Lean.Json :=
  .mkObj [
    ("kind", error.kind),
    ("schema", error.schema),
    ("id", match error.id with
      | none => .null
      | some id => encodeRequestId id),
    ("code", error.code),
    ("path", error.path),
    ("arguments", error.arguments),
    ("display", error.display)
  ]

def encodeProtocolErrorText
    (error : Solcore.Oracle.V5.ProtocolError) : String :=
  (encodeProtocolError error).compress

end Solcore.Oracle.V5.Wire
