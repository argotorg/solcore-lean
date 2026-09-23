import Solcore.Oracle.V5.Wire.CapabilityDecode
import Solcore.Oracle.V5.Wire.ObservationDecode
import Solcore.Oracle.V5.Wire.Protocol
import Solcore.Oracle.V5.Wire.RequestShape
import Solcore.Oracle.V5.Wire.ResponseEncode
import Solcore.Oracle.V5.Wire.ScenarioDiagnostic

/-! Strict query-indexed decoding for complete Oracle v5 responses. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

private def decodeVerdictKindAt
    (path : Path)
    (json : Lean.Json)
    (allowed : Array String) : DecodeResult String := do
  let kind ← decodeStringAt path json
  if allowed.contains kind then pure kind
  else invalidTagAt path kind (.arr <| allowed.map Lean.Json.str)

private def requireEncodedPhase
    (path : Path)
    (actual expected : Phase) : DecodeResult Unit :=
  unless actual == expected do
    invalidTagAt path (encodePhase actual) (encodePhase expected)

private def decodeSingletonAt {α : Type}
    (decode : Path → Lean.Json → DecodeResult α)
    (path : Path)
    (json : Lean.Json) : DecodeResult α :=
  match json with
  | .arr values =>
      if length : values.size = 1 then
        decode (path.index 0) values[0]
      else
        invalidTagAt path (.mkObj [("length", values.size)])
          (.mkObj [("length", 1)])
  | _ => failAt path .expectedArray (expectedArguments "array" json)

private def decodeCapabilitiesAcceptedAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CapabilitiesVerdict := do
  ensureExactObject path json
    ["kind", "phase", "result"] ["kind", "phase", "result"]
  requireLiteralAt (path.field "kind")
    (← requireField path json "kind") "accepted"
  requireLiteralAt (path.field "phase")
    (← requireField path json "phase") "protocol"
  let report ← decodeCapabilityResultAt (path.field "result")
    (← requireField path json "result")
  pure (.accepted report)

private def decodeCoreAcceptedAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CoreCheckVerdict := do
  ensureExactObject path json
    ["kind", "phase", "result"] ["kind", "phase", "result"]
  requireLiteralAt (path.field "kind")
    (← requireField path json "kind") "accepted"
  requireLiteralAt (path.field "phase")
    (← requireField path json "phase") "coreChecking"
  let result ← decodeCoreCheckResultAt (path.field "result")
    (← requireField path json "result")
  pure (.accepted result)

private def decodeCoreRejectedAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CoreCheckVerdict := do
  ensureExactObject path json
    ["diagnostics", "kind", "phase"] ["diagnostics", "kind", "phase"]
  let rejection ← decodeSingletonAt decodeCoreCheckRejectionAt
    (path.field "diagnostics") (← requireField path json "diagnostics")
  requireLiteralAt (path.field "kind")
    (← requireField path json "kind") "rejected"
  let phasePath := path.field "phase"
  let phase ← decodePhaseAt phasePath (← requireField path json "phase")
  requireEncodedPhase phasePath phase rejection.diagnostic.phase
  pure (.rejected rejection)

private def decodeExecuteRejectedAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ExecuteVerdict := do
  ensureExactObject path json
    ["diagnostics", "kind", "phase"] ["diagnostics", "kind", "phase"]
  let rejection ← decodeSingletonAt decodeExecuteRejectionAt
    (path.field "diagnostics") (← requireField path json "diagnostics")
  requireLiteralAt (path.field "kind")
    (← requireField path json "kind") "rejected"
  let phasePath := path.field "phase"
  let phase ← decodePhaseAt phasePath (← requireField path json "phase")
  requireEncodedPhase phasePath phase rejection.diagnostic.phase
  pure (.rejected rejection)

private def decodeCapabilitiesVerdictAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CapabilitiesVerdict := do
  let allowedFields := [
    "code", "consumed", "kind", "limit", "phase", "resource", "result"]
  ensureExactObject path json allowedFields ["kind", "phase"]
  let kind ← decodeVerdictKindAt (path.field "kind")
    (← requireField path json "kind")
    #["accepted", "inconclusive", "internalError"]
  match kind with
  | "accepted" => decodeCapabilitiesAcceptedAt path json
  | "inconclusive" => do
      let exhaustion ← decodeInconclusiveAt false path json
      match exhaustion with
      | .preflight value => pure (.inconclusive value)
      | .evaluationSteps _ =>
          invalidTagAt (path.field "resource")
            (Lean.Json.str "evaluationSteps") (Lean.Json.str "preflight-resource")
  | "internalError" =>
      .internalError <$> decodeInternalErrorVerdictAt path json
  | _ => invalidTagAt (path.field "kind") kind .null

private def decodeCoreVerdictAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CoreCheckVerdict := do
  let allowedFields := [
    "code", "consumed", "diagnostics", "kind", "limit", "phase",
    "resource", "result"]
  ensureExactObject path json allowedFields ["kind", "phase"]
  let kind ← decodeVerdictKindAt (path.field "kind")
    (← requireField path json "kind")
    #["accepted", "rejected", "inconclusive", "internalError"]
  match kind with
  | "accepted" => decodeCoreAcceptedAt path json
  | "rejected" => decodeCoreRejectedAt path json
  | "inconclusive" => do
      let exhaustion ← decodeInconclusiveAt false path json
      match exhaustion with
      | .preflight value => pure (.inconclusive value)
      | .evaluationSteps _ =>
          invalidTagAt (path.field "resource")
            (Lean.Json.str "evaluationSteps") (Lean.Json.str "preflight-resource")
  | "internalError" =>
      .internalError <$> decodeInternalErrorVerdictAt path json
  | _ => invalidTagAt (path.field "kind") kind .null

private def decodeExecutedAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ExecuteVerdict := do
  ensureExactObject path json
    ["kind", "observation"] ["kind", "observation"]
  requireLiteralAt (path.field "kind")
    (← requireField path json "kind") "executed"
  let observation ← decodeExecutionObservationAt (path.field "observation")
    (← requireField path json "observation")
  pure (.executed observation)

private def decodeExecuteVerdictAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ExecuteVerdict := do
  let allowedFields := [
    "code", "consumed", "diagnostics", "kind", "limit", "observation",
    "phase", "resource"]
  ensureExactObject path json allowedFields ["kind"]
  let kind ← decodeVerdictKindAt (path.field "kind")
    (← requireField path json "kind")
    #["rejected", "inconclusive", "executed", "internalError"]
  match kind with
  | "rejected" => decodeExecuteRejectedAt path json
  | "inconclusive" =>
      .inconclusive <$> decodeInconclusiveAt true path json
  | "executed" => decodeExecutedAt path json
  | "internalError" =>
      .internalError <$> decodeInternalErrorVerdictAt path json
  | _ => invalidTagAt (path.field "kind") kind .null

private def decodeResponseBodyAt
    (query : QueryKind)
    (path : Path)
    (json : Lean.Json) : DecodeResult ResponseBody :=
  match query with
  | .capabilities => .capabilities <$> decodeCapabilitiesVerdictAt path json
  | .coreCheck => .coreCheck <$> decodeCoreVerdictAt path json
  | .execute => .execute <$> decodeExecuteVerdictAt path json

/-- Decode a parsed response while preserving Oracle/Core error ownership. -/
def decodeResponseValue
    (json : Lean.Json) : DecodeResult Response := do
  let path := Path.root
  let fields := ["id", "profile", "query", "schema", "spec", "verdict"]
  ensureExactObject path json fields fields
  let id ← decodeRequestIdAt (path.field "id")
    (← requireField path json "id")
  let _ ← decodeProfileAt (path.field "profile")
    (← requireField path json "profile")
  let query ← decodeQueryKindAt (path.field "query")
    (← requireField path json "query")
  let schemaPath := path.field "schema"
  let schema ← decodeStringAt schemaPath (← requireField path json "schema")
  unless schema == schemaVersion do
    failAt schemaPath .invalidSchema (.mkObj [
      ("expected", schemaVersion), ("actual", schema)
    ])
  let specPath := path.field "spec"
  let spec ← decodeStringAt specPath (← requireField path json "spec")
  unless spec == Solcore.m3aLanguage.id do
    failAt specPath .invalidSpec (.mkObj [
      ("expected", Solcore.m3aLanguage.id), ("actual", spec)
    ])
  let body ← decodeResponseBodyAt query (path.field "verdict")
    (← requireField path json "verdict")
  pure { id, body }

/-- Public parsed-JSON response decoder with recoverable request identity. -/
def decodeResponseJson
    (json : Lean.Json) : Except ValidProtocolError Response :=
  (decodeResponseValue json).mapError
    (fun error => error.toPublic (recoverRequestId? json))

/-- Duplicate-rejecting direct-text response decoder. -/
def decodeResponseText
    (text : String) : Except ValidProtocolError Response :=
  decodeDirectTextWith decodeResponseValue text

/-- Strictly decode and re-emit the unique canonical response spelling. -/
def canonicalizeResponseText
    (text : String) : Except ValidProtocolError String := do
  pure (encodeResponseText (← decodeResponseText text))

end Solcore.Oracle.V5.Wire
