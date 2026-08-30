import Solcore.Core.Wire.V3
import Solcore.Oracle.V5.Wire.JsonBudget
import Solcore.Oracle.V5.Wire.ObservationDecode
import Solcore.Oracle.V5.Wire.ResponseEncode

/-! Closed component decoding for typed Oracle v5 responses. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

def decodeQueryKindAt
    (path : Path)
    (json : Lean.Json) : DecodeResult QueryKind := do
  let value ← decodeStringAt path json
  match value with
  | "capabilities" => pure .capabilities
  | "coreCheck" => pure .coreCheck
  | "execute" => pure .execute
  | _ => invalidTagAt path value <| .arr #[
      "capabilities", "coreCheck", "execute"
    ]

def decodePhaseAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Phase := do
  let value ← decodeStringAt path json
  match value with
  | "protocol" => pure .protocol
  | "requestPreflight" => pure .requestPreflight
  | "coreDecoding" => pure .coreDecoding
  | "coreChecking" => pure .coreChecking
  | "contractAdmission" => pure .contractAdmission
  | "worldValidation" => pure .worldValidation
  | "environmentValidation" => pure .environmentValidation
  | "probeValidation" => pure .probeValidation
  | "rootInstallation" => pure .rootInstallation
  | "contractExecution" => pure .contractExecution
  | "observationEncoding" => pure .observationEncoding
  | _ => invalidTagAt path value <| .arr #[
      "protocol", "requestPreflight", "coreDecoding", "coreChecking",
      "contractAdmission", "worldValidation", "environmentValidation",
      "probeValidation", "rootInstallation", "contractExecution",
      "observationEncoding"
    ]

def decodeResourceKindAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ResourceKind := do
  let value ← decodeStringAt path json
  match value with
  | "jsonDepth" => pure .jsonDepth
  | "jsonNodes" => pure .jsonNodes
  | "coreDepth" => pure .coreDepth
  | "coreNodes" => pure .coreNodes
  | "scenarioEntries" => pure .scenarioEntries
  | "identifierBytes" => pure .identifierBytes
  | "calldataBytes" => pure .calldataBytes
  | "evaluationSteps" => pure .evaluationSteps
  | _ => invalidTagAt path value <| .arr #[
      "jsonDepth", "jsonNodes", "coreDepth", "coreNodes",
      "scenarioEntries", "identifierBytes", "calldataBytes",
      "evaluationSteps"
    ]

private def decodeJsonObjectAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Lean.Json :=
  match json with
  | .obj _ => pure json
  | _ => failAt path .expectedObject (expectedArguments "object" json)

def decodeDiagnosticAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Diagnostic := do
  let fields := ["arguments", "code", "display", "path", "phase", "severity"]
  ensureExactObject path json fields fields
  let arguments ← decodeJsonObjectAt (path.field "arguments")
    (← requireField path json "arguments")
  let code ← decodeStringAt (path.field "code")
    (← requireField path json "code")
  let displayPath := path.field "display"
  let display ← requireField path json "display"
  unless display == .null do
    invalidTagAt displayPath display .null
  let semanticPath ← decodeArrayAt decodeStringAt (path.field "path")
    (← requireField path json "path")
  let phase ← decodePhaseAt (path.field "phase")
    (← requireField path json "phase")
  requireLiteralAt (path.field "severity")
    (← requireField path json "severity") "error"
  pure { code, phase, path := semanticPath, arguments }

def decodeCoreTypeAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Solcore.Core.Wire.V3.Ty :=
  let limits : Solcore.Core.Wire.V3.CoreBudgetLimits := {
    maxDepth := jsonDepth json + 1
    maxNodes := jsonNodes json + 1
  }
  match Solcore.Core.Wire.V3.decodeTypeAtWithBudget limits .initial 1 path json with
  | .ok (type, _) => pure type
  | .error (.protocol error) => throw (.core error)
  | .error (.exhausted _) =>
      invalidTagAt path json (.mkObj [("constraint", "finite-core-type")])

def decodeCoreCheckResultAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CoreCheckResult := do
  ensureExactObject path json ["schema", "value"] ["schema", "value"]
  let schemaPath := path.field "schema"
  let schema ← decodeStringAt schemaPath (← requireField path json "schema")
  unless schema == checkResultSchema do
    failAt schemaPath .invalidSchema (.mkObj [
      ("expected", checkResultSchema), ("actual", schema)
    ])
  let valuePath := path.field "value"
  let value ← requireField path json "value"
  ensureExactObject valuePath value ["resultType"] ["resultType"]
  let resultType ← decodeCoreTypeAt (valuePath.field "resultType")
    (← requireField valuePath value "resultType")
  pure { resultType }

private def requirePhase
    (path : Path)
    (actual expected : Phase) : DecodeResult Unit :=
  unless actual == expected do
    invalidTagAt path (encodePhase actual) (encodePhase expected)

private def preflightResource? : ResourceKind → Option PreflightResource
  | .jsonDepth => some .jsonDepth
  | .jsonNodes => some .jsonNodes
  | .coreDepth => some .coreDepth
  | .coreNodes => some .coreNodes
  | .scenarioEntries => some .scenarioEntries
  | .identifierBytes => some .identifierBytes
  | .calldataBytes => some .calldataBytes
  | .evaluationSteps => none

def decodeInconclusiveAt
    (allowEvaluationSteps : Bool)
    (path : Path)
    (json : Lean.Json) : DecodeResult Exhaustion := do
  let fields := ["consumed", "kind", "limit", "phase", "resource"]
  ensureExactObject path json fields fields
  let consumed ← decodeNatAt (path.field "consumed")
    (← requireField path json "consumed")
  requireLiteralAt (path.field "kind")
    (← requireField path json "kind") "inconclusive"
  let limit ← decodeNatAt (path.field "limit")
    (← requireField path json "limit")
  let phase ← decodePhaseAt (path.field "phase")
    (← requireField path json "phase")
  let resourcePath := path.field "resource"
  let resource ← decodeResourceKindAt resourcePath
    (← requireField path json "resource")
  match resource with
  | .evaluationSteps => do
      unless consumed == limit do
        invalidTagAt (path.field "consumed") consumed limit
      unless allowEvaluationSteps do
        invalidTagAt resourcePath (encodeResourceKind resource) <| .arr #[
          "jsonDepth", "jsonNodes", "coreDepth", "coreNodes",
          "scenarioEntries", "identifierBytes", "calldataBytes"
        ]
      requirePhase (path.field "phase") phase .contractExecution
      pure (.evaluationSteps limit)
  | _ => do
      let preflight ← match preflightResource? resource with
        | some value => pure value
        | none => invalidTagAt resourcePath (encodeResourceKind resource) .null
      let exhaustion ← match PreflightExhaustion.ofValues?
          preflight limit consumed with
        | some value => pure value
        | none => invalidTagAt (path.field "consumed") consumed <| .mkObj [
            ("constraint", "strictly-greater-than-limit"), ("limit", limit)
          ]
      requirePhase (path.field "phase") phase preflight.phase
      pure (.preflight exhaustion)

def decodeInternalErrorVerdictAt
    (path : Path)
    (json : Lean.Json) : DecodeResult InternalError := do
  ensureExactObject path json ["code", "kind", "phase"] ["code", "kind", "phase"]
  let codePath := path.field "code"
  let code ← decodeStringAt codePath (← requireField path json "code")
  requireLiteralAt (path.field "kind")
    (← requireField path json "kind") "internalError"
  let phasePath := path.field "phase"
  let phaseJson ← requireField path json "phase"
  match code with
  | "core-wire-projection-failed" => do
      requireLiteralAt phasePath phaseJson "observationEncoding"
      pure .coreWireProjectionFailed
  | "world-code-reference-invariant" => do
      requireLiteralAt phasePath phaseJson "observationEncoding"
      pure .worldCodeReferenceInvariant
  | "oracle-response-invariant" => do
      unless phaseJson == .null do invalidTagAt phasePath phaseJson .null
      pure .oracleResponseInvariant
  | _ => invalidTagAt codePath code <| .arr #[
      "core-wire-projection-failed", "world-code-reference-invariant",
      "oracle-response-invariant"
    ]

end Solcore.Oracle.V5.Wire
