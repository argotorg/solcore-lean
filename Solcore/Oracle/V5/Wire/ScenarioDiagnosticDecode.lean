import Solcore.Oracle.V5.Wire.ScenarioDiagnosticArguments

/-! Strict decoding and sealing for Oracle v5 execution rejections. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

private def fixedScenarioPhase? : String → Option Phase
  | "oracle.v5.contract.invalid-id"
  | "oracle.v5.contract.duplicate-id"
  | "oracle.v5.contract.unsupported-entry-result-type"
  | "oracle.v5.method.invalid-name"
  | "oracle.v5.method.nonempty-data-definitions"
  | "oracle.v5.method.result-type-mismatch"
  | "oracle.v5.abi.empty-method-table"
  | "oracle.v5.abi.duplicate-signature"
  | "oracle.v5.abi.selector-collision"
  | "oracle.v5.contract.duplicate-code" => some .contractAdmission
  | "oracle.v5.world.duplicate-account"
  | "oracle.v5.world.duplicate-storage-slot"
  | "oracle.v5.world.zero-storage-value" => some .worldValidation
  | "oracle.v5.environment.duplicate-call-address"
  | "oracle.v5.environment.duplicate-template-id"
  | "oracle.v5.environment.duplicate-creation-route" =>
      some .environmentValidation
  | "oracle.v5.probe.duplicate" => some .probeValidation
  | "oracle.v5.root.target-absent"
  | "oracle.v5.root.target-code-absent" => some .rootInstallation
  | _ => none

private def requireScenarioPhase
    (code : String)
    (path : Path)
    (phase : Phase) : DecodeResult Unit :=
  match fixedScenarioPhase? code with
  | some expected =>
      unless phase == expected do
        invalidTagAt path (encodePhase phase) (encodePhase expected)
  | none =>
      if code == "oracle.v5.reference.dangling-contract" then
        unless phase == .worldValidation || phase == .environmentValidation do
          invalidTagAt path (encodePhase phase) <| .arr #[
            "worldValidation", "environmentValidation"
          ]
      else
        invalidTagAt path code expectedScenarioDiagnosticCodes

private def scenarioPathValid
    (code : String)
    (semanticPath : List String)
    (arguments : Lean.Json) : Bool :=
  let validAt (phase : Phase) :=
    ({ code, phase, path := semanticPath, arguments } : Diagnostic).isValidExecute
  match fixedScenarioPhase? code with
  | some phase => validAt phase
  | none =>
      code == "oracle.v5.reference.dangling-contract" &&
        (validAt .worldValidation || validAt .environmentValidation)

private def decodeScenarioDiagnosticAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Diagnostic := do
  let fields := ["arguments", "code", "display", "path", "phase", "severity"]
  ensureExactObject path json fields fields
  let codePath := path.field "code"
  let codeJson ← requireField path json "code"
  let code? := match codeJson with | .str value => some value | _ => none
  let argumentsPath := path.field "arguments"
  let rawArguments ← requireField path json "arguments"
  let _ ← match rawArguments with
    | .obj _ => pure ()
    | _ => failAt argumentsPath .expectedObject (expectedArguments
        "object" rawArguments)
  let arguments ← match code? with
    | some code =>
        decodeScenarioArgumentsAt codePath argumentsPath code rawArguments
    | none => pure rawArguments
  let code ← decodeStringAt codePath codeJson
  let displayPath := path.field "display"
  let display ← requireField path json "display"
  unless display == .null do invalidTagAt displayPath display .null
  let semanticPathJson ← requireField path json "path"
  let semanticPath ← decodeArrayAt decodeStringAt
    (path.field "path") semanticPathJson
  unless scenarioPathValid code semanticPath arguments do
    invalidTagAt (path.field "path") semanticPathJson <|
      .mkObj [("constraint", "canonical-path-for-" ++ code)]
  let phasePath := path.field "phase"
  let phase ← decodePhaseAt phasePath (← requireField path json "phase")
  requireScenarioPhase code phasePath phase
  requireLiteralAt (path.field "severity")
    (← requireField path json "severity") "error"
  let diagnostic : Diagnostic := { code, phase, path := semanticPath, arguments }
  unless diagnostic.isValidExecute do
    invalidTagAt (path.field "path") semanticPathJson <|
      .mkObj [("constraint", "canonical-path-for-" ++ code)]
  pure diagnostic

private def decodeScenarioRejectionAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ExecuteRejection := do
  let diagnostic ← decodeScenarioDiagnosticAt path json
  match ExecuteRejection.of? diagnostic with
  | some rejection => pure rejection
  | none =>
      invalidTagAt (path.field "path")
        (Lean.Json.arr <| diagnostic.path.toArray.map Lean.Json.str)
        (.mkObj [("constraint", "closed-execute-diagnostic")])

/-- Decode either a contract-checker or scenario rejection and seal it. -/
def decodeExecuteRejectionAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ExecuteRejection := do
  let fields := ["arguments", "code", "display", "path", "phase", "severity"]
  ensureExactObject path json fields fields
  let codeJson ← requireField path json "code"
  match codeJson with
  | .str code =>
      if code.startsWith "core.check." then
        decodeContractCheckRejectionAt path json
      else
        decodeScenarioRejectionAt path json
  | _ => decodeScenarioRejectionAt path json

end Solcore.Oracle.V5.Wire
