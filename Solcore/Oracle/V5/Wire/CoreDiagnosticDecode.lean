import Solcore.Oracle.V5.Wire.ResponseShape

/-! Code-directed strict decoding for Core-check rejection diagnostics. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

private def coreCodes : Array String := #[
  "core.check.unbound-variable", "core.check.expected-bool",
  "core.check.expected-product", "core.check.expected-function",
  "core.check.function-argument-type-mismatch",
  "core.check.lambda-result-type-mismatch", "core.check.expected-sum",
  "core.check.case-branch-type-mismatch", "core.check.invalid-cell-payload",
  "core.check.cell-initializer-type-mismatch", "core.check.expected-cell",
  "core.check.cell-value-type-mismatch", "core.check.invalid-definition-payload",
  "core.check.unknown-named-data-type", "core.check.unknown-data-type",
  "core.check.unknown-constructor",
  "core.check.constructor-payload-type-mismatch",
  "core.check.expected-named-data", "core.check.match-data-type-mismatch",
  "core.check.match-branch-count-mismatch",
  "core.check.match-branch-result-type-mismatch", "core.check.invalid-result-type",
  "core.check.primitive-operand-type-mismatch", "core.check.branch-type-mismatch",
  "core.check.declared-result-type-mismatch", "core.check.inference-failure"
]

private def expectedCoreCodes : Lean.Json :=
  .arr <| coreCodes.map Lean.Json.str

private def exactArguments
    (path : Path)
    (json : Lean.Json)
    (fields : List String) : DecodeResult Unit :=
  ensureExactObject path json fields fields

private def decodeNatField
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult Nat := do
  decodeNatAt (path.field name) (← requireField path json name)

private def decodeTypeField
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult Solcore.Core.Wire.V3.Ty := do
  decodeCoreTypeAt (path.field name) (← requireField path json name)

private def oneTypeArguments
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult Lean.Json := do
  exactArguments path json [name]
  let value ← decodeTypeField path json name
  pure (.mkObj [(name, Solcore.Core.Wire.V3.encodeType value)])

private def twoTypeArguments
    (path : Path)
    (json : Lean.Json)
    (firstName secondName : String) : DecodeResult Lean.Json := do
  let fields := [firstName, secondName].mergeSort (fun left right =>
    (compare left right).isLE)
  exactArguments path json fields
  let first ← if (compare firstName secondName).isLE then
      decodeTypeField path json firstName
    else
      decodeTypeField path json secondName
  let second ← if (compare firstName secondName).isLE then
      decodeTypeField path json secondName
    else
      decodeTypeField path json firstName
  let (firstValue, secondValue) :=
    if (compare firstName secondName).isLE then (first, second) else (second, first)
  pure (.mkObj [
    (firstName, Solcore.Core.Wire.V3.encodeType firstValue),
    (secondName, Solcore.Core.Wire.V3.encodeType secondValue)
  ])

private def decodeCoreArgumentsAt
    (codePath argumentsPath : Path)
    (code : String)
    (json : Lean.Json) : DecodeResult Lean.Json :=
  match code with
  | "core.check.unbound-variable" => do
      exactArguments argumentsPath json ["contextSize", "index"]
      let contextSize ← decodeNatField argumentsPath json "contextSize"
      let index ← decodeNatField argumentsPath json "index"
      pure (.mkObj [("index", index), ("contextSize", contextSize)])
  | "core.check.expected-bool"
  | "core.check.expected-product"
  | "core.check.expected-function"
  | "core.check.expected-sum"
  | "core.check.invalid-cell-payload"
  | "core.check.expected-cell"
  | "core.check.expected-named-data"
  | "core.check.invalid-result-type" =>
      oneTypeArguments argumentsPath json "actual"
  | "core.check.function-argument-type-mismatch"
  | "core.check.cell-initializer-type-mismatch"
  | "core.check.cell-value-type-mismatch"
  | "core.check.constructor-payload-type-mismatch"
  | "core.check.primitive-operand-type-mismatch" =>
      twoTypeArguments argumentsPath json "expected" "actual"
  | "core.check.lambda-result-type-mismatch" =>
      twoTypeArguments argumentsPath json "declared" "actual"
  | "core.check.case-branch-type-mismatch" =>
      twoTypeArguments argumentsPath json "leftType" "rightType"
  | "core.check.invalid-definition-payload" => do
      exactArguments argumentsPath json
        ["actual", "constructorIndex", "dataTypeIndex"]
      let actual ← decodeTypeField argumentsPath json "actual"
      let constructorIndex ←
        decodeNatField argumentsPath json "constructorIndex"
      let dataTypeIndex ← decodeNatField argumentsPath json "dataTypeIndex"
      pure (.mkObj [
        ("dataTypeIndex", dataTypeIndex),
        ("constructorIndex", constructorIndex),
        ("actual", Solcore.Core.Wire.V3.encodeType actual)
      ])
  | "core.check.unknown-named-data-type"
  | "core.check.unknown-data-type" => do
      exactArguments argumentsPath json ["dataType"]
      let dataType ← decodeNatField argumentsPath json "dataType"
      pure (.mkObj [("dataType", dataType)])
  | "core.check.unknown-constructor" => do
      exactArguments argumentsPath json ["constructor"]
      let constructorJson ← requireField argumentsPath json "constructor"
      let constructor ← liftCoreProtocol <|
        Solcore.Core.Wire.V3.decodeConstructorIdAt
          (argumentsPath.field "constructor") constructorJson
      pure (.mkObj [("constructor",
        Solcore.Core.Wire.V3.encodeConstructorId constructor)])
  | "core.check.match-data-type-mismatch"
  | "core.check.match-branch-count-mismatch" => do
      exactArguments argumentsPath json ["actual", "expected"]
      let actual ← decodeNatField argumentsPath json "actual"
      let expected ← decodeNatField argumentsPath json "expected"
      pure (.mkObj [("expected", expected), ("actual", actual)])
  | "core.check.match-branch-result-type-mismatch" => do
      exactArguments argumentsPath json ["actual", "branchIndex", "expected"]
      let actual ← decodeTypeField argumentsPath json "actual"
      let branchIndex ← decodeNatField argumentsPath json "branchIndex"
      let expected ← decodeTypeField argumentsPath json "expected"
      pure (.mkObj [
        ("branchIndex", branchIndex),
        ("expected", Solcore.Core.Wire.V3.encodeType expected),
        ("actual", Solcore.Core.Wire.V3.encodeType actual)
      ])
  | "core.check.branch-type-mismatch" =>
      twoTypeArguments argumentsPath json "thenType" "elseType"
  | "core.check.declared-result-type-mismatch" =>
      twoTypeArguments argumentsPath json "declaredType" "inferredType"
  | "core.check.inference-failure" => do
      exactArguments argumentsPath json []
      pure (.mkObj [])
  | _ => invalidTagAt codePath code expectedCoreCodes

private inductive CoreDiagnosticSite where
  | query
  | contract

private def expectedPhase : CoreDiagnosticSite → Phase
  | .query => .coreChecking
  | .contract => .contractAdmission

private def validPath
    (site : CoreDiagnosticSite)
    (path : List String) : Bool :=
  match site with
  | .query => Diagnostic.Catalog.validCoreCheckPath path
  | .contract => Diagnostic.Catalog.validContractCheckPath path

private def expectedPathConstraint : CoreDiagnosticSite → String
  | .query => "core-check-program-path"
  | .contract => "contract-program-or-method-path"

private def decodeCoreDiagnosticAt
    (site : CoreDiagnosticSite)
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
    | some code => decodeCoreArgumentsAt codePath argumentsPath code rawArguments
    | none => pure rawArguments
  let code ← decodeStringAt codePath codeJson
  let displayPath := path.field "display"
  let display ← requireField path json "display"
  unless display == .null do invalidTagAt displayPath display .null
  let semanticPathJson ← requireField path json "path"
  let semanticPath ← decodeArrayAt decodeStringAt
    (path.field "path") semanticPathJson
  unless validPath site semanticPath do
    invalidTagAt (path.field "path") semanticPathJson <|
      .mkObj [("constraint", expectedPathConstraint site)]
  let phasePath := path.field "phase"
  let phase ← decodePhaseAt phasePath (← requireField path json "phase")
  unless phase == expectedPhase site do
    invalidTagAt phasePath (encodePhase phase) (encodePhase <| expectedPhase site)
  requireLiteralAt (path.field "severity")
    (← requireField path json "severity") "error"
  pure { code, phase, path := semanticPath, arguments }

def decodeCoreCheckRejectionAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CoreCheckRejection := do
  let diagnostic ← decodeCoreDiagnosticAt .query path json
  match CoreCheckRejection.of? diagnostic with
  | some rejection => pure rejection
  | none => invalidTagAt (path.field "code") diagnostic.code expectedCoreCodes

def decodeContractCheckRejectionAt
    (path : Path)
    (json : Lean.Json) : DecodeResult ExecuteRejection := do
  let diagnostic ← decodeCoreDiagnosticAt .contract path json
  match ExecuteRejection.of? diagnostic with
  | some rejection => pure rejection
  | none => invalidTagAt (path.field "code") diagnostic.code expectedCoreCodes

end Solcore.Oracle.V5.Wire
