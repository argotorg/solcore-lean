import Solcore.Oracle.V5.Wire.CoreDiagnosticDecode
import Solcore.Oracle.V5.Wire.Scalar

/-! Strict code-directed arguments for non-Core Oracle v5 rejections. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

def scenarioDiagnosticCodes : Array String := #[
  "oracle.v5.contract.invalid-id", "oracle.v5.contract.duplicate-id",
  "oracle.v5.contract.unsupported-entry-result-type",
  "oracle.v5.method.invalid-name", "oracle.v5.method.nonempty-data-definitions",
  "oracle.v5.method.result-type-mismatch", "oracle.v5.abi.empty-method-table",
  "oracle.v5.abi.duplicate-signature", "oracle.v5.abi.selector-collision",
  "oracle.v5.contract.duplicate-code", "oracle.v5.reference.dangling-contract",
  "oracle.v5.world.duplicate-account", "oracle.v5.world.duplicate-storage-slot",
  "oracle.v5.world.zero-storage-value",
  "oracle.v5.environment.duplicate-call-address",
  "oracle.v5.environment.duplicate-template-id",
  "oracle.v5.environment.duplicate-creation-route", "oracle.v5.probe.duplicate",
  "oracle.v5.root.target-absent", "oracle.v5.root.target-code-absent"
]

def expectedScenarioDiagnosticCodes : Lean.Json :=
  .arr <| scenarioDiagnosticCodes.map Lean.Json.str

private def exactArguments
    (path : Path)
    (json : Lean.Json)
    (fields : List String) : DecodeResult Unit :=
  ensureExactObject path json fields fields

private def decodeStringField
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult String := do
  decodeStringAt (path.field name) (← requireField path json name)

private def decodeNatField
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult Nat := do
  decodeNatAt (path.field name) (← requireField path json name)

private def decodeContractIdField
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult String := do
  let fieldPath := path.field name
  let value ← decodeStringField path json name
  unless contractIdValid value do
    invalidTagAt fieldPath value <|
      .mkObj [("constraint", "contract-id")]
  pure value

private def decodeMethodNameField
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult String := do
  let fieldPath := path.field name
  let value ← decodeStringField path json name
  unless Solcore.Abi.V1.isValidMethodName value do
    invalidTagAt fieldPath value <|
      .mkObj [("constraint", "method-name")]
  pure value

private def canonicalMethodSignature (signature : String) : Bool :=
  let suffix := "(uint256)".toList
  let characters := signature.toList
  characters.length > suffix.length &&
    characters.drop (characters.length - suffix.length) == suffix &&
    Solcore.Abi.V1.isValidMethodName
      (String.ofList <| characters.take (characters.length - suffix.length))

private def decodeCoreTypeField
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult Solcore.Core.Wire.V3.Ty := do
  decodeCoreTypeAt (path.field name) (← requireField path json name)

private def decodeAddressField
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult Solcore.Semantics.Address := do
  decodeAddressAt (path.field name) (← requireField path json name)

private def decodeWordField
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult Solcore.Core.Word := do
  decodeWordAt (path.field name) (← requireField path json name)

private def decodeOneCoreType
    (path : Path)
    (json : Lean.Json) :
    DecodeResult (Solcore.Core.Wire.V3.Ty × Lean.Json) := do
  exactArguments path json ["actual"]
  let actual ← decodeCoreTypeField path json "actual"
  pure (actual,
    .mkObj [("actual", Solcore.Core.Wire.V3.encodeType actual)])

private def oneAddress
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult Lean.Json := do
  exactArguments path json [name]
  let value ← decodeAddressField path json name
  pure (.mkObj [(name, encodeAddress value)])

private def oneWord
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult Lean.Json := do
  exactArguments path json [name]
  let value ← decodeWordField path json name
  pure (.mkObj [(name, encodeWord value)])

def decodeScenarioArgumentsAt
    (codePath argumentsPath : Path)
    (code : String)
    (json : Lean.Json) : DecodeResult Lean.Json :=
  match code with
  | "oracle.v5.contract.invalid-id" => do
      exactArguments argumentsPath json ["actual"]
      let actual ← decodeStringField argumentsPath json "actual"
      if contractIdValid actual then
        invalidTagAt (argumentsPath.field "actual") actual <|
          .mkObj [("constraint", "invalid-contract-id")]
      pure (.mkObj [("actual", actual)])
  | "oracle.v5.contract.duplicate-id" => do
      exactArguments argumentsPath json ["id"]
      let id ← decodeContractIdField argumentsPath json "id"
      pure (.mkObj [("id", id)])
  | "oracle.v5.contract.unsupported-entry-result-type" => do
      let (actual, canonical) ← decodeOneCoreType argumentsPath json
      if Diagnostic.entryResultTypeSupported actual then
        invalidTagAt (argumentsPath.field "actual")
          (Solcore.Core.Wire.V3.encodeType actual) <|
          .mkObj [("constraint", "unsupported-contract-entry-result-type")]
      pure canonical
  | "oracle.v5.method.result-type-mismatch" => do
      let (actual, canonical) ← decodeOneCoreType argumentsPath json
      if Diagnostic.staticWordMethodResultTypeSupported actual then
        invalidTagAt (argumentsPath.field "actual")
          (Solcore.Core.Wire.V3.encodeType actual) <|
          .mkObj [("constraint", "not-static-word-method-result-type")]
      pure canonical
  | "oracle.v5.method.invalid-name" => do
      exactArguments argumentsPath json ["actual"]
      let actual ← decodeStringField argumentsPath json "actual"
      if Solcore.Abi.V1.isValidMethodName actual then
        invalidTagAt (argumentsPath.field "actual") actual <|
          .mkObj [("constraint", "invalid-method-name")]
      pure (.mkObj [("actual", actual)])
  | "oracle.v5.method.nonempty-data-definitions" => do
      exactArguments argumentsPath json ["count"]
      let count ← decodeNatField argumentsPath json "count"
      unless 0 < count do
        invalidTagAt (argumentsPath.field "count") count <|
          .mkObj [("constraint", "positive")]
      pure (.mkObj [("count", count)])
  | "oracle.v5.abi.empty-method-table" => do
      exactArguments argumentsPath json []
      pure (.mkObj [])
  | "oracle.v5.abi.duplicate-signature" => do
      exactArguments argumentsPath json
        ["firstMethod", "secondMethod", "signature"]
      let first ← decodeMethodNameField argumentsPath json "firstMethod"
      let second ← decodeMethodNameField argumentsPath json "secondMethod"
      unless second == first do
        invalidTagAt (argumentsPath.field "secondMethod") second first
      let signature ← decodeStringField argumentsPath json "signature"
      unless signature == first ++ "(uint256)" do
        invalidTagAt (argumentsPath.field "signature") signature <|
          first ++ "(uint256)"
      pure (.mkObj [
        ("signature", signature), ("firstMethod", first),
        ("secondMethod", second)
      ])
  | "oracle.v5.abi.selector-collision" => do
      exactArguments argumentsPath json
        ["firstSignature", "secondSignature", "selector"]
      let first ← decodeStringField argumentsPath json "firstSignature"
      unless canonicalMethodSignature first do
        invalidTagAt (argumentsPath.field "firstSignature") first <|
          .mkObj [("constraint", "method(uint256)")]
      let second ← decodeStringField argumentsPath json "secondSignature"
      unless canonicalMethodSignature second &&
          (compare first second).isLT do
        invalidTagAt (argumentsPath.field "secondSignature") second <|
          .mkObj [("constraint", "canonical-signature-after-firstSignature")]
      let selector ← decodeStringField argumentsPath json "selector"
      let firstSelector := Diagnostic.selectorTextForSignature first
      unless selector == firstSelector &&
          selector == Diagnostic.selectorTextForSignature second do
        invalidTagAt (argumentsPath.field "selector") selector firstSelector
      pure (.mkObj [
        ("selector", selector), ("firstSignature", first),
        ("secondSignature", second)
      ])
  | "oracle.v5.contract.duplicate-code" => do
      exactArguments argumentsPath json ["firstId", "secondId"]
      let first ← decodeContractIdField argumentsPath json "firstId"
      let second ← decodeContractIdField argumentsPath json "secondId"
      unless (compare first second).isLT do
        invalidTagAt (argumentsPath.field "secondId") second <|
          .mkObj [("constraint", "canonical-contract-id-after-firstId")]
      pure (.mkObj [("firstId", first), ("secondId", second)])
  | "oracle.v5.reference.dangling-contract" => do
      exactArguments argumentsPath json ["id"]
      let id ← decodeStringField argumentsPath json "id"
      pure (.mkObj [("id", id)])
  | "oracle.v5.world.duplicate-account"
  | "oracle.v5.environment.duplicate-call-address" =>
      oneAddress argumentsPath json "address"
  | "oracle.v5.world.duplicate-storage-slot"
  | "oracle.v5.world.zero-storage-value" => do
      exactArguments argumentsPath json ["address", "slot"]
      let address ← decodeAddressField argumentsPath json "address"
      let slot ← decodeWordField argumentsPath json "slot"
      pure (.mkObj [("address", encodeAddress address), ("slot", encodeWord slot)])
  | "oracle.v5.environment.duplicate-template-id" =>
      oneWord argumentsPath json "templateId"
  | "oracle.v5.environment.duplicate-creation-route" => do
      exactArguments argumentsPath json ["creator", "nonce"]
      let creator ← decodeAddressField argumentsPath json "creator"
      let nonce ← decodeWordField argumentsPath json "nonce"
      pure (.mkObj [("creator", encodeAddress creator), ("nonce", encodeWord nonce)])
  | "oracle.v5.probe.duplicate" => do
      exactArguments argumentsPath json ["firstIndex", "secondIndex"]
      let first ← decodeNatField argumentsPath json "firstIndex"
      let second ← decodeNatField argumentsPath json "secondIndex"
      unless first < second do
        invalidTagAt (argumentsPath.field "secondIndex") second <|
          .mkObj [("constraint", "strictly-greater-than-firstIndex")]
      pure (.mkObj [("firstIndex", first), ("secondIndex", second)])
  | "oracle.v5.root.target-absent"
  | "oracle.v5.root.target-code-absent" =>
      oneAddress argumentsPath json "target"
  | _ => invalidTagAt codePath code expectedScenarioDiagnosticCodes

end Solcore.Oracle.V5.Wire
