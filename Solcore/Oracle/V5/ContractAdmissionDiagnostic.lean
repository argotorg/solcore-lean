import Solcore.Oracle.V5.CheckDiagnostic
import Solcore.Oracle.V5.ContractAdmission
import Solcore.Semantics.RuntimeScalars.TextProperties

/-! Canonical Oracle v5 diagnostics for contract-package admission. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.ContractAdmissionDiagnostic

open Solcore.Core.Wire

private def diagnostic
    (code : String)
    (path : List String)
    (arguments : Lean.Json) : Diagnostic := {
  code
  phase := .contractAdmission
  path
  arguments
}

private def encodeCoreType
    (type : Solcore.Core.Ty) : Except InternalError Lean.Json :=
  match V3.Ty.ofCore? type with
  | some wire => .ok (V3.encodeType wire)
  | none => .error .coreWireProjectionFailed

private def selectorText (selector : Solcore.Abi.V1.Selector) : String :=
  ((Solcore.Semantics.encodeBytesText selector.encode).drop 2).toString

private def programPrefix : ContractProgramSite → List String
  | .checkedCore contract => ["contracts", contract.value, "program"]
  | .staticMethod contract methodName =>
      ["contracts", contract.value, "methods", methodName, "implementation"]

/-- Project every closed admission failure into its exact diagnostic shape. -/
def ofError :
    ContractAdmissionError → Except InternalError Diagnostic
  | .invalidContractId actual => .ok <| diagnostic
      "oracle.v5.contract.invalid-id"
      ["contracts", actual, "id"]
      (.mkObj [("actual", actual)])
  | .duplicateContractId id => .ok <| diagnostic
      "oracle.v5.contract.duplicate-id"
      ["contracts", id.value, "id"]
      (.mkObj [("id", id.value)])
  | .coreCheckFailed site error =>
      CheckDiagnostic.ofError .contractAdmission (programPrefix site) error
  | .unsupportedEntryResultType contract actual => do
      .ok <| diagnostic
        "oracle.v5.contract.unsupported-entry-result-type"
        ["contracts", contract.value, "program", "resultType"]
        (.mkObj [("actual", ← encodeCoreType actual)])
  | .invalidMethodName contract actual => .ok <| diagnostic
      "oracle.v5.method.invalid-name"
      ["contracts", contract.value, "methods", actual, "name"]
      (.mkObj [("actual", actual)])
  | .methodDataDefinitionsNonempty contract methodName count => .ok <|
      diagnostic
        "oracle.v5.method.nonempty-data-definitions"
        ["contracts", contract.value, "methods", methodName,
          "implementation", "dataDefinitions"]
        (.mkObj [("count", Lean.toJson count)])
  | .methodResultTypeMismatch contract methodName actual => do
      .ok <| diagnostic
        "oracle.v5.method.result-type-mismatch"
        ["contracts", contract.value, "methods", methodName,
          "implementation", "resultType"]
        (.mkObj [("actual", ← encodeCoreType actual)])
  | .emptyMethodTable contract => .ok <| diagnostic
      "oracle.v5.abi.empty-method-table"
      ["contracts", contract.value, "methods"]
      (.mkObj [])
  | .duplicateSignature contract firstMethod secondMethod signature =>
      .ok <| diagnostic
        "oracle.v5.abi.duplicate-signature"
        ["contracts", contract.value, "methods"]
        (.mkObj [
          ("signature", signature),
          ("firstMethod", firstMethod),
          ("secondMethod", secondMethod)
        ])
  | .selectorCollision contract firstSignature secondSignature selector =>
      .ok <| diagnostic
        "oracle.v5.abi.selector-collision"
        ["contracts", contract.value, "methods"]
        (.mkObj [
          ("selector", selectorText selector),
          ("firstSignature", firstSignature),
          ("secondSignature", secondSignature)
        ])
  | .duplicateCode firstId secondId => .ok <| diagnostic
      "oracle.v5.contract.duplicate-code"
      ["contracts", secondId.value]
      (.mkObj [
        ("firstId", firstId.value),
        ("secondId", secondId.value)
      ])

end Solcore.Oracle.V5.ContractAdmissionDiagnostic
