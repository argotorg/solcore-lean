import Solcore.Oracle.V5.Wire.ResponseEncode
import Solcore.Oracle.V5.Wire.ScenarioDiagnosticDecode

/-! Focused strict-decoding tests for Oracle v5 scenario diagnostics. -/

set_option autoImplicit false

namespace Tests.OracleV5ScenarioDiagnosticDecode

open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire

private def address : String :=
  "0x0000000000000000000000000000000000000001"

private def word : String :=
  "0x0000000000000000000000000000000000000000000000000000000000000002"

private def unsupportedType : Diagnostic := {
  code := "oracle.v5.contract.unsupported-entry-result-type"
  phase := .contractAdmission
  path := ["contracts", "root", "program", "resultType"]
  arguments := .mkObj [("actual", "bool")]
}

private def duplicateSignature : Diagnostic := {
  code := "oracle.v5.abi.duplicate-signature"
  phase := .contractAdmission
  path := ["contracts", "root", "methods"]
  arguments := .mkObj [
    ("signature", "read(uint256)"),
    ("firstMethod", "read"), ("secondMethod", "read")]
}

private def dangling : Diagnostic := {
  code := "oracle.v5.reference.dangling-contract"
  phase := .worldValidation
  path := ["world", "accounts", address, "code"]
  arguments := .mkObj [("id", "not a valid id")]
}

private def duplicateProbe : Diagnostic := {
  code := "oracle.v5.probe.duplicate"
  phase := .probeValidation
  path := ["invocation", "probes", "2"]
  arguments := .mkObj [("firstIndex", 1), ("secondIndex", 2)]
}

private def rootCodeAbsent : Diagnostic := {
  code := "oracle.v5.root.target-code-absent"
  phase := .rootInstallation
  path := ["world", "accounts", address, "code"]
  arguments := .mkObj [("target", address)]
}

private def diagnostics : List Diagnostic := [
  {
    code := "oracle.v5.contract.invalid-id"
    phase := .contractAdmission
    path := ["contracts", "*", "id"]
    arguments := .mkObj [("actual", "*")]
  },
  unsupportedType,
  duplicateSignature,
  dangling,
  {
    code := "oracle.v5.world.duplicate-storage-slot"
    phase := .worldValidation
    path := ["world", "accounts", address, "storage", word]
    arguments := .mkObj [("address", address), ("slot", word)]
  },
  {
    code := "oracle.v5.environment.duplicate-creation-route"
    phase := .environmentValidation
    path := ["environment", "creationAddressPolicy", "routes", address, word]
    arguments := .mkObj [("creator", address), ("nonce", word)]
  },
  duplicateProbe,
  rootCodeAbsent
]

private def roundTrips : Bool :=
  diagnostics.all fun diagnostic =>
    match decodeExecuteRejectionAt .root (encodeDiagnostic diagnostic) with
    | .ok rejection => rejection.diagnostic == diagnostic
    | .error _ => false

private def replaceArgumentsField
    (json : Lean.Json)
    (name : String)
    (value : Lean.Json) : Lean.Json :=
  json.setObjVal! "arguments" <|
    (json.getObjValD "arguments").setObjVal! name value

private def embeddedCoreOwnershipAndPrecedence : Bool :=
  let bad := (replaceArgumentsField (encodeDiagnostic unsupportedType)
    "actual" false).setObjVal! "display" true
  match decodeExecuteRejectionAt .root bad with
  | .error (.core error) =>
      error.path.toPointer == "/arguments/actual" &&
        error.code == .invalidType
  | _ => false

private def naturalCanonicalization : Bool :=
  let decimalOne : Lean.Json := .num { mantissa := 10, exponent := 1 }
  let json := replaceArgumentsField (encodeDiagnostic duplicateProbe)
    "firstIndex" decimalOne
  match decodeExecuteRejectionAt .root json with
  | .ok rejection => rejection.diagnostic == duplicateProbe
  | .error _ => false

private def relationErrorsAreSpecific : Bool :=
  let wrongSecond := replaceArgumentsField (encodeDiagnostic duplicateSignature)
    "secondMethod" "write"
  let falseCollision : Diagnostic := {
    code := "oracle.v5.abi.selector-collision"
    phase := .contractAdmission
    path := ["contracts", "root", "methods"]
    arguments := .mkObj [
      ("selector", "00000000"),
      ("firstSignature", "f(uint256)"),
      ("secondSignature", "foo(uint256)")]
  }
  let duplicatePath := match decodeExecuteRejectionAt .root wrongSecond with
    | .error (.oracle path .invalidTag _) =>
        path.toPointer == "/arguments/secondMethod"
    | _ => false
  let selectorPath :=
    match decodeExecuteRejectionAt .root (encodeDiagnostic falseCollision) with
    | .error (.oracle path .invalidTag _) =>
        path.toPointer == "/arguments/selector"
    | _ => false
  duplicatePath && selectorPath

private def phasePathAndCodeClosed : Bool :=
  let badPhase := (encodeDiagnostic dangling).setObjVal! "phase" "rootInstallation"
  let badPath := (encodeDiagnostic dangling).setObjVal!
    "path" (.arr #["world", "future"])
  let future := (encodeDiagnostic dangling).setObjVal!
    "code" "oracle.v5.future"
  let phaseExact := match decodeExecuteRejectionAt .root badPhase with
    | .error (.oracle path .invalidTag _) => path.toPointer == "/phase"
    | _ => false
  let pathExact := match decodeExecuteRejectionAt .root badPath with
    | .error (.oracle path .invalidTag _) => path.toPointer == "/path"
    | _ => false
  let codeExact := match decodeExecuteRejectionAt .root future with
    | .error (.oracle path .invalidTag _) => path.toPointer == "/code"
    | _ => false
  phaseExact && pathExact && codeExact

private def argumentShapeExact : Bool :=
  let bad := replaceArgumentsField (encodeDiagnostic rootCodeAbsent)
    "future" true
  match decodeExecuteRejectionAt .root bad with
  | .error (.oracle path .unknownField _) =>
      path.toPointer == "/arguments/future"
  | _ => false

private def allChecks : Bool :=
  roundTrips && embeddedCoreOwnershipAndPrecedence && naturalCanonicalization &&
    relationErrorsAreSpecific && phasePathAndCodeClosed && argumentShapeExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ScenarioDiagnosticDecode : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 scenario diagnostic decoding changed")

end Tests.OracleV5ScenarioDiagnosticDecode
