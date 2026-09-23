import Solcore.Oracle.V5.Wire.ResponseEncode
import Solcore.Oracle.V5.Wire.ScenarioDiagnostic

/-! Focused strict-decoding tests for Oracle v5 scenario diagnostics. -/

set_option autoImplicit false

namespace Tests.OracleV5ScenarioDiagnosticDecode

open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire

private def address : String :=
  "0x0000000000000000000000000000000000000001"

private def word : String :=
  "0x0000000000000000000000000000000000000000000000000000000000000002"

private def encodeCoreType
    (type : Solcore.Core.Wire.V3.Ty) : Lean.Json :=
  Solcore.Core.Wire.V3.encodeType type

private def unsupportedType : Diagnostic := {
  code := "oracle.v5.contract.unsupported-entry-result-type"
  phase := .contractAdmission
  path := ["contracts", "root", "program", "resultType"]
  arguments := .mkObj [("actual", "bool")]
}

private def methodResultMismatch : Diagnostic := {
  code := "oracle.v5.method.result-type-mismatch"
  phase := .contractAdmission
  path := ["contracts", "root", "methods", "read", "implementation",
    "resultType"]
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

private def selectorCollision : Diagnostic := {
  code := "oracle.v5.abi.selector-collision"
  phase := .contractAdmission
  path := ["contracts", "root", "methods"]
  arguments := .mkObj [
    ("selector", "77dbd42e"),
    ("firstSignature", "f116643(uint256)"),
    ("secondSignature", "f38491(uint256)")]
}

private def duplicateCode : Diagnostic := {
  code := "oracle.v5.contract.duplicate-code"
  phase := .contractAdmission
  path := ["contracts", "second"]
  arguments := .mkObj [("firstId", "first"), ("secondId", "second")]
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

/-- One valid witness for every published non-Core execution diagnostic code. -/
private def diagnostics : List Diagnostic := [
  {
    code := "oracle.v5.contract.invalid-id"
    phase := .contractAdmission
    path := ["contracts", "*", "id"]
    arguments := .mkObj [("actual", "*")]
  },
  {
    code := "oracle.v5.contract.duplicate-id"
    phase := .contractAdmission
    path := ["contracts", "root", "id"]
    arguments := .mkObj [("id", "root")]
  },
  unsupportedType,
  {
    code := "oracle.v5.method.invalid-name"
    phase := .contractAdmission
    path := ["contracts", "root", "methods", "*", "name"]
    arguments := .mkObj [("actual", "*")]
  },
  {
    code := "oracle.v5.method.nonempty-data-definitions"
    phase := .contractAdmission
    path := ["contracts", "root", "methods", "read", "implementation",
      "dataDefinitions"]
    arguments := .mkObj [("count", 1)]
  },
  methodResultMismatch,
  {
    code := "oracle.v5.abi.empty-method-table"
    phase := .contractAdmission
    path := ["contracts", "root", "methods"]
    arguments := .mkObj []
  },
  duplicateSignature,
  selectorCollision,
  duplicateCode,
  dangling,
  {
    code := "oracle.v5.world.duplicate-account"
    phase := .worldValidation
    path := ["world", "accounts", address]
    arguments := .mkObj [("address", address)]
  },
  {
    code := "oracle.v5.world.duplicate-storage-slot"
    phase := .worldValidation
    path := ["world", "accounts", address, "storage", word]
    arguments := .mkObj [("address", address), ("slot", word)]
  },
  {
    code := "oracle.v5.world.zero-storage-value"
    phase := .worldValidation
    path := ["world", "accounts", address, "storage", word, "value"]
    arguments := .mkObj [("address", address), ("slot", word)]
  },
  {
    code := "oracle.v5.environment.duplicate-call-address"
    phase := .environmentValidation
    path := ["environment", "callRegistry", address]
    arguments := .mkObj [("address", address)]
  },
  {
    code := "oracle.v5.environment.duplicate-template-id"
    phase := .environmentValidation
    path := ["environment", "creationTemplates", word]
    arguments := .mkObj [("templateId", word)]
  },
  {
    code := "oracle.v5.environment.duplicate-creation-route"
    phase := .environmentValidation
    path := ["environment", "creationAddressPolicy", "routes", address, word]
    arguments := .mkObj [("creator", address), ("nonce", word)]
  },
  duplicateProbe,
  {
    code := "oracle.v5.root.target-absent"
    phase := .rootInstallation
    path := ["world", "accounts", address]
    arguments := .mkObj [("target", address)]
  },
  rootCodeAbsent
]

private def danglingVariants : List Diagnostic := [
  {
    code := "oracle.v5.reference.dangling-contract"
    phase := .environmentValidation
    path := ["environment", "callRegistry", address, "contract"]
    arguments := .mkObj [("id", "missing")]
  },
  {
    code := "oracle.v5.reference.dangling-contract"
    phase := .environmentValidation
    path := ["environment", "creationTemplates", word, "initializer"]
    arguments := .mkObj [("id", "missing")]
  },
  {
    code := "oracle.v5.reference.dangling-contract"
    phase := .environmentValidation
    path := ["environment", "creationTemplates", word, "runtime"]
    arguments := .mkObj [("id", "missing")]
  }
]

private def coversEveryScenarioCode : Bool :=
  diagnostics.toArray.map (fun diagnostic => diagnostic.code) ==
    scenarioDiagnosticCodes

private def roundTrip (diagnostic : Diagnostic) : Bool :=
  match decodeExecuteRejectionAt .root (encodeDiagnostic diagnostic) with
  | .ok rejection => rejection.diagnostic == diagnostic
  | .error _ => false

private def roundTrips : Bool :=
  (diagnostics ++ danglingVariants).all roundTrip

private def contractCoreCheck : Diagnostic := {
  code := "core.check.inference-failure"
  phase := .contractAdmission
  path := ["contracts", "root", "program"]
  arguments := .mkObj []
}

private def coreCheckRouting : Bool :=
  match decodeExecuteRejectionAt .root (encodeDiagnostic contractCoreCheck) with
  | .ok rejection => rejection.diagnostic == contractCoreCheck
  | .error _ => false

private def replaceArgumentsField
    (json : Lean.Json)
    (name : String)
    (value : Lean.Json) : Lean.Json :=
  json.setObjVal! "arguments" <|
    (json.getObjValD "arguments").setObjVal! name value

private def oracleErrorAt (pointer : String) :
    Except Solcore.Oracle.V5.Wire.ProtocolError ExecuteRejection → Bool
  | .error (.oracle path .invalidTag _) => path.toPointer == pointer
  | _ => false

private def embeddedCoreOwnershipAndPrecedence : Bool :=
  let bad := (replaceArgumentsField (encodeDiagnostic unsupportedType)
    "actual" false).setObjVal! "display" true
  match decodeExecuteRejectionAt .root bad with
  | .error (.core error) =>
      error.path.toPointer == "/arguments/actual" &&
        error.code == .invalidType
  | _ => false

private def supportedTypeClaimsRejected : Bool :=
  let returnWord := { unsupportedType with
    arguments := .mkObj [("actual", encodeCoreType .word)] }
  let wordOutcome := { unsupportedType with
    arguments := .mkObj [("actual",
      encodeCoreType (.sum .word (.sum .word .word)))] }
  let staticWordMethod := { methodResultMismatch with
    arguments := .mkObj [("actual",
      encodeCoreType (.function .word .word))] }
  !returnWord.isValidExecute && !wordOutcome.isValidExecute &&
    !staticWordMethod.isValidExecute &&
    oracleErrorAt "/arguments/actual"
      (decodeExecuteRejectionAt .root <| encodeDiagnostic returnWord) &&
    oracleErrorAt "/arguments/actual"
      (decodeExecuteRejectionAt .root <| encodeDiagnostic wordOutcome) &&
    oracleErrorAt "/arguments/actual"
      (decodeExecuteRejectionAt .root <| encodeDiagnostic staticWordMethod)

private def canonicalPairOrder : Bool :=
  let reversedCollision : Diagnostic := { selectorCollision with
    arguments := .mkObj [
      ("selector", "77dbd42e"),
      ("firstSignature", "f38491(uint256)"),
      ("secondSignature", "f116643(uint256)")] }
  let reversedCode : Diagnostic := { duplicateCode with
    path := ["contracts", "first"]
    arguments := .mkObj [("firstId", "second"), ("secondId", "first")] }
  (compare "f116643(uint256)" "f38491(uint256)").isLT &&
    (compare "first" "second").isLT &&
    roundTrip selectorCollision && roundTrip duplicateCode &&
    !reversedCollision.isValidExecute && !reversedCode.isValidExecute &&
    oracleErrorAt "/arguments/secondSignature"
      (decodeExecuteRejectionAt .root <| encodeDiagnostic reversedCollision) &&
    oracleErrorAt "/arguments/secondId"
      (decodeExecuteRejectionAt .root <| encodeDiagnostic reversedCode)

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
  oracleErrorAt "/arguments/secondMethod"
      (decodeExecuteRejectionAt .root wrongSecond) &&
    oracleErrorAt "/arguments/selector"
      (decodeExecuteRejectionAt .root <| encodeDiagnostic falseCollision)

private def phasePathAndCodeClosed : Bool :=
  let badPhase := (encodeDiagnostic dangling).setObjVal!
    "phase" "rootInstallation"
  let badPath := (encodeDiagnostic dangling).setObjVal!
    "path" (.arr #["world", "future"])
  let future := (encodeDiagnostic dangling).setObjVal!
    "code" "oracle.v5.future"
  oracleErrorAt "/phase" (decodeExecuteRejectionAt .root badPhase) &&
    oracleErrorAt "/path" (decodeExecuteRejectionAt .root badPath) &&
    oracleErrorAt "/code" (decodeExecuteRejectionAt .root future)

private def canonicalPathPrecedesPhaseAndSeverity : Bool :=
  let badPath := (encodeDiagnostic dangling).setObjVal!
    "path" (.arr #["world", "future"])
  let badPhase := badPath.setObjVal! "phase" "rootInstallation"
  let bad := badPhase.setObjVal! "severity" "warning"
  oracleErrorAt "/path" (decodeExecuteRejectionAt .root bad)

private def argumentShapeExact : Bool :=
  let bad := replaceArgumentsField (encodeDiagnostic rootCodeAbsent)
    "future" true
  match decodeExecuteRejectionAt .root bad with
  | .error (.oracle path .unknownField _) =>
      path.toPointer == "/arguments/future"
  | _ => false

private def allChecks : Bool :=
  coversEveryScenarioCode && roundTrips && coreCheckRouting &&
    embeddedCoreOwnershipAndPrecedence && supportedTypeClaimsRejected &&
    canonicalPairOrder && naturalCanonicalization &&
    relationErrorsAreSpecific && phasePathAndCodeClosed &&
    canonicalPathPrecedesPhaseAndSeverity && argumentShapeExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ScenarioDiagnosticDecode : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 scenario diagnostic decoding changed")

end Tests.OracleV5ScenarioDiagnosticDecode
