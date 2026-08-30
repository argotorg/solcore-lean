import Solcore.Oracle.V5.Wire.CoreDiagnosticDecode
import Solcore.Oracle.V5.Wire.ResponseEncode

/-! Focused strict-decoding tests for Oracle v5 Core diagnostics. -/

set_option autoImplicit false

namespace Tests.OracleV5CoreDiagnosticDecode

open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire

private def expectedBool : Diagnostic := {
  code := "core.check.expected-bool"
  phase := .coreChecking
  path := ["program", "ifCondition"]
  arguments := .mkObj [("actual", "word")]
}

private def unbound : Diagnostic := {
  code := "core.check.unbound-variable"
  phase := .coreChecking
  path := ["program"]
  arguments := .mkObj [("index", 1), ("contextSize", 0)]
}

private def contractCheck : Diagnostic := {
  code := "core.check.inference-failure"
  phase := .contractAdmission
  path := ["contracts", "root", "methods", "read", "implementation"]
  arguments := .mkObj []
}

private def unknownConstructor : Diagnostic := {
  code := "core.check.unknown-constructor"
  phase := .coreChecking
  path := ["program", "constructPayload"]
  arguments := .mkObj [
    ("constructor", .mkObj [("owner", 0), ("index", 1)])
  ]
}

private def replaceArgumentsField
    (json : Lean.Json)
    (name : String)
    (value : Lean.Json) : Lean.Json :=
  json.setObjVal! "arguments" <|
    (json.getObjValD "arguments").setObjVal! name value

private def roundTrips : Bool :=
  let core := match decodeCoreCheckRejectionAt .root
      (encodeDiagnostic expectedBool) with
    | .ok rejection => rejection.diagnostic == expectedBool
    | .error _ => false
  let contract := match decodeContractCheckRejectionAt .root
      (encodeDiagnostic contractCheck) with
    | .ok rejection => rejection.diagnostic == contractCheck
    | .error _ => false
  core && contract

private def embeddedCoreOwnership : Bool :=
  let badType := (replaceArgumentsField (encodeDiagnostic expectedBool)
    "actual" false).setObjVal! "display" true
  let badConstructor := replaceArgumentsField
    (encodeDiagnostic unknownConstructor) "constructor"
    (.mkObj [("index", 1)])
  let typeOwned := match decodeCoreCheckRejectionAt .root badType with
    | .error (.core error) =>
        error.path.toPointer == "/arguments/actual" &&
          error.code == .invalidType
    | _ => false
  let constructorOwned :=
    match decodeCoreCheckRejectionAt .root badConstructor with
    | .error (.core error) =>
        error.path.toPointer == "/arguments/constructor/owner" &&
          error.code == .missingField
    | _ => false
  typeOwned && constructorOwned

private def naturalCanonicalization : Bool :=
  let decimalOne : Lean.Json := .num { mantissa := 10, exponent := 1 }
  let json := replaceArgumentsField (encodeDiagnostic unbound)
    "index" decimalOne
  match decodeCoreCheckRejectionAt .root json with
  | .ok rejection =>
      rejection.diagnostic.arguments.getObjValD "index" == (1 : Lean.Json) &&
        encodeDiagnostic rejection.diagnostic == encodeDiagnostic unbound
  | .error _ => false

private def closedCatalogAndPath : Bool :=
  let future := (encodeDiagnostic expectedBool).setObjVal!
    "code" "core.check.future"
  let badPath := (encodeDiagnostic expectedBool).setObjVal!
    "path" (.arr #["future"])
  let badMethod := (encodeDiagnostic contractCheck).setObjVal!
    "path" (.arr #[
      "contracts", "root", "methods", "not valid", "implementation"])
  let futureRejected := match decodeCoreCheckRejectionAt .root future with
    | .error (.oracle path .invalidTag _) => path.toPointer == "/code"
    | _ => false
  let pathRejected := match decodeCoreCheckRejectionAt .root badPath with
    | .error (.oracle path .invalidTag _) => path.toPointer == "/path"
    | _ => false
  let methodRejected := match decodeContractCheckRejectionAt .root badMethod with
    | .error (.oracle path .invalidTag _) => path.toPointer == "/path"
    | _ => false
  futureRejected && pathRejected && methodRejected

private def argumentFieldSetExact : Bool :=
  let bad := replaceArgumentsField (encodeDiagnostic expectedBool)
    "future" true
  match decodeCoreCheckRejectionAt .root bad with
  | .error (.oracle path .unknownField _) =>
      path.toPointer == "/arguments/future"
  | _ => false

private def allChecks : Bool :=
  roundTrips && embeddedCoreOwnership && naturalCanonicalization &&
    closedCatalogAndPath && argumentFieldSetExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5CoreDiagnosticDecode : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 Core diagnostic decoding changed")

end Tests.OracleV5CoreDiagnosticDecode
