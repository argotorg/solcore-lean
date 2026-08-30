import Solcore.Oracle.V5.DiagnosticExecutionValidity

/-! Semantic regressions for the sealed Oracle v5 diagnostic catalog. -/

set_option autoImplicit false

namespace Tests.OracleV5DiagnosticValidity

open Solcore.Oracle.V5

private def duplicateSignature : Diagnostic := {
  code := "oracle.v5.abi.duplicate-signature"
  phase := .contractAdmission
  path := ["contracts", "root", "methods"]
  arguments := .mkObj [
    ("signature", "read(uint256)"),
    ("firstMethod", "read"),
    ("secondMethod", "read")
  ]
}

private def danglingRawId : Diagnostic := {
  code := "oracle.v5.reference.dangling-contract"
  phase := .worldValidation
  path := ["world", "accounts",
    "0x0000000000000000000000000000000000000001", "code"]
  arguments := .mkObj [("id", "not a valid contract id")]
}

private def staticChecker : Diagnostic := {
  code := "core.check.inference-failure"
  phase := .contractAdmission
  path := ["contracts", "root", "methods", "read", "implementation"]
  arguments := .mkObj []
}

private def allChecks : Bool :=
  duplicateSignature.isValidExecute && danglingRawId.isValidExecute &&
    staticChecker.isValidExecute &&
    !({ staticChecker with
      path := ["contracts", "root", "methods", "not valid", "implementation"]
    }).isValidExecute &&
    !({ duplicateSignature with
      arguments := .mkObj [
        ("signature", "read(uint256)"),
        ("firstMethod", "read"),
        ("secondMethod", "write")]
    }).isValidExecute

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5DiagnosticValidity : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 diagnostic validity changed")

end Tests.OracleV5DiagnosticValidity
