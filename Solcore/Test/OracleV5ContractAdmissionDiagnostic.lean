import Solcore.Oracle.V5.ContractAdmissionDiagnostic

/-! Focused wire-shape tests for contract-admission diagnostics. -/

set_option autoImplicit false

namespace Tests.OracleV5ContractAdmissionDiagnostic

open Solcore.Oracle.V5

private def contract : ContractId := ⟨"root", by decide⟩
private def other : ContractId := ⟨"other", by decide⟩

private def selector : Solcore.Abi.V1.Selector :=
  ⟨#v[0xde, 0xad, 0xbe, 0xef]⟩

private def project
    (error : ContractAdmissionError) : Option Diagnostic :=
  match ContractAdmissionDiagnostic.ofError error with
  | .error _ => none
  | .ok diagnostic => some diagnostic

private def invalidIdExact : Bool :=
  project (.invalidContractId "bad id!") == some {
    code := "oracle.v5.contract.invalid-id"
    phase := .contractAdmission
    path := ["contracts", "bad id!", "id"]
    arguments := .mkObj [("actual", "bad id!")]
  }

private def checkerPrefixExact : Bool :=
  project (.coreCheckFailed (.staticMethod contract "read") {
    path := [.binaryLeft, .matchBranch 4]
    data := .unboundVariable 15 14
  }) == some {
    code := "core.check.unbound-variable"
    phase := .contractAdmission
    path := ["contracts", "root", "methods", "read", "implementation",
      "binaryLeft", "matchBranch[4]"]
    arguments := .mkObj [
      ("index", Lean.toJson 15),
      ("contextSize", Lean.toJson 14)
    ]
  }

private def entryTypeExact : Bool :=
  project (.unsupportedEntryResultType contract
    (.function .word .bool)) == some {
      code := "oracle.v5.contract.unsupported-entry-result-type"
      phase := .contractAdmission
      path := ["contracts", "root", "program", "resultType"]
      arguments := .mkObj [
        ("actual", .mkObj [
          ("parameter", .str "word"),
          ("result", .str "bool"),
          ("tag", .str "function")
        ])
      ]
    }

private def selectorExact : Bool :=
  project (.selectorCollision contract "first(uint256)" "second(uint256)"
    selector) == some {
      code := "oracle.v5.abi.selector-collision"
      phase := .contractAdmission
      path := ["contracts", "root", "methods"]
      arguments := .mkObj [
        ("selector", "deadbeef"),
        ("firstSignature", "first(uint256)"),
        ("secondSignature", "second(uint256)")
      ]
    }

private def duplicateCodeExact : Bool :=
  project (.duplicateCode contract other) == some {
    code := "oracle.v5.contract.duplicate-code"
    phase := .contractAdmission
    path := ["contracts", "other"]
    arguments := .mkObj [("firstId", "root"), ("secondId", "other")]
  }

private def allChecks : Bool :=
  invalidIdExact && checkerPrefixExact && entryTypeExact && selectorExact &&
    duplicateCodeExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ContractAdmissionDiagnostic : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 contract-admission diagnostics changed")

end Tests.OracleV5ContractAdmissionDiagnostic
