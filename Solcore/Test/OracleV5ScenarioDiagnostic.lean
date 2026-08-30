import Solcore.Oracle.V5.ScenarioDiagnostic

/-! Focused path and argument tests for Oracle v5 scenario diagnostics. -/

set_option autoImplicit false

namespace Tests.OracleV5ScenarioDiagnostic

open Solcore.Oracle.V5
open Solcore.Semantics

private def address : Address := ⟨1, by decide⟩
private def slot : Solcore.Core.Word := ⟨2, by decide⟩

private def addressWire : String := encodeAddressText address
private def slotWire : String := encodeWordText slot

private def zeroStorageExact : Bool :=
  ScenarioDiagnostic.ofWorldError (.zeroStorageValue address slot) == {
    code := "oracle.v5.world.zero-storage-value"
    phase := .worldValidation
    path := ["world", "accounts", addressWire, "storage", slotWire, "value"]
    arguments := .mkObj [("address", addressWire), ("slot", slotWire)]
  }

private def danglingRuntimeExact : Bool :=
  ScenarioDiagnostic.ofEnvironmentError (.danglingRuntime slot "runtime") == {
    code := "oracle.v5.reference.dangling-contract"
    phase := .environmentValidation
    path := ["environment", "creationTemplates", slotWire, "runtime"]
    arguments := .mkObj [("id", "runtime")]
  }

private def duplicateProbeExact : Bool :=
  ScenarioDiagnostic.ofProbeError {
    firstIndex := 1
    secondIndex := 3
    probe := .storage address slot
  } == {
    code := "oracle.v5.probe.duplicate"
    phase := .probeValidation
    path := ["invocation", "probes", "3"]
    arguments := .mkObj [
      ("firstIndex", Lean.toJson 1),
      ("secondIndex", Lean.toJson 3)
    ]
  }

private def preparationWrapperExact : Bool :=
  match ScenarioDiagnostic.ofPreparationError
      (.worldValidation (.duplicateAccount address)) with
  | .error _ => false
  | .ok diagnostic =>
      diagnostic.code == "oracle.v5.world.duplicate-account" &&
        diagnostic.phase == .worldValidation &&
        diagnostic.path == ["world", "accounts", addressWire]

private def allChecks : Bool :=
  zeroStorageExact && danglingRuntimeExact && duplicateProbeExact &&
    preparationWrapperExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ScenarioDiagnostic : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 scenario diagnostics changed")

end Tests.OracleV5ScenarioDiagnostic
