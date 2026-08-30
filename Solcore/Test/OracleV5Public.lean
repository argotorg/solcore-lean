import Solcore
import Solcore.Oracle.Main

/-! Public-module and NDJSON-dispatch regressions for Oracle v5. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Oracle

private def v5CapabilitiesRequest : Oracle.V5.Request := {
  id := ⟨"public-v5", by decide⟩
  limits := Oracle.V5.Limits.default
  query := .capabilities
}

private def v4CapabilitiesRequest : Oracle.V4.Request := {
  id := ⟨"neighbor-v4", by decide⟩
  limits := Oracle.V4.Limits.default
  query := .capabilities
}

private def fieldEquals
    (json : Lean.Json)
    (field : String)
    (expected : Lean.Json) : Bool :=
  json.getObjValD field == expected

private def v5DispatchExact : Bool :=
  let output := processJsonLine
    (Oracle.V5.Wire.encodeRequestText v5CapabilitiesRequest)
  fieldEquals output "schema" Oracle.V5.schemaVersion &&
    fieldEquals output "id" "public-v5" &&
    fieldEquals output "query" "capabilities" &&
    fieldEquals (output.getObjValD "verdict") "kind" "accepted"

private def v5ProtocolOwnershipExact : Bool :=
  let request :=
    (Oracle.V5.Wire.encodeRequest v5CapabilitiesRequest).setObjVal!
      "future" true
  let output := processJsonLine request.compress
  fieldEquals output "kind" "protocolError" &&
    fieldEquals output "schema" Oracle.V5.schemaVersion &&
    fieldEquals output "id" "public-v5" &&
    fieldEquals output "code" "oracle.wire.unknown-field" &&
    fieldEquals output "path" "/future"

private def v4NeighborUnchanged : Bool :=
  let output := processJsonLine
    (Oracle.V4.encodeRequest v4CapabilitiesRequest).compress
  fieldEquals output "schema" Oracle.V4.schemaVersion &&
    fieldEquals output "id" "neighbor-v4" &&
    fieldEquals output "query" "capabilities" &&
    fieldEquals (output.getObjValD "verdict") "kind" "accepted"

private def allChecks : Bool :=
  v5DispatchExact && v5ProtocolOwnershipExact && v4NeighborUnchanged

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5Public : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 public dispatch changed")

end Tests
