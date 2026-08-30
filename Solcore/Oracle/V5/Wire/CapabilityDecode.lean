import Solcore.Oracle.V5.Wire.ResponseShape

/-! Strict singleton decoding for the Oracle v5 capability report. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

mutual

partial def decodeExpectedJsonAt
    (path : Path)
    (actual expected : Lean.Json) : DecodeResult Unit :=
  match expected with
  | .null => unless actual == .null do invalidTagAt path actual .null
  | .bool wanted => do
      let value ← decodeBoolAt path actual
      unless value == wanted do invalidTagAt path value wanted
  | .str wanted => do
      let value ← decodeStringAt path actual
      unless value == wanted do invalidTagAt path value wanted
  | .num _ =>
      match Solcore.Foundation.jsonNatural? expected with
      | some wanted => do
          let value ← decodeNatAt path actual
          unless value == wanted do invalidTagAt path value wanted
      | none => unless actual == expected do invalidTagAt path actual expected
  | .arr wanted =>
      match actual with
      | .arr values =>
          decodeExpectedArrayAt path 0 values.toList wanted.toList
      | _ => failAt path .expectedArray (expectedArguments "array" actual)
  | .obj wanted => do
      let fields := wanted.keys
      ensureExactObject path actual fields fields
      decodeExpectedFieldsAt path actual wanted.toList

partial def decodeExpectedArrayAt
    (path : Path) :
    Nat → List Lean.Json → List Lean.Json → DecodeResult Unit
  | _, [], [] => pure ()
  | index, actual :: rest, wanted :: wantedRest => do
      decodeExpectedJsonAt (path.index index) actual wanted
      decodeExpectedArrayAt path (index + 1) rest wantedRest
  | index, actual, wanted =>
      invalidTagAt path
        (.mkObj [("length", index + actual.length)])
        (.mkObj [("length", index + wanted.length)])

partial def decodeExpectedFieldsAt
    (path : Path)
    (actual : Lean.Json) :
    List (String × Lean.Json) → DecodeResult Unit
  | [] => pure ()
  | (name, wanted) :: rest => do
      decodeExpectedJsonAt (path.field name)
        (← requireField path actual name) wanted
      decodeExpectedFieldsAt path actual rest

end

private def capabilityFields : List String := [
  "abiProfiles", "baselines", "checkResultSchema", "contractProfiles",
  "coreSchema", "defaultLimits", "executionSchema", "features",
  "implementedQueries", "maxNestedCallDepth", "observationKinds", "profile",
  "profileDigest", "schema", "spec", "stateObservationSchema"
]

private def decodeCapabilityReportAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CapabilityReport := do
  ensureExactObject path json capabilityFields capabilityFields
  let expected := capabilityReport
  decodeExpectedJsonAt (path.field "abiProfiles")
    (← requireField path json "abiProfiles")
    (.arr <| expected.abiProfiles.map Lean.Json.str)
  decodeExpectedJsonAt (path.field "baselines")
    (← requireField path json "baselines") (Lean.toJson expected.baselines)
  requireLiteralAt (path.field "checkResultSchema")
    (← requireField path json "checkResultSchema") expected.checkResultSchema
  decodeExpectedJsonAt (path.field "contractProfiles")
    (← requireField path json "contractProfiles")
    (.arr <| expected.contractProfiles.map Lean.Json.str)
  requireLiteralAt (path.field "coreSchema")
    (← requireField path json "coreSchema") expected.coreSchema
  decodeExpectedJsonAt (path.field "defaultLimits")
    (← requireField path json "defaultLimits")
    (encodeLimits expected.defaultLimits)
  requireLiteralAt (path.field "executionSchema")
    (← requireField path json "executionSchema") expected.executionSchema
  decodeExpectedJsonAt (path.field "features")
    (← requireField path json "features") (Lean.toJson expected.features)
  decodeExpectedJsonAt (path.field "implementedQueries")
    (← requireField path json "implementedQueries")
    (.arr <| expected.implementedQueries.map encodeQueryKind)
  decodeExpectedJsonAt (path.field "maxNestedCallDepth")
    (← requireField path json "maxNestedCallDepth")
    (Lean.toJson expected.maxNestedCallDepth)
  decodeExpectedJsonAt (path.field "observationKinds")
    (← requireField path json "observationKinds")
    (.arr <| expected.observationKinds.map Lean.Json.str)
  decodeExpectedJsonAt (path.field "profile")
    (← requireField path json "profile") (Lean.toJson expected.profile)
  requireLiteralAt (path.field "profileDigest")
    (← requireField path json "profileDigest") expected.profileDigest
  let schemaPath := path.field "schema"
  let schema ← decodeStringAt schemaPath (← requireField path json "schema")
  unless schema == expected.schema do
    failAt schemaPath .invalidSchema (.mkObj [
      ("expected", expected.schema), ("actual", schema)
    ])
  let specPath := path.field "spec"
  let spec ← decodeStringAt specPath (← requireField path json "spec")
  unless spec == expected.spec do
    failAt specPath .invalidSpec (.mkObj [
      ("expected", expected.spec), ("actual", spec)
    ])
  requireLiteralAt (path.field "stateObservationSchema")
    (← requireField path json "stateObservationSchema")
      expected.stateObservationSchema
  pure .canonical

def decodeCapabilityResultAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CapabilityReport := do
  ensureExactObject path json ["schema", "value"] ["schema", "value"]
  let schemaPath := path.field "schema"
  let schema ← decodeStringAt schemaPath (← requireField path json "schema")
  unless schema == capabilitiesSchema do
    failAt schemaPath .invalidSchema (.mkObj [
      ("expected", capabilitiesSchema), ("actual", schema)
    ])
  decodeCapabilityReportAt (path.field "value")
    (← requireField path json "value")

end Solcore.Oracle.V5.Wire
