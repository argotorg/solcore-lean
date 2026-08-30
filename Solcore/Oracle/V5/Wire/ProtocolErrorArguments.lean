import Solcore.Oracle.V5.ProtocolErrorValidity
import Solcore.Oracle.V5.Wire.Foundation

/-! Closed code and argument decoding for public Oracle v5 protocol errors. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire.ProtocolErrorDecoding

inductive CodeOwner where
  | malformed
  | oracle
  | core
  deriving Repr, BEq, DecidableEq

def oracleCodes : List String := [
  "oracle.wire.expected-object", "oracle.wire.expected-array",
  "oracle.wire.expected-string", "oracle.wire.expected-bool",
  "oracle.wire.expected-natural", "oracle.wire.missing-field",
  "oracle.wire.unknown-field", "oracle.wire.invalid-schema",
  "oracle.wire.invalid-spec", "oracle.wire.invalid-profile",
  "oracle.wire.invalid-tag", "oracle.wire.invalid-word",
  "oracle.wire.invalid-address", "oracle.wire.invalid-bytes",
  "oracle.wire.invalid-request-id", "oracle.wire.invalid-limit"
]

def coreCodes : List String := [
  "core.wire.expected-object", "core.wire.expected-array",
  "core.wire.expected-string", "core.wire.expected-bool",
  "core.wire.expected-natural", "core.wire.missing-field",
  "core.wire.unknown-field", "core.wire.invalid-schema",
  "core.wire.invalid-tag", "core.wire.invalid-type",
  "core.wire.invalid-word"
]

def allCodes : List String := "malformed-json" :: oracleCodes ++ coreCodes

def classifyCode? (code : String) : Option CodeOwner :=
  if code == "malformed-json" then some .malformed
  else if oracleCodes.contains code then some .oracle
  else if coreCodes.contains code then some .core
  else none

private def jsonKinds : List String :=
  ["null", "boolean", "number", "string", "array", "object"]

private def decodeExpectedArgumentsAt
    (path : Path)
    (json : Lean.Json)
    (expected : String) : DecodeResult Lean.Json := do
  ensureExactObject path json ["actual", "expected"] ["actual", "expected"]
  let actualPath := path.field "actual"
  let actual ← decodeStringAt actualPath (← requireField path json "actual")
  unless jsonKinds.contains actual do
    invalidTagAt actualPath actual (.arr <| jsonKinds.toArray.map Lean.Json.str)
  let expectedPath := path.field "expected"
  let decodedExpected ← decodeStringAt expectedPath
    (← requireField path json "expected")
  unless decodedExpected == expected do
    invalidTagAt expectedPath decodedExpected expected
  unless expected == "number" || actual != expected do
    invalidTagAt actualPath actual <| .mkObj [
      ("constraint", "different-from-expected"), ("expected", expected)]
  pure <| .mkObj [("actual", actual), ("expected", expected)]

private def decodeFieldArgumentsAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Lean.Json := do
  ensureExactObject path json ["field"] ["field"]
  let field ← decodeStringAt (path.field "field")
    (← requireField path json "field")
  pure <| .mkObj [("field", field)]

private def decodeIdentityArgumentsAt
    (path : Path)
    (json : Lean.Json)
    (allowedExpected : List String) : DecodeResult Lean.Json := do
  ensureExactObject path json ["actual", "expected"] ["actual", "expected"]
  let actualPath := path.field "actual"
  let actual ← decodeStringAt actualPath (← requireField path json "actual")
  let expectedPath := path.field "expected"
  let expected ← decodeStringAt expectedPath
    (← requireField path json "expected")
  unless allowedExpected.contains expected do
    invalidTagAt expectedPath expected <|
      .arr (allowedExpected.toArray.map Lean.Json.str)
  unless actual != expected do
    invalidTagAt actualPath actual <| .mkObj [
      ("constraint", "different-from-expected"), ("expected", expected)]
  pure <| .mkObj [("actual", actual), ("expected", expected)]

private def decodeProfileArgumentsAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Lean.Json := do
  let fields := ["actualDigest", "actualId", "expectedDigest", "expectedId"]
  ensureExactObject path json fields fields
  let actualDigestPath := path.field "actualDigest"
  let actualDigest ← decodeStringAt actualDigestPath
    (← requireField path json "actualDigest")
  let actualId ← decodeStringAt (path.field "actualId")
    (← requireField path json "actualId")
  let canonical := ProfileRef.canonical
  let expectedDigest ← decodeStringAt (path.field "expectedDigest")
    (← requireField path json "expectedDigest")
  unless expectedDigest == canonical.digest do
    invalidTagAt (path.field "expectedDigest") expectedDigest canonical.digest
  let expectedId ← decodeStringAt (path.field "expectedId")
    (← requireField path json "expectedId")
  unless expectedId == canonical.id do
    invalidTagAt (path.field "expectedId") expectedId canonical.id
  unless actualId != expectedId || actualDigest != expectedDigest do
    invalidTagAt actualDigestPath actualDigest <| .mkObj [
      ("constraint", "profile-differs-from-expected")]
  pure <| .mkObj [
    ("actualDigest", actualDigest), ("actualId", actualId),
    ("expectedDigest", expectedDigest), ("expectedId", expectedId)]

private def decodeTagArgumentsAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Lean.Json := do
  ensureExactObject path json ["actual", "expected"] ["actual", "expected"]
  let actual ← requireField path json "actual"
  let expected ← requireField path json "expected"
  pure <| .mkObj [("actual", actual), ("expected", expected)]

private def decodeReasonArgumentsAt
    (path : Path)
    (json : Lean.Json)
    (allowed : List String) : DecodeResult Lean.Json := do
  ensureExactObject path json ["reason"] ["reason"]
  let reasonPath := path.field "reason"
  let reason ← decodeStringAt reasonPath (← requireField path json "reason")
  unless allowed.contains reason do
    invalidTagAt reasonPath reason (.arr <| allowed.toArray.map Lean.Json.str)
  pure <| .mkObj [("reason", reason)]

private def decodeLiteralArgumentsAt
    (path : Path)
    (json : Lean.Json)
    (name expected : String) : DecodeResult Lean.Json := do
  ensureExactObject path json [name] [name]
  let valuePath := path.field name
  let value ← decodeStringAt valuePath (← requireField path json name)
  unless value == expected do invalidTagAt valuePath value expected
  pure <| .mkObj [(name, expected)]

private partial def decodeFixedStringsAt
    (path : Path)
    (index : Nat)
    (actual expected : List Lean.Json) : DecodeResult Unit := do
  match actual, expected with
  | [], [] => pure ()
  | value :: rest, wanted :: wantedRest =>
      let value ← decodeStringAt (path.index index) value
      let wanted ← decodeStringAt (path.index index) wanted
      unless value == wanted do invalidTagAt (path.index index) value wanted
      decodeFixedStringsAt path (index + 1) rest wantedRest
  | _, _ =>
      invalidTagAt path
        (Lean.Json.mkObj [("length", index + actual.length)])
        (Lean.Json.mkObj [("length", index + expected.length)])

private inductive CoreAllowed where
  | values
  | jsonKinds

private def CoreAllowed.json : CoreAllowed → Lean.Json
  | .values => .arr #["unit", "bool", "word"]
  | .jsonKinds => .arr #["string", "object"]

private def CoreAllowed.valuesList : CoreAllowed → List Lean.Json
  | .values => ["unit", "bool", "word"]
  | .jsonKinds => ["string", "object"]

private def decodeCoreAllowedAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CoreAllowed := do
  let values ← match json with
    | .arr values => pure values.toList
    | _ => failAt path .expectedArray (expectedArguments "array" json)
  let first ← match values with
    | value :: _ => decodeStringAt (path.index 0) value
    | [] => invalidTagAt path (.mkObj [("length", 0)]) <|
        .mkObj [("length", .arr #[2, 3])]
  let allowed ← if first == "unit" then pure CoreAllowed.values
    else if first == "string" then pure CoreAllowed.jsonKinds
    else invalidTagAt (path.index 0) first (.arr #["unit", "string"])
  decodeFixedStringsAt path 0 values allowed.valuesList
  pure allowed

private def decodeCoreTypeArgumentsAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Lean.Json := do
  ensureExactObject path json ["actual", "allowed"] ["actual", "allowed"]
  let actualPath := path.field "actual"
  let actual ← decodeStringAt actualPath (← requireField path json "actual")
  let allowed ← decodeCoreAllowedAt (path.field "allowed")
    (← requireField path json "allowed")
  let actualAllowed := match allowed with
    | .values => !["unit", "bool", "word"].contains actual
    | .jsonKinds => ["null", "boolean", "number", "array"].contains actual
  unless actualAllowed do
    invalidTagAt actualPath actual <| .mkObj [
      ("constraint", "not-in-allowed-types")]
  pure <| .mkObj [("actual", actual), ("allowed", allowed.json)]

private def decodeBroadArgumentsAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Lean.Json :=
  match json with
  | .null | .obj _ => pure json
  | _ => invalidTagAt path json (.arr #["object", "null"])

private def decodeKnownArgumentsAt
    (path : Path)
    (code : String)
    (json : Lean.Json) : DecodeResult Lean.Json :=
  match code with
  | "malformed-json" =>
      if json == .null then pure .null else invalidTagAt path json .null
  | "oracle.wire.expected-object" | "core.wire.expected-object" =>
      decodeExpectedArgumentsAt path json "object"
  | "oracle.wire.expected-array" | "core.wire.expected-array" =>
      decodeExpectedArgumentsAt path json "array"
  | "oracle.wire.expected-string" | "core.wire.expected-string" =>
      decodeExpectedArgumentsAt path json "string"
  | "oracle.wire.expected-bool" | "core.wire.expected-bool" =>
      decodeExpectedArgumentsAt path json "boolean"
  | "oracle.wire.expected-natural" | "core.wire.expected-natural" =>
      decodeExpectedArgumentsAt path json "number"
  | "oracle.wire.missing-field" | "oracle.wire.unknown-field"
  | "core.wire.missing-field" | "core.wire.unknown-field" =>
      decodeFieldArgumentsAt path json
  | "oracle.wire.invalid-schema" => decodeIdentityArgumentsAt path json [
      schemaVersion, capabilitiesSchema, checkResultSchema,
      executionSchema, stateObservationSchema]
  | "oracle.wire.invalid-spec" =>
      decodeIdentityArgumentsAt path json [Solcore.m3aLanguage.id]
  | "core.wire.invalid-schema" => decodeIdentityArgumentsAt path json [
      Solcore.Core.Wire.V3.schemaVersion]
  | "oracle.wire.invalid-profile" => decodeProfileArgumentsAt path json
  | "oracle.wire.invalid-tag" | "core.wire.invalid-tag" =>
      decodeTagArgumentsAt path json
  | "oracle.wire.invalid-word" | "oracle.wire.invalid-address"
  | "core.wire.invalid-word" => decodeReasonArgumentsAt path json
      ["prefix", "length", "lowercase-hex"]
  | "oracle.wire.invalid-bytes" => decodeReasonArgumentsAt path json
      ["prefix", "odd-length", "lowercase-hex"]
  | "oracle.wire.invalid-request-id" =>
      decodeLiteralArgumentsAt path json "constraint" "nonempty-utf8"
  | "oracle.wire.invalid-limit" => do
      ensureExactObject path json ["constraint", "field"] ["constraint", "field"]
      let constraint ← decodeStringAt (path.field "constraint")
        (← requireField path json "constraint")
      unless constraint == "strictly-less-than-2^256" do
        invalidTagAt (path.field "constraint") constraint
          "strictly-less-than-2^256"
      let field ← decodeStringAt (path.field "field")
        (← requireField path json "field")
      unless field == "calldataBytes" do
        invalidTagAt (path.field "field") field "calldataBytes"
      pure <| .mkObj [("constraint", constraint), ("field", field)]
  | "core.wire.invalid-type" => decodeCoreTypeArgumentsAt path json
  | _ => decodeBroadArgumentsAt path json

/-- Decode arguments according to a non-failing raw code discriminator read. -/
def decodeArgumentsAt
    (path : Path)
    (rawCode arguments : Lean.Json) : DecodeResult Lean.Json :=
  match rawCode with
  | .str code => decodeKnownArgumentsAt path code arguments
  | _ => decodeBroadArgumentsAt path arguments

/-- Decode one closed public protocol-error code after argument validation. -/
def decodeCodeAt
    (path : Path)
    (json : Lean.Json) : DecodeResult (String × CodeOwner) := do
  let code ← decodeStringAt path json
  match classifyCode? code with
  | some owner => pure (code, owner)
  | none => invalidTagAt path code (.arr <| allCodes.toArray.map Lean.Json.str)

private def escapePointerToken (value : String) : String :=
  (value.replace "~" "~0").replace "/" "~1"

private def pointerEndsWithField (path field : String) : Bool :=
  path.endsWith ("/" ++ escapePointerToken field)

/-- Check the catalog's code-specific pointer relationship once path is known. -/
def validatePathAt
    (wirePath : Path)
    (code path : String)
    (arguments : Lean.Json) : DecodeResult Unit := do
  let field? := Diagnostic.Catalog.stringField? arguments "field"
  let valid := match code with
    | "oracle.wire.missing-field" | "oracle.wire.unknown-field"
    | "core.wire.missing-field" | "core.wire.unknown-field" =>
        match field? with
        | some field => pointerEndsWithField path field
        | none => false
    | "oracle.wire.invalid-schema" | "core.wire.invalid-schema" =>
        pointerEndsWithField path "schema"
    | "oracle.wire.invalid-spec" => pointerEndsWithField path "spec"
    | "oracle.wire.invalid-profile" => path == "/profile"
    | "oracle.wire.invalid-request-id" => path == "/id"
    | "oracle.wire.invalid-limit" => path == "/limits/calldataBytes"
    | _ => true
  unless valid do
    invalidTagAt wirePath path <| .mkObj [
      ("constraint", "code-compatible-json-pointer"), ("code", code)]

end Solcore.Oracle.V5.Wire.ProtocolErrorDecoding
