import Solcore.Oracle.V5.Wire.Protocol

/-! Focused strict-decoding tests for the Oracle v5 protocol-error partition. -/

set_option autoImplicit false

namespace Tests.OracleV5ProtocolErrorDecode

open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire

private def requestId : RequestId := ⟨"protocol-id", by decide⟩

private def oracleExpectedRaw : Solcore.Oracle.V5.ProtocolError := {
  id := some requestId
  code := "oracle.wire.expected-object"
  path := "/query"
  arguments := .mkObj [("actual", "string"), ("expected", "object")]
  display := "invalid Oracle v5 value"
}

private def oracleExpected : ValidProtocolError :=
  (ValidProtocolError.of? oracleExpectedRaw).get (by native_decide)

private def oracleProfileRaw : Solcore.Oracle.V5.ProtocolError := {
  code := "oracle.wire.invalid-profile"
  path := "/profile"
  arguments := .mkObj [
    ("actualDigest", "future-digest"), ("actualId", "future-profile"),
    ("expectedDigest", ProfileRef.canonical.digest),
    ("expectedId", ProfileRef.canonical.id)]
  display := "invalid Oracle v5 value"
}

private def oracleProfile : ValidProtocolError :=
  (ValidProtocolError.of? oracleProfileRaw).get (by native_decide)

private def coreTypeRaw : Solcore.Oracle.V5.ProtocolError := {
  code := "core.wire.invalid-type"
  path := "/query/program/resultType"
  arguments := .mkObj [
    ("actual", "array"), ("allowed", .arr #["string", "object"])]
  display := "invalid Semantic Core v3 program"
}

private def coreType : ValidProtocolError :=
  (ValidProtocolError.of? coreTypeRaw).get (by native_decide)

private def coreWordRaw : Solcore.Oracle.V5.ProtocolError := {
  code := "core.wire.invalid-word"
  path := "/query/program/definitions/0/value"
  arguments := .mkObj [("reason", "length")]
  display := "invalid Semantic Core v3 program"
}

private def coreWord : ValidProtocolError :=
  (ValidProtocolError.of? coreWordRaw).get (by native_decide)

private def naturalErrorRaw (owner : Bool) : Solcore.Oracle.V5.ProtocolError := {
  code := if owner then "core.wire.expected-natural"
    else "oracle.wire.expected-natural"
  path := "/limits/jsonDepth"
  arguments := .mkObj [("actual", "number"), ("expected", "number")]
  display := if owner then "invalid Semantic Core v3 program"
    else "invalid Oracle v5 value"
}

private def oracleNatural : ValidProtocolError :=
  (ValidProtocolError.of? (naturalErrorRaw false)).get (by native_decide)

private def coreNatural : ValidProtocolError :=
  (ValidProtocolError.of? (naturalErrorRaw true)).get (by native_decide)

private def escapedFieldRaw : Solcore.Oracle.V5.ProtocolError := {
  code := "oracle.wire.unknown-field"
  path := "/a~1b"
  arguments := .mkObj [("field", "a/b")]
  display := "invalid Oracle v5 value"
}

private def escapedField : ValidProtocolError :=
  (ValidProtocolError.of? escapedFieldRaw).get (by native_decide)

private def errors : List ValidProtocolError := [
  ValidProtocolError.malformedJson "duplicate object key: kind",
  oracleExpected, oracleProfile, oracleNatural, coreType, coreWord,
  coreNatural, escapedField
]

private def roundTrips : Bool :=
  errors.all fun expected =>
    match decodeProtocolErrorValue (encodeProtocolError expected) with
    | .ok actual => actual == expected
    | .error _ => false

private def catalogExpectedArguments (expected : String) : Lean.Json :=
  .mkObj [("actual", "null"), ("expected", expected)]

private def oracleArguments : DecodeErrorCode → Lean.Json
  | .expectedObject => catalogExpectedArguments "object"
  | .expectedArray => catalogExpectedArguments "array"
  | .expectedString => catalogExpectedArguments "string"
  | .expectedBool => catalogExpectedArguments "boolean"
  | .expectedNatural => catalogExpectedArguments "number"
  | .missingField => .mkObj [("field", "missing")]
  | .unknownField => .mkObj [("field", "future")]
  | .invalidSchema => .mkObj [("actual", "future"), ("expected", schemaVersion)]
  | .invalidSpec => .mkObj [
      ("actual", "future"), ("expected", Solcore.m3aLanguage.id)]
  | .invalidProfile => .mkObj [
      ("actualDigest", "sha256:future"), ("actualId", "future"),
      ("expectedDigest", ProfileRef.canonical.digest),
      ("expectedId", ProfileRef.canonical.id)]
  | .invalidTag => .mkObj [("actual", "future"), ("expected", "known")]
  | .invalidWord => .mkObj [("reason", "prefix")]
  | .invalidAddress => .mkObj [("reason", "length")]
  | .invalidBytes => .mkObj [("reason", "odd-length")]
  | .invalidRequestId => .mkObj [("constraint", "nonempty-utf8")]
  | .invalidLimit => .mkObj [
      ("constraint", "strictly-less-than-2^256"),
      ("field", "calldataBytes")]

private def oraclePath : DecodeErrorCode → Path
  | .missingField => Path.root.field "missing"
  | .unknownField => Path.root.field "future"
  | .invalidSchema => Path.root.field "schema"
  | .invalidSpec => Path.root.field "spec"
  | .invalidProfile => Path.root.field "profile"
  | .invalidRequestId => Path.root.field "id"
  | .invalidLimit => (Path.root.field "limits").field "calldataBytes"
  | _ => Path.root.field "value"

private def oracleCodes : List DecodeErrorCode := [
  .expectedObject, .expectedArray, .expectedString, .expectedBool,
  .expectedNatural, .missingField, .unknownField, .invalidSchema,
  .invalidSpec, .invalidProfile, .invalidTag, .invalidWord,
  .invalidAddress, .invalidBytes, .invalidRequestId, .invalidLimit]

private def coreArguments :
    Solcore.Core.Wire.V3.DecodeErrorCode → Lean.Json
  | .expectedObject => catalogExpectedArguments "object"
  | .expectedArray => catalogExpectedArguments "array"
  | .expectedString => catalogExpectedArguments "string"
  | .expectedBool => catalogExpectedArguments "boolean"
  | .expectedNatural => catalogExpectedArguments "number"
  | .missingField => .mkObj [("field", "missing")]
  | .unknownField => .mkObj [("field", "future")]
  | .invalidSchema => .mkObj [
      ("actual", "future"),
      ("expected", Solcore.Core.Wire.V3.schemaVersion)]
  | .invalidTag => .mkObj [("actual", "future"), ("expected", "known")]
  | .invalidType => .mkObj [
      ("actual", "future"), ("allowed", .arr #["unit", "bool", "word"])]
  | .invalidWord => .mkObj [("reason", "lowercase-hex")]

private def corePath
    (code : Solcore.Core.Wire.V3.DecodeErrorCode) :
    Solcore.Core.Wire.V3.DecodePath :=
  match code with
  | .missingField => Solcore.Core.Wire.V3.DecodePath.root.field "missing"
  | .unknownField => Solcore.Core.Wire.V3.DecodePath.root.field "future"
  | .invalidSchema => Solcore.Core.Wire.V3.DecodePath.root.field "schema"
  | _ => Solcore.Core.Wire.V3.DecodePath.root.field "program"

private def coreCodes : List Solcore.Core.Wire.V3.DecodeErrorCode := [
  .expectedObject, .expectedArray, .expectedString, .expectedBool,
  .expectedNatural, .missingField, .unknownField, .invalidSchema,
  .invalidTag, .invalidType, .invalidWord]

private def oracleCatalogRoundTrip (code : DecodeErrorCode) : Bool :=
  let internal : Solcore.Oracle.V5.Wire.ProtocolError :=
    .oracle (oraclePath code) code (oracleArguments code)
  let expected := internal.toPublic (some requestId)
  match decodeProtocolErrorValue (encodeProtocolError expected) with
  | .ok actual => actual == expected
  | .error _ => false

private def coreCatalogRoundTrip
    (code : Solcore.Core.Wire.V3.DecodeErrorCode) : Bool :=
  let core : Solcore.Core.Wire.V3.DecodeError := {
    path := corePath code
    code
    arguments := coreArguments code
  }
  let expected :=
    (Solcore.Oracle.V5.Wire.ProtocolError.core core).toPublic (some requestId)
  match decodeProtocolErrorValue (encodeProtocolError expected) with
  | .ok actual => actual == expected
  | .error _ => false

private def allClosedCodesRoundTrip : Bool :=
  (match decodeProtocolErrorValue <| encodeProtocolError <|
      ValidProtocolError.malformedJson "bad json" with
    | .ok actual => actual.code == "malformed-json"
    | .error _ => false) &&
    oracleCodes.all oracleCatalogRoundTrip &&
    coreCodes.all coreCatalogRoundTrip

private def errorAt {alpha : Type}
    (result : DecodeResult alpha)
    (pointer : String)
    (code : DecodeErrorCode) : Bool :=
  match result with
  | .error (.oracle path actualCode _) =>
      path.toPointer == pointer && actualCode == code
  | _ => false

private def publicErrorAt {alpha : Type}
    (result : Except ValidProtocolError alpha)
    (pointer code : String) : Bool :=
  match result with
  | .error error => error.path == pointer && error.code == code
  | .ok _ => false

private def envelopeAndLexicographicPrecedence : Bool :=
  let encoded := encodeProtocolError oracleExpected
  let unknown := encoded.setObjVal! "aaa" true
  let argumentsBeforeCode := (encoded.setObjVal! "arguments" true)
    |>.setObjVal! "code" true
  let codeBeforeDisplay := (encoded.setObjVal! "code" "future")
    |>.setObjVal! "display" false
  let displayBeforeId := (encoded.setObjVal! "display" "future")
    |>.setObjVal! "id" ""
  let idBeforeKind := (encoded.setObjVal! "id" "")
    |>.setObjVal! "kind" "future"
  let kindBeforePath := (encoded.setObjVal! "kind" "future")
    |>.setObjVal! "path" "not-a-pointer"
  let pathBeforeSchema := (encoded.setObjVal! "path" "not-a-pointer")
    |>.setObjVal! "schema" "future"
  errorAt (decodeProtocolErrorValue unknown) "/aaa" .unknownField &&
    errorAt (decodeProtocolErrorValue argumentsBeforeCode)
      "/arguments" .invalidTag &&
    errorAt (decodeProtocolErrorValue codeBeforeDisplay)
      "/code" .invalidTag &&
    errorAt (decodeProtocolErrorValue displayBeforeId)
      "/display" .invalidTag &&
    errorAt (decodeProtocolErrorValue idBeforeKind)
      "/id" .invalidRequestId &&
    errorAt (decodeProtocolErrorValue kindBeforePath)
      "/kind" .invalidTag &&
    errorAt (decodeProtocolErrorValue pathBeforeSchema)
      "/path" .invalidTag

private def argumentShapeAndIndexPrecedence : Bool :=
  let encodedExpected := encodeProtocolError oracleExpected
  let expectedArguments := encodedExpected.getObjValD "arguments"
  let badActual := encodedExpected.setObjVal! "arguments" <|
    expectedArguments.setObjVal! "actual" false
  let extraArgument := encodedExpected.setObjVal! "arguments" <|
    expectedArguments.setObjVal! "zzz" true
  let encodedCore := encodeProtocolError coreType
  let coreArguments := encodedCore.getObjValD "arguments"
  let badFirst := encodedCore.setObjVal! "arguments" <|
    coreArguments.setObjVal! "allowed" (.arr #["bad", 7])
  let badSecond := encodedCore.setObjVal! "arguments" <|
    coreArguments.setObjVal! "allowed" (.arr #["unit", 7, "word"])
  errorAt (decodeProtocolErrorValue badActual)
      "/arguments/actual" .expectedString &&
    errorAt (decodeProtocolErrorValue extraArgument)
      "/arguments/zzz" .unknownField &&
    errorAt (decodeProtocolErrorValue badFirst)
      "/arguments/allowed/0" .invalidTag &&
    errorAt (decodeProtocolErrorValue badSecond)
      "/arguments/allowed/1" .expectedString

private def malformedAndPointerConstraints : Bool :=
  let malformed := encodeProtocolError <|
    ValidProtocolError.malformedJson "bad input"
  let badArguments := malformed.setObjVal! "arguments" (.mkObj [])
  let badId := malformed.setObjVal! "id" "protocol-id"
  let badPath := malformed.setObjVal! "path" "/future"
  let wrongFieldPath := (encodeProtocolError escapedField).setObjVal!
    "path" "/different"
  let loneEscape := (encodeProtocolError oracleExpected).setObjVal!
    "path" "/bad~"
  errorAt (decodeProtocolErrorValue badArguments)
      "/arguments" .invalidTag &&
    errorAt (decodeProtocolErrorValue badId) "/id" .invalidTag &&
    errorAt (decodeProtocolErrorValue badPath) "/path" .invalidTag &&
    errorAt (decodeProtocolErrorValue wrongFieldPath)
      "/path" .invalidTag &&
    errorAt (decodeProtocolErrorValue loneEscape) "/path" .invalidTag

private def dedicatedSchemaAndRecoveredId : Bool :=
  let encoded := encodeProtocolError oracleExpected
  let badSchema := encoded.setObjVal! "schema" "future"
  let badKind := encoded.setObjVal! "kind" "future"
  errorAt (decodeProtocolErrorValue badSchema)
      "/schema" .invalidSchema &&
    (match decodeProtocolErrorJson badKind with
    | .error error =>
        error.id == some requestId && error.path == "/kind" &&
          error.code == "oracle.wire.invalid-tag"
    | .ok _ => false)

private def directTextAndCanonicalization : Bool :=
  let canonical := encodeProtocolErrorText coreType
  let padded := " \n" ++ canonical ++ " \n"
  let duplicate :=
    "{\"arguments\":null,\"code\":\"malformed-json\"," ++
    "\"display\":\"bad\",\"id\":null,\"kind\":\"protocolError\"," ++
    "\"kind\":\"protocolError\",\"path\":\"\",\"schema\":" ++
    "\"solcore-oracle/v5\"}"
  (match canonicalizeProtocolErrorText padded with
  | .ok actual => actual == canonical
  | .error _ => false) &&
    (match decodeProtocolErrorText duplicate with
    | .error error => error.code == "malformed-json" && error.id.isNone
    | .ok _ => false)

private def allChecks : Bool :=
  roundTrips && allClosedCodesRoundTrip &&
    envelopeAndLexicographicPrecedence &&
    argumentShapeAndIndexPrecedence && malformedAndPointerConstraints &&
    dedicatedSchemaAndRecoveredId && directTextAndCanonicalization

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ProtocolErrorDecode : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 protocol-error decoding changed")

end Tests.OracleV5ProtocolErrorDecode
