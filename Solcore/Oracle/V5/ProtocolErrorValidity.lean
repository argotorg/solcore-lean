import Solcore.Oracle.V5.Response

/-! Closed validity for protocol errors admitted to the public v5 encoder. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

namespace ProtocolError

open Diagnostic.Catalog

private def isLiteral (expected actual : Lean.Json) : Bool :=
  actual == expected

private def isJsonKind (json : Lean.Json) : Bool :=
  match stringValue? json with
  | some value =>
      ["null", "boolean", "number", "string", "array", "object"].contains value
  | none => false

private def validExpectedArguments
    (expected : String)
    (arguments : Lean.Json) : Bool :=
  match stringField? arguments "expected", stringField? arguments "actual" with
  | some actualExpected, some actual =>
      actualExpected == expected && actual != expected &&
        isJsonKind actual && arguments == .mkObj [
          ("expected", actualExpected), ("actual", actual)]
  | _, _ => false

private def escapePointerToken (value : String) : String :=
  (value.replace "~" "~0").replace "/" "~1"

private def pointerEndsWithField (path field : String) : Bool :=
  path.endsWith ("/" ++ escapePointerToken field)

private def validFieldArguments
    (path : String)
    (arguments : Lean.Json) : Bool :=
  match stringField? arguments "field" with
  | some field =>
      pointerEndsWithField path field &&
        arguments == .mkObj [("field", field)]
  | none => false

private def validIdentityArguments
    (allowedExpected : List String)
    (arguments : Lean.Json) : Bool :=
  match stringField? arguments "expected", stringField? arguments "actual" with
  | some expected, some actual =>
      allowedExpected.contains expected && actual != expected &&
        arguments == .mkObj [("expected", expected), ("actual", actual)]
  | _, _ => false

private def validProfileArguments (arguments : Lean.Json) : Bool :=
  match stringField? arguments "expectedId",
      stringField? arguments "expectedDigest",
      stringField? arguments "actualId",
      stringField? arguments "actualDigest" with
  | some expectedId, some expectedDigest, some actualId, some actualDigest =>
      let expected := ProfileRef.canonical
      expectedId == expected.id && expectedDigest == expected.digest &&
        (actualId != expectedId || actualDigest != expectedDigest) &&
        arguments == .mkObj [
          ("expectedId", expectedId), ("expectedDigest", expectedDigest),
          ("actualId", actualId), ("actualDigest", actualDigest)]
  | _, _, _, _ => false

private def validTagArguments (arguments : Lean.Json) : Bool :=
  exactTwo "actual" (fun _ => true) "expected" (fun _ => true) arguments

private def validReasonArguments
    (allowed : List String)
    (arguments : Lean.Json) : Bool :=
  exactOne "reason" (fun value =>
    match stringValue? value with
    | some reason => allowed.contains reason
    | none => false) arguments

private def validRequestIdArguments (arguments : Lean.Json) : Bool :=
  exactOne "constraint" (isLiteral "nonempty-utf8") arguments

private def validLimitArguments (arguments : Lean.Json) : Bool :=
  exactTwo "field" (isLiteral "calldataBytes")
    "constraint" (isLiteral "strictly-less-than-2^256") arguments

private def validCoreTypeArguments (arguments : Lean.Json) : Bool :=
  match stringField? arguments "actual", field? arguments "allowed" with
  | some actual, some allowed =>
      arguments == .mkObj [("actual", actual), ("allowed", allowed)] &&
        ((allowed == .arr #["unit", "bool", "word"] &&
            !["unit", "bool", "word"].contains actual) ||
          (allowed == .arr #["string", "object"] &&
            ["null", "boolean", "number", "array"].contains actual))
  | _, _ => false

private def validOracleArguments
    (code : String)
    (path : String)
    (arguments : Lean.Json) : Bool :=
  match code with
  | "oracle.wire.expected-object" => validExpectedArguments "object" arguments
  | "oracle.wire.expected-array" => validExpectedArguments "array" arguments
  | "oracle.wire.expected-string" => validExpectedArguments "string" arguments
  | "oracle.wire.expected-bool" => validExpectedArguments "boolean" arguments
  | "oracle.wire.expected-natural" => validExpectedArguments "number" arguments
  | "oracle.wire.missing-field"
  | "oracle.wire.unknown-field" => validFieldArguments path arguments
  | "oracle.wire.invalid-schema" =>
      pointerEndsWithField path "schema" && validIdentityArguments [
        schemaVersion, capabilitiesSchema, checkResultSchema,
        executionSchema, stateObservationSchema] arguments
  | "oracle.wire.invalid-spec" =>
      pointerEndsWithField path "spec" &&
        validIdentityArguments [Solcore.m3aLanguage.id] arguments
  | "oracle.wire.invalid-profile" =>
      path == "/profile" && validProfileArguments arguments
  | "oracle.wire.invalid-tag" => validTagArguments arguments
  | "oracle.wire.invalid-word" =>
      validReasonArguments ["prefix", "length", "lowercase-hex"] arguments
  | "oracle.wire.invalid-address" =>
      validReasonArguments ["prefix", "length", "lowercase-hex"] arguments
  | "oracle.wire.invalid-bytes" =>
      validReasonArguments
        ["prefix", "odd-length", "lowercase-hex"] arguments
  | "oracle.wire.invalid-request-id" =>
      path == "/id" && validRequestIdArguments arguments
  | "oracle.wire.invalid-limit" =>
      path == "/limits/calldataBytes" && validLimitArguments arguments
  | _ => false

private def validCoreArguments
    (code : String)
    (path : String)
    (arguments : Lean.Json) : Bool :=
  match code with
  | "core.wire.expected-object" => validExpectedArguments "object" arguments
  | "core.wire.expected-array" => validExpectedArguments "array" arguments
  | "core.wire.expected-string" => validExpectedArguments "string" arguments
  | "core.wire.expected-bool" => validExpectedArguments "boolean" arguments
  | "core.wire.expected-natural" => validExpectedArguments "number" arguments
  | "core.wire.missing-field"
  | "core.wire.unknown-field" => validFieldArguments path arguments
  | "core.wire.invalid-schema" =>
      pointerEndsWithField path "schema" &&
        validIdentityArguments [Solcore.Core.Wire.V3.schemaVersion] arguments
  | "core.wire.invalid-tag" => validTagArguments arguments
  | "core.wire.invalid-type" => validCoreTypeArguments arguments
  | "core.wire.invalid-word" =>
      validReasonArguments ["prefix", "length", "lowercase-hex"] arguments
  | _ => false

private def validPointerTail : List Char → Bool
  | [] => true
  | ['~'] => false
  | '~' :: escape :: rest =>
      (escape == '0' || escape == '1') && validPointerTail rest
  | _ :: rest => validPointerTail rest

/-- RFC 6901 syntax, including the empty pointer denoting the root. -/
def canonicalPointer (path : String) : Bool :=
  match path.toList with
  | [] => true
  | '/' :: rest => validPointerTail rest
  | _ => false

private def isValidTyped (error : ProtocolError) : Bool :=
  canonicalPointer error.path &&
    ((error.display == "invalid Oracle v5 value" &&
        validOracleArguments error.code error.path error.arguments) ||
      (error.display == "invalid Semantic Core v3 program" &&
        validCoreArguments error.code error.path error.arguments))

/-- Full closed validity of one raw protocol-error value. -/
def isValid (error : ProtocolError) : Bool :=
  if error.code == "malformed-json" then
    error.id.isNone && error.path == "" &&
      (match error.arguments with | .null => true | _ => false)
  else
    isValidTyped error

def Valid (error : ProtocolError) : Prop :=
  error.isValid = true

end ProtocolError

/-- A protocol error whose complete public shape belongs to the v5 catalog. -/
structure ValidProtocolError where
  private mk ::
  value : ProtocolError
  valid : value.Valid

namespace ValidProtocolError

instance : BEq ValidProtocolError :=
  ⟨fun left right => left.value == right.value⟩

/-- Admit a raw value only after checking the complete public catalog. -/
def of? (value : ProtocolError) : Option ValidProtocolError :=
  if valid : value.isValid = true then some (.mk value valid) else none

private def fallbackRaw (id : Option RequestId) : ProtocolError := {
  id
  code := "oracle.wire.invalid-tag"
  path := ""
  arguments := .mkObj [
    ("actual", .null),
    ("expected", .mkObj [("constraint", "valid-protocol-error")])
  ]
  display := "invalid Oracle v5 value"
}

private theorem fallbackRaw_valid (id : Option RequestId) :
    (fallbackRaw id).Valid := by
  simp [ProtocolError.Valid, ProtocolError.isValid, ProtocolError.isValidTyped,
    fallbackRaw, ProtocolError.canonicalPointer,
    ProtocolError.validOracleArguments,
    ProtocolError.validTagArguments, Diagnostic.Catalog.exactTwo,
    Diagnostic.Catalog.field?]
  native_decide

/--
Seal an internal producer result without adding a failure channel. A violated
producer invariant becomes one fixed, valid Oracle-owned invalid-tag error.
-/
def fromRaw (value : ProtocolError) : ValidProtocolError :=
  if valid : value.isValid = true then
    .mk value valid
  else
    .mk (fallbackRaw value.id) (fallbackRaw_valid value.id)

private def malformedRaw (message : String) : ProtocolError := {
  code := "malformed-json"
  display := message
}

private theorem malformedRaw_valid (message : String) :
    (malformedRaw message).Valid := by
  simp [ProtocolError.Valid, ProtocolError.isValid, malformedRaw]

/-- The sole constructor for strict-parser failures. -/
def malformedJson (message : String) : ValidProtocolError :=
  .mk (malformedRaw message) (malformedRaw_valid message)

def id (error : ValidProtocolError) : Option RequestId := error.value.id

def code (error : ValidProtocolError) : String := error.value.code

def path (error : ValidProtocolError) : String := error.value.path

def arguments (error : ValidProtocolError) : Lean.Json := error.value.arguments

def display (error : ValidProtocolError) : String := error.value.display

def kind (_error : ValidProtocolError) : String := "protocolError"

def schema (_error : ValidProtocolError) : String := schemaVersion

end ValidProtocolError

end Solcore.Oracle.V5
