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

private def exactFour
    (firstName : String)
    (firstValid : Lean.Json → Bool)
    (secondName : String)
    (secondValid : Lean.Json → Bool)
    (thirdName : String)
    (thirdValid : Lean.Json → Bool)
    (fourthName : String)
    (fourthValid : Lean.Json → Bool)
    (json : Lean.Json) : Bool :=
  match field? json firstName, field? json secondName,
      field? json thirdName, field? json fourthName with
  | some first, some second, some third, some fourth =>
      firstValid first && secondValid second && thirdValid third &&
        fourthValid fourth && json == .mkObj [
          (firstName, first), (secondName, second), (thirdName, third),
          (fourthName, fourth)]
  | _, _, _, _ => false

private def validExpectedArguments
    (expected : String)
    (arguments : Lean.Json) : Bool :=
  exactTwo "expected" (isLiteral expected) "actual" isJsonKind arguments

private def validFieldArguments (arguments : Lean.Json) : Bool :=
  exactOne "field" isString arguments

private def validIdentityArguments (arguments : Lean.Json) : Bool :=
  exactTwo "expected" isString "actual" isString arguments

private def validProfileArguments (arguments : Lean.Json) : Bool :=
  exactFour "expectedId" isString "expectedDigest" isString
    "actualId" isString "actualDigest" isString arguments

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
        (allowed == .arr #["unit", "bool", "word"] ||
          allowed == .arr #["string", "object"])
  | _, _ => false

private def validOracleArguments
    (code : String)
    (arguments : Lean.Json) : Bool :=
  match code with
  | "oracle.wire.expected-object" => validExpectedArguments "object" arguments
  | "oracle.wire.expected-array" => validExpectedArguments "array" arguments
  | "oracle.wire.expected-string" => validExpectedArguments "string" arguments
  | "oracle.wire.expected-bool" => validExpectedArguments "boolean" arguments
  | "oracle.wire.expected-natural" => validExpectedArguments "number" arguments
  | "oracle.wire.missing-field"
  | "oracle.wire.unknown-field" => validFieldArguments arguments
  | "oracle.wire.invalid-schema"
  | "oracle.wire.invalid-spec" => validIdentityArguments arguments
  | "oracle.wire.invalid-profile" => validProfileArguments arguments
  | "oracle.wire.invalid-tag" => validTagArguments arguments
  | "oracle.wire.invalid-word" =>
      validReasonArguments ["prefix", "length", "lowercase-hex"] arguments
  | "oracle.wire.invalid-address" =>
      validReasonArguments ["prefix", "length", "lowercase-hex"] arguments
  | "oracle.wire.invalid-bytes" =>
      validReasonArguments
        ["prefix", "odd-length", "lowercase-hex"] arguments
  | "oracle.wire.invalid-request-id" => validRequestIdArguments arguments
  | "oracle.wire.invalid-limit" => validLimitArguments arguments
  | _ => false

private def validCoreArguments
    (code : String)
    (arguments : Lean.Json) : Bool :=
  match code with
  | "core.wire.expected-object" => validExpectedArguments "object" arguments
  | "core.wire.expected-array" => validExpectedArguments "array" arguments
  | "core.wire.expected-string" => validExpectedArguments "string" arguments
  | "core.wire.expected-bool" => validExpectedArguments "boolean" arguments
  | "core.wire.expected-natural" => validExpectedArguments "number" arguments
  | "core.wire.missing-field"
  | "core.wire.unknown-field" => validFieldArguments arguments
  | "core.wire.invalid-schema" => validIdentityArguments arguments
  | "core.wire.invalid-tag" => validTagArguments arguments
  | "core.wire.invalid-type" => validCoreTypeArguments arguments
  | "core.wire.invalid-word" =>
      validReasonArguments ["prefix", "length", "lowercase-hex"] arguments
  | _ => false

private def validPointerTail : List Char → Bool
  | [] => true
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
        validOracleArguments error.code error.arguments) ||
      (error.display == "invalid Semantic Core v3 program" &&
        validCoreArguments error.code error.arguments))

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
