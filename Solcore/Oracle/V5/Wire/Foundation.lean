import Lean.Data.Json
import Solcore.Core.Wire.V3.Codec.Foundation
import Solcore.Foundation.Json

/-! Strict structural JSON primitives owned by the Oracle v5 wire. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

abbrev Path := Solcore.Core.Wire.V3.DecodePath

namespace Path

def root : Path := Solcore.Core.Wire.V3.DecodePath.root

def field (path : Path) (name : String) : Path :=
  Solcore.Core.Wire.V3.DecodePath.field path name

def index (path : Path) (value : Nat) : Path :=
  Solcore.Core.Wire.V3.DecodePath.index path value

def toPointer (path : Path) : String :=
  Solcore.Core.Wire.V3.DecodePath.toPointer path

end Path

/-- Closed typed-decoder suffixes owned by the Oracle v5 boundary. -/
inductive DecodeErrorCode where
  | expectedObject
  | expectedArray
  | expectedString
  | expectedBool
  | expectedNatural
  | missingField
  | unknownField
  | invalidSchema
  | invalidSpec
  | invalidProfile
  | invalidTag
  | invalidWord
  | invalidAddress
  | invalidBytes
  | invalidRequestId
  | invalidLimit
  deriving Repr, BEq, DecidableEq

namespace DecodeErrorCode

def suffix : DecodeErrorCode → String
  | .expectedObject => "expected-object"
  | .expectedArray => "expected-array"
  | .expectedString => "expected-string"
  | .expectedBool => "expected-bool"
  | .expectedNatural => "expected-natural"
  | .missingField => "missing-field"
  | .unknownField => "unknown-field"
  | .invalidSchema => "invalid-schema"
  | .invalidSpec => "invalid-spec"
  | .invalidProfile => "invalid-profile"
  | .invalidTag => "invalid-tag"
  | .invalidWord => "invalid-word"
  | .invalidAddress => "invalid-address"
  | .invalidBytes => "invalid-bytes"
  | .invalidRequestId => "invalid-request-id"
  | .invalidLimit => "invalid-limit"

def wireName (code : DecodeErrorCode) : String :=
  "oracle.wire." ++ code.suffix

end DecodeErrorCode

/-- Protocol failures preserve whether Oracle or embedded Core owns the path. -/
inductive ProtocolError where
  | oracle
      (path : Path)
      (code : DecodeErrorCode)
      (arguments : Lean.Json := .null)
  | core (error : Solcore.Core.Wire.V3.DecodeError)

namespace ProtocolError

def path : ProtocolError → Path
  | .oracle path _ _ => path
  | .core error => error.path

def code : ProtocolError → String
  | .oracle _ code _ => code.wireName
  | .core error => "core.wire." ++ error.code.wireName

def arguments : ProtocolError → Lean.Json
  | .oracle _ _ arguments => arguments
  | .core error => error.arguments

def display : ProtocolError → String
  | .oracle .. => "invalid Oracle v5 value"
  | .core .. => "invalid Semantic Core v3 program"

def toJson (error : ProtocolError) : Lean.Json :=
  .mkObj [
    ("code", error.code),
    ("path", error.path.toPointer),
    ("arguments", error.arguments),
    ("display", error.display)
  ]

end ProtocolError

instance : Lean.ToJson ProtocolError := ⟨ProtocolError.toJson⟩

abbrev DecodeResult (α : Type) := Except ProtocolError α

def failAt {α : Type}
    (path : Path)
    (code : DecodeErrorCode)
    (arguments : Lean.Json := .null) : DecodeResult α :=
  .error (.oracle path code arguments)

def liftCoreProtocol {α : Type}
    (result : Solcore.Core.Wire.V3.DecodeResult α) : DecodeResult α :=
  result.mapError .core

def jsonKind : Lean.Json → String
  | .null => "null"
  | .bool _ => "boolean"
  | .num _ => "number"
  | .str _ => "string"
  | .arr _ => "array"
  | .obj _ => "object"

def expectedArguments
    (expected : String)
    (actual : Lean.Json) : Lean.Json :=
  .mkObj [
    ("expected", expected),
    ("actual", jsonKind actual)
  ]

/-- Accept an object only when its fields are exactly the published set. -/
def ensureExactObject
    (path : Path)
    (json : Lean.Json)
    (allowed required : List String) : DecodeResult Unit := do
  let fields ←
    match json with
    | .obj fields => pure fields
    | _ => failAt path .expectedObject (expectedArguments "object" json)
  match fields.keys.find? (fun key => !allowed.contains key) with
  | some key =>
      failAt (path.field key) .unknownField (.mkObj [("field", key)])
  | none =>
      match required.find? (fun key => !fields.contains key) with
      | some key =>
          failAt (path.field key) .missingField (.mkObj [("field", key)])
      | none => pure ()

def requireField
    (path : Path)
    (json : Lean.Json)
    (name : String) : DecodeResult Lean.Json :=
  match json with
  | .obj _ =>
      match json.getObjVal? name with
      | .ok value => pure value
      | .error _ =>
          failAt (path.field name) .missingField (.mkObj [("field", name)])
  | _ => failAt path .expectedObject (expectedArguments "object" json)

def decodeStringAt
    (path : Path)
    (json : Lean.Json) : DecodeResult String :=
  match json with
  | .str value => pure value
  | _ => failAt path .expectedString (expectedArguments "string" json)

def decodeBoolAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Bool :=
  match json with
  | .bool value => pure value
  | _ => failAt path .expectedBool (expectedArguments "boolean" json)

def decodeNatAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Nat :=
  match Solcore.Foundation.jsonNatural? json with
  | some value => pure value
  | none => failAt path .expectedNatural (expectedArguments "natural" json)

def invalidTagAt {α : Type}
    (path : Path)
    (actual expected : Lean.Json) : DecodeResult α :=
  failAt path .invalidTag (.mkObj [
    ("actual", actual),
    ("expected", expected)
  ])

def requireLiteralAt
    (path : Path)
    (json : Lean.Json)
    (expected : String) : DecodeResult Unit := do
  let actual ← decodeStringAt path json
  unless actual == expected do
    invalidTagAt path actual expected

def decodeListAt {α : Type}
    (decodeValue : Path → Lean.Json → DecodeResult α)
    (path : Path) :
    Nat → List Lean.Json → DecodeResult (List α)
  | _, [] => pure []
  | index, json :: rest => do
      let value ← decodeValue (path.index index) json
      let values ← decodeListAt decodeValue path (index + 1) rest
      pure (value :: values)

def decodeArrayAt {α : Type}
    (decodeValue : Path → Lean.Json → DecodeResult α)
    (path : Path)
    (json : Lean.Json) : DecodeResult (List α) :=
  match json with
  | .arr values => decodeListAt decodeValue path 0 values.toList
  | _ => failAt path .expectedArray (expectedArguments "array" json)

end Solcore.Oracle.V5.Wire
