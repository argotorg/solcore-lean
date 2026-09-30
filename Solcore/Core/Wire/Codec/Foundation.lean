import Lean.Data.Json
import Solcore.Util.Json

/-! Strict JSON-decoding primitives owned by Semantic Core Wire. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

inductive PathSegment where
  | field (name : String)
  | index (value : Nat)
  deriving Repr, BEq, DecidableEq

structure DecodePath where
  segments : Array PathSegment := #[]
  deriving Repr, BEq, DecidableEq

namespace DecodePath

def root : DecodePath := {}

def field (path : DecodePath) (name : String) : DecodePath :=
  { segments := path.segments.push (.field name) }

def index (path : DecodePath) (value : Nat) : DecodePath :=
  { segments := path.segments.push (.index value) }

private def escapeToken (value : String) : String :=
  (value.replace "~" "~0").replace "/" "~1"

private def segmentToken : PathSegment → String
  | .field name => escapeToken name
  | .index value => toString value

def toPointer (path : DecodePath) : String :=
  path.segments.foldl
    (fun result segment => result ++ "/" ++ segmentToken segment) ""

end DecodePath

inductive DecodeErrorCode where
  | expectedObject
  | expectedArray
  | expectedString
  | expectedBool
  | expectedNatural
  | missingField
  | unknownField
  | invalidSchema
  | invalidTag
  | invalidType
  | invalidWord
  | invalidInteger
  deriving Repr, BEq, DecidableEq

namespace DecodeErrorCode

def wireName : DecodeErrorCode → String
  | .expectedObject => "expected-object"
  | .expectedArray => "expected-array"
  | .expectedString => "expected-string"
  | .expectedBool => "expected-bool"
  | .expectedNatural => "expected-natural"
  | .missingField => "missing-field"
  | .unknownField => "unknown-field"
  | .invalidSchema => "invalid-schema"
  | .invalidTag => "invalid-tag"
  | .invalidType => "invalid-type"
  | .invalidWord => "invalid-word"
  | .invalidInteger => "invalid-integer"

end DecodeErrorCode

structure DecodeError where
  path : DecodePath
  code : DecodeErrorCode
  arguments : Lean.Json := .null

namespace DecodeError

def toJson (error : DecodeError) : Lean.Json :=
  .mkObj [
    ("path", error.path.toPointer),
    ("code", error.code.wireName),
    ("arguments", error.arguments)
  ]

end DecodeError

instance : Lean.ToJson DecodeError := ⟨DecodeError.toJson⟩

abbrev DecodeResult (α : Type) := Except DecodeError α

def failAt {α : Type}
    (path : DecodePath)
    (code : DecodeErrorCode)
    (arguments : Lean.Json := .null) :
    DecodeResult α :=
  .error { path, code, arguments }

private def jsonKind : Lean.Json → String
  | .null => "null"
  | .bool _ => "boolean"
  | .num _ => "number"
  | .str _ => "string"
  | .arr _ => "array"
  | .obj _ => "object"

private def expectedArguments
    (expected : String)
    (actual : Lean.Json) :
    Lean.Json :=
  .mkObj [
    ("expected", expected),
    ("actual", jsonKind actual)
  ]

private def lexicographicMinimum? : List String → Option String
  | [] => none
  | first :: rest =>
      some <| rest.foldl (fun current candidate =>
        if (compare candidate current).isLE then candidate else current) first

/-- Accept an object only when its key set is exactly the expected one. -/
def ensureExactObject
    (path : DecodePath)
    (json : Lean.Json)
    (allowed required : List String) :
    DecodeResult Unit := do
  let fields ←
    match json with
    | .obj fields => pure fields
    | _ => failAt path .expectedObject (expectedArguments "object" json)
  let unknown? := lexicographicMinimum? <|
    fields.keys.filter (fun key => !allowed.contains key)
  let missing? := lexicographicMinimum? <|
    required.filter (fun key => !fields.contains key)
  match unknown?, missing? with
  | none, none => pure ()
  | some key, none =>
      failAt (path.field key) .unknownField (.mkObj [("field", key)])
  | none, some key =>
      failAt (path.field key) .missingField (.mkObj [("field", key)])
  | some unknown, some missing =>
      if (compare unknown missing).isLE then
        failAt (path.field unknown) .unknownField (.mkObj [("field", unknown)])
      else
        failAt (path.field missing) .missingField (.mkObj [("field", missing)])

def requireField
    (path : DecodePath)
    (json : Lean.Json)
    (name : String) :
    DecodeResult Lean.Json :=
  match json with
  | .obj _ =>
      match json.getObjVal? name with
      | .ok value => pure value
      | .error _ =>
          failAt (path.field name) .missingField (.mkObj [("field", name)])
  | _ => failAt path .expectedObject (expectedArguments "object" json)

def decodeStringAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult String :=
  match json with
  | .str value => pure value
  | _ => failAt path .expectedString (expectedArguments "string" json)

def decodeBoolAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Bool :=
  match json with
  | .bool value => pure value
  | _ => failAt path .expectedBool (expectedArguments "boolean" json)

def decodeNatAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Nat :=
  match Util.jsonNatural? json with
  | some value => pure value
  | none => failAt path .expectedNatural (expectedArguments "number" json)

def decodeListAt {α : Type}
    (decodeValue : DecodePath → Lean.Json → DecodeResult α)
    (path : DecodePath) :
    Nat → List Lean.Json → DecodeResult (List α)
  | _, [] => pure []
  | index, json :: rest => do
      let value ← decodeValue (path.index index) json
      let values ← decodeListAt decodeValue path (index + 1) rest
      pure (value :: values)

def decodeArrayAt {α : Type}
    (decodeValue : DecodePath → Lean.Json → DecodeResult α)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (List α) :=
  match json with
  | .arr values => decodeListAt decodeValue path 0 values.toList
  | _ => failAt path .expectedArray (expectedArguments "array" json)

end Solcore.Core.Wire
