import Lean.Data.Json
import Solcore.Core.Syntax

set_option autoImplicit false

namespace Solcore.Core.Wire

def schemaVersion : String := "solcore-semantic-core/v1"

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
  path.segments.foldl (fun result segment => result ++ "/" ++ segmentToken segment) ""

end DecodePath

inductive DecodeErrorCode where
  | expectedObject
  | expectedString
  | expectedBool
  | expectedNatural
  | missingField
  | unknownField
  | invalidSchema
  | invalidTag
  | invalidType
  | invalidWord
  | depthLimitExceeded
  | nodeLimitExceeded
  deriving Repr, BEq, DecidableEq

namespace DecodeErrorCode

def wireName : DecodeErrorCode → String
  | .expectedObject => "expected-object"
  | .expectedString => "expected-string"
  | .expectedBool => "expected-bool"
  | .expectedNatural => "expected-natural"
  | .missingField => "missing-field"
  | .unknownField => "unknown-field"
  | .invalidSchema => "invalid-schema"
  | .invalidTag => "invalid-tag"
  | .invalidType => "invalid-type"
  | .invalidWord => "invalid-word"
  | .depthLimitExceeded => "depth-limit-exceeded"
  | .nodeLimitExceeded => "node-limit-exceeded"

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

structure DecodeLimits where
  maxDepth : Nat
  maxNodes : Nat
  deriving Repr, BEq, DecidableEq

def DecodeLimits.default : DecodeLimits := {
  maxDepth := 1024
  maxNodes := 1000000
}

abbrev DecodeResult (α : Type) := Except DecodeError α

private def failAt {α : Type}
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

private def expectedArguments (expected : String) (actual : Lean.Json) : Lean.Json :=
  .mkObj [
    ("expected", expected),
    ("actual", jsonKind actual)
  ]

private def ensureExactObject
    (path : DecodePath)
    (json : Lean.Json)
    (allowed required : List String) :
    DecodeResult Unit := do
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

private def requireField
    (path : DecodePath)
    (json : Lean.Json)
    (name : String) :
    DecodeResult Lean.Json :=
  match json with
  | .obj _ =>
      match json.getObjVal? name with
      | .ok value => pure value
      | .error _ => failAt (path.field name) .missingField (.mkObj [("field", name)])
  | _ => failAt path .expectedObject (expectedArguments "object" json)

private def decodeStringAt (path : DecodePath) (json : Lean.Json) : DecodeResult String :=
  match json with
  | .str value => pure value
  | _ => failAt path .expectedString (expectedArguments "string" json)

private def decodeBoolAt (path : DecodePath) (json : Lean.Json) : DecodeResult Bool :=
  match json with
  | .bool value => pure value
  | _ => failAt path .expectedBool (expectedArguments "boolean" json)

private def decodeNatAt (path : DecodePath) (json : Lean.Json) : DecodeResult Nat :=
  match json.getNat? with
  | .ok value => pure value
  | .error _ => failAt path .expectedNatural (expectedArguments "natural" json)

def encodeType : Ty → Lean.Json
  | .unit => "unit"
  | .bool => "bool"
  | .word => "word"

def decodeTypeAt (path : DecodePath) (json : Lean.Json) : DecodeResult Ty := do
  let name ← decodeStringAt path json
  match name with
  | "unit" => pure .unit
  | "bool" => pure .bool
  | "word" => pure .word
  | _ =>
      failAt path .invalidType (.mkObj [
        ("actual", name),
        ("allowed", .arr #["unit", "bool", "word"])
      ])

def decodeType (json : Lean.Json) : DecodeResult Ty :=
  decodeTypeAt .root json

@[simp] theorem decodeType_encodeType (type : Ty) :
    decodeType (encodeType type) = .ok type := by
  cases type <;> rfl

private def paddedHexDigits (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

def encodeWordText (value : Word) : String :=
  "0x" ++ paddedHexDigits value.val

private def hexDigitValue? : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | 'a' => some 10
  | 'b' => some 11
  | 'c' => some 12
  | 'd' => some 13
  | 'e' => some 14
  | 'f' => some 15
  | _ => none

private def parseHexDigits : List Char → Nat → Option Nat
  | [], result => some result
  | digit :: rest, result =>
      match hexDigitValue? digit with
      | some value => parseHexDigits rest (result * 16 + value)
      | none => none

def decodeWordTextAt (path : DecodePath) (text : String) : DecodeResult Word :=
  match text.toList with
  | '0' :: 'x' :: digits =>
      if digits.length != 64 then
        failAt path .invalidWord (.mkObj [
          ("reason", "length"),
          ("expectedHexDigits", 64),
          ("actualHexDigits", digits.length)
        ])
      else
        match parseHexDigits digits 0 with
        | none =>
            failAt path .invalidWord (.mkObj [("reason", "lowercase-hex")])
        | some value =>
            match Word.ofNat? value with
            | some word => pure word
            | none => failAt path .invalidWord (.mkObj [("reason", "range")])
  | _ => failAt path .invalidWord (.mkObj [("reason", "prefix")])

def decodeWordText (text : String) : DecodeResult Word :=
  decodeWordTextAt .root text

def encodeWord (value : Word) : Lean.Json :=
  encodeWordText value

def decodeWordAt (path : DecodePath) (json : Lean.Json) : DecodeResult Word := do
  decodeWordTextAt path (← decodeStringAt path json)

def decodeWord (json : Lean.Json) : DecodeResult Word :=
  decodeWordAt .root json

def encodeExpr : Expr → Lean.Json
  | .unit =>
      .mkObj [("tag", "unit")]
  | .bool value =>
      .mkObj [
        ("tag", "bool"),
        ("value", value)
      ]
  | .word value =>
      .mkObj [
        ("tag", "word"),
        ("value", encodeWord value)
      ]
  | .var index =>
      .mkObj [
        ("tag", "var"),
        ("index", index)
      ]
  | .letE initializer body =>
      .mkObj [
        ("tag", "let"),
        ("initializer", encodeExpr initializer),
        ("body", encodeExpr body)
      ]
  | .ifE condition thenBranch elseBranch =>
      .mkObj [
        ("tag", "if"),
        ("condition", encodeExpr condition),
        ("thenBranch", encodeExpr thenBranch),
        ("elseBranch", encodeExpr elseBranch)
      ]

private def decodeExprAt
    (limits : DecodeLimits) :
    Nat → Nat → DecodePath → Lean.Json → DecodeResult (Expr × Nat)
  | 0, _, path, _ =>
      failAt path .depthLimitExceeded (.mkObj [("limit", limits.maxDepth)])
  | _ + 1, 0, path, _ =>
      failAt path .nodeLimitExceeded (.mkObj [("limit", limits.maxNodes)])
  | depth + 1, nodes + 1, path, json => do
      ensureExactObject path json
        ["tag", "value", "index", "initializer", "body",
          "condition", "thenBranch", "elseBranch"]
        ["tag"]
      let tagPath := path.field "tag"
      let tag ← decodeStringAt tagPath (← requireField path json "tag")
      match tag with
      | "unit" =>
          ensureExactObject path json ["tag"] ["tag"]
          pure (.unit, nodes)
      | "bool" =>
          ensureExactObject path json ["tag", "value"] ["tag", "value"]
          let valuePath := path.field "value"
          let value ← decodeBoolAt valuePath (← requireField path json "value")
          pure (.bool value, nodes)
      | "word" =>
          ensureExactObject path json ["tag", "value"] ["tag", "value"]
          let valuePath := path.field "value"
          let value ← decodeWordAt valuePath (← requireField path json "value")
          pure (.word value, nodes)
      | "var" =>
          ensureExactObject path json ["tag", "index"] ["tag", "index"]
          let indexPath := path.field "index"
          let index ← decodeNatAt indexPath (← requireField path json "index")
          pure (.var index, nodes)
      | "let" =>
          ensureExactObject path json
            ["tag", "initializer", "body"] ["tag", "initializer", "body"]
          let initializerPath := path.field "initializer"
          let (initializer, afterInitializer) ←
            decodeExprAt limits depth nodes initializerPath
              (← requireField path json "initializer")
          let bodyPath := path.field "body"
          let (body, afterBody) ←
            decodeExprAt limits depth afterInitializer bodyPath
              (← requireField path json "body")
          pure (.letE initializer body, afterBody)
      | "if" =>
          ensureExactObject path json
            ["tag", "condition", "thenBranch", "elseBranch"]
            ["tag", "condition", "thenBranch", "elseBranch"]
          let conditionPath := path.field "condition"
          let (condition, afterCondition) ←
            decodeExprAt limits depth nodes conditionPath
              (← requireField path json "condition")
          let thenPath := path.field "thenBranch"
          let (thenBranch, afterThen) ←
            decodeExprAt limits depth afterCondition thenPath
              (← requireField path json "thenBranch")
          let elsePath := path.field "elseBranch"
          let (elseBranch, afterElse) ←
            decodeExprAt limits depth afterThen elsePath
              (← requireField path json "elseBranch")
          pure (.ifE condition thenBranch elseBranch, afterElse)
      | _ =>
          failAt tagPath .invalidTag (.mkObj [
            ("actual", tag),
            ("allowed", .arr #["unit", "bool", "word", "var", "let", "if"])
          ])

def decodeExprWith (limits : DecodeLimits) (json : Lean.Json) : DecodeResult Expr := do
  let (expr, _) ←
    decodeExprAt limits limits.maxDepth limits.maxNodes .root json
  pure expr

def decodeExpr (json : Lean.Json) : DecodeResult Expr :=
  decodeExprWith DecodeLimits.default json

@[simp] theorem decodeExpr_encodeUnit :
    decodeExpr (encodeExpr .unit) = .ok .unit := by
  rfl

@[simp] theorem decodeExpr_encodeBool (value : Bool) :
    decodeExpr (encodeExpr (.bool value)) = .ok (.bool value) := by
  cases value <;> rfl

@[simp] theorem decodeExpr_encodeVar (index : Nat) :
    decodeExpr (encodeExpr (.var index)) = .ok (.var index) := by
  rfl

def encodeValue : Value → Lean.Json
  | .unit =>
      .mkObj [("tag", "unit")]
  | .bool value =>
      .mkObj [
        ("tag", "bool"),
        ("value", value)
      ]
  | .word value =>
      .mkObj [
        ("tag", "word"),
        ("value", encodeWord value)
      ]

def decodeValueAt (path : DecodePath) (json : Lean.Json) : DecodeResult Value := do
  ensureExactObject path json ["tag", "value"] ["tag"]
  let tagPath := path.field "tag"
  let tag ← decodeStringAt tagPath (← requireField path json "tag")
  match tag with
  | "unit" =>
      ensureExactObject path json ["tag"] ["tag"]
      pure .unit
  | "bool" =>
      ensureExactObject path json ["tag", "value"] ["tag", "value"]
      let valuePath := path.field "value"
      pure (.bool (← decodeBoolAt valuePath (← requireField path json "value")))
  | "word" =>
      ensureExactObject path json ["tag", "value"] ["tag", "value"]
      let valuePath := path.field "value"
      pure (.word (← decodeWordAt valuePath (← requireField path json "value")))
  | _ =>
      failAt tagPath .invalidTag (.mkObj [
        ("actual", tag),
        ("allowed", .arr #["unit", "bool", "word"])
      ])

def decodeValue (json : Lean.Json) : DecodeResult Value :=
  decodeValueAt .root json

@[simp] theorem decodeValue_encodeUnit :
    decodeValue (encodeValue .unit) = .ok .unit := by
  rfl

@[simp] theorem decodeValue_encodeBool (value : Bool) :
    decodeValue (encodeValue (.bool value)) = .ok (.bool value) := by
  cases value <;> rfl

def encodeProgram (program : Program) : Lean.Json :=
  .mkObj [
    ("schema", schemaVersion),
    ("resultType", encodeType program.resultType),
    ("body", encodeExpr program.body)
  ]

def decodeProgramWith
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult Program := do
  ensureExactObject .root json
    ["schema", "resultType", "body"] ["schema", "resultType", "body"]
  let schemaPath := DecodePath.root.field "schema"
  let actualSchema ← decodeStringAt schemaPath (← requireField .root json "schema")
  unless actualSchema == schemaVersion do
    failAt schemaPath .invalidSchema (.mkObj [
      ("expected", schemaVersion),
      ("actual", actualSchema)
    ])
  let resultTypePath := DecodePath.root.field "resultType"
  let resultType ← decodeTypeAt resultTypePath (← requireField .root json "resultType")
  let bodyPath := DecodePath.root.field "body"
  let (body, _) ←
    decodeExprAt limits limits.maxDepth limits.maxNodes bodyPath
      (← requireField .root json "body")
  pure { resultType, body }

def decodeProgram (json : Lean.Json) : DecodeResult Program :=
  decodeProgramWith DecodeLimits.default json

def canonicalizeProgramWith
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult Lean.Json :=
  encodeProgram <$> decodeProgramWith limits json

def canonicalizeProgram (json : Lean.Json) : DecodeResult Lean.Json :=
  canonicalizeProgramWith DecodeLimits.default json

end Solcore.Core.Wire
