import Lean.Data.Json
import Solcore.Core.Syntax
import Solcore.Foundation.Json

set_option autoImplicit false

namespace Solcore.Core.Wire.V2

/-!
The Semantic Core v2 wire language is deliberately independent of the evolving
internal Core syntax. Its closed expression and operator types keep the v2
encoder total without assigning v2 encodings to later constructors or
operations.
-/

inductive Ty where
  | unit
  | bool
  | word
  deriving Repr, BEq, DecidableEq

namespace Ty

def toCore : Ty → Solcore.Core.Ty
  | .unit => .unit
  | .bool => .bool
  | .word => .word

/-!
The fallback is intentionally unreachable for the current Core. Keeping it
makes this frozen projection reject future Core type constructors without
editing the v2 definition.
-/
set_option match.ignoreUnusedAlts true in
def ofCore? : Solcore.Core.Ty → Option Ty
  | .unit => some .unit
  | .bool => some .bool
  | .word => some .word
  | .product _ _ => none
  | _ => none

@[simp] theorem ofCore?_toCore (type : Ty) :
    ofCore? type.toCore = some type := by
  cases type <;> rfl

end Ty

inductive Value where
  | unit
  | bool (value : Bool)
  | word (value : Solcore.Core.Word)
  deriving Repr, BEq, DecidableEq

namespace Value

def type : Value → Ty
  | .unit => .unit
  | .bool _ => .bool
  | .word _ => .word

def toCore : Value → Solcore.Core.Value
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value

/-!
As with types, the final equation preserves v2 as a closed projection when the
internal Core gains value constructors.
-/
set_option match.ignoreUnusedAlts true in
def ofCore? : Solcore.Core.Value → Option Value
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .pair _ _ => none
  | _ => none

@[simp] theorem ofCore?_toCore (value : Value) :
    ofCore? value.toCore = some value := by
  cases value <;> rfl

@[simp] theorem toCore_type (value : Value) :
    value.toCore.type = value.type.toCore := by
  cases value <;> rfl

end Value

inductive UnaryOp where
  | boolNot
  | wordNot
  deriving Repr, BEq, DecidableEq

namespace UnaryOp

def toCore : UnaryOp → Solcore.Core.UnaryOp
  | .boolNot => .boolNot
  | .wordNot => .wordNot

set_option match.ignoreUnusedAlts true in
def ofCore? : Solcore.Core.UnaryOp → Option UnaryOp
  | .boolNot => some .boolNot
  | .wordNot => some .wordNot
  | _ => none

@[simp] theorem ofCore?_toCore (op : UnaryOp) :
    ofCore? op.toCore = some op := by
  cases op <;> rfl

end UnaryOp

inductive BinaryOp where
  | wordAdd
  | wordSub
  | wordMul
  | wordDiv
  | wordMod
  | wordEq
  | wordGt
  | wordAnd
  | wordOr
  | wordXor
  | wordShl
  | wordShr
  deriving Repr, BEq, DecidableEq

namespace BinaryOp

/-!
Binary operands retain Core evaluation order. In particular, `wordShl` and
`wordShr` take the value on the left and the shift amount on the right.
-/

def toCore : BinaryOp → Solcore.Core.BinaryOp
  | .wordAdd => .wordAdd
  | .wordSub => .wordSub
  | .wordMul => .wordMul
  | .wordDiv => .wordDiv
  | .wordMod => .wordMod
  | .wordEq => .wordEq
  | .wordGt => .wordGt
  | .wordAnd => .wordAnd
  | .wordOr => .wordOr
  | .wordXor => .wordXor
  | .wordShl => .wordShl
  | .wordShr => .wordShr

set_option match.ignoreUnusedAlts true in
def ofCore? : Solcore.Core.BinaryOp → Option BinaryOp
  | .wordAdd => some .wordAdd
  | .wordSub => some .wordSub
  | .wordMul => some .wordMul
  | .wordDiv => some .wordDiv
  | .wordMod => some .wordMod
  | .wordEq => some .wordEq
  | .wordGt => some .wordGt
  | .wordAnd => some .wordAnd
  | .wordOr => some .wordOr
  | .wordXor => some .wordXor
  | .wordShl => some .wordShl
  | .wordShr => some .wordShr
  | _ => none

@[simp] theorem ofCore?_toCore (op : BinaryOp) :
    ofCore? op.toCore = some op := by
  cases op <;> rfl

end BinaryOp

inductive Expr where
  | unit
  | bool (value : Bool)
  | word (value : Solcore.Core.Word)
  | var (index : Nat)
  | unary (op : UnaryOp) (operand : Expr)
  | binary (op : BinaryOp) (left : Expr) (right : Expr)
  | letE (initializer : Expr) (body : Expr)
  | ifE (condition : Expr) (thenBranch : Expr) (elseBranch : Expr)
  deriving Repr, BEq, DecidableEq

structure Program where
  resultType : Ty
  body : Expr
  deriving Repr, BEq, DecidableEq

namespace Expr

def toCore : Expr → Solcore.Core.Expr
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .var index => .var index
  | .unary op operand => .unary op.toCore operand.toCore
  | .binary op left right => .binary op.toCore left.toCore right.toCore
  | .letE initializer body => .letE initializer.toCore body.toCore
  | .ifE condition thenBranch elseBranch =>
      .ifE condition.toCore thenBranch.toCore elseBranch.toCore

set_option match.ignoreUnusedAlts true in
def ofCore? : Solcore.Core.Expr → Option Expr
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .var index => some (.var index)
  | .unary op operand => do
      let op ← UnaryOp.ofCore? op
      let operand ← ofCore? operand
      some (.unary op operand)
  | .binary op left right => do
      let op ← BinaryOp.ofCore? op
      let left ← ofCore? left
      let right ← ofCore? right
      some (.binary op left right)
  | .letE initializer body => do
      let initializer ← ofCore? initializer
      let body ← ofCore? body
      some (.letE initializer body)
  | .ifE condition thenBranch elseBranch => do
      let condition ← ofCore? condition
      let thenBranch ← ofCore? thenBranch
      let elseBranch ← ofCore? elseBranch
      some (.ifE condition thenBranch elseBranch)
  | .pair _ _ => none
  | .first _ => none
  | .second _ => none
  | _ => none

@[simp] theorem ofCore?_toCore (expr : Expr) :
    ofCore? expr.toCore = some expr := by
  induction expr with
  | unit | bool | word | var => rfl
  | unary op operand operandIH =>
      simp [toCore, ofCore?, UnaryOp.ofCore?_toCore, operandIH]
  | binary op left right leftIH rightIH =>
      simp [toCore, ofCore?, BinaryOp.ofCore?_toCore, leftIH, rightIH]
  | letE initializer body initializerIH bodyIH =>
      simp [toCore, ofCore?, initializerIH, bodyIH]
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      simp [toCore, ofCore?, conditionIH, thenIH, elseIH]

end Expr

namespace Program

def toCore (program : Program) : Solcore.Core.Program := {
  resultType := program.resultType.toCore
  body := program.body.toCore
}

def ofCore? (program : Solcore.Core.Program) : Option Program := do
  let resultType ← Ty.ofCore? program.resultType
  let body ← Expr.ofCore? program.body
  some {
    resultType
    body
  }

@[simp] theorem ofCore?_toCore (program : Program) :
    ofCore? program.toCore = some program := by
  cases program with
  | mk resultType body =>
      simp [toCore, ofCore?, Expr.ofCore?_toCore]

end Program

def schemaVersion : String := "solcore-semantic-core/v2"

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
  match Foundation.jsonNatural? json with
  | some value => pure value
  | none => failAt path .expectedNatural (expectedArguments "natural" json)

def encodeUnaryOp : UnaryOp → Lean.Json
  | .boolNot => "boolNot"
  | .wordNot => "wordNot"

def decodeUnaryOpAt (path : DecodePath) (json : Lean.Json) : DecodeResult UnaryOp := do
  let name ← decodeStringAt path json
  match name with
  | "boolNot" => pure .boolNot
  | "wordNot" => pure .wordNot
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", name),
        ("allowed", .arr #["boolNot", "wordNot"])
      ])

def decodeUnaryOp (json : Lean.Json) : DecodeResult UnaryOp :=
  decodeUnaryOpAt .root json

@[simp] theorem decodeUnaryOp_encodeUnaryOp (op : UnaryOp) :
    decodeUnaryOp (encodeUnaryOp op) = .ok op := by
  cases op <;> rfl

def encodeBinaryOp : BinaryOp → Lean.Json
  | .wordAdd => "wordAdd"
  | .wordSub => "wordSub"
  | .wordMul => "wordMul"
  | .wordDiv => "wordDiv"
  | .wordMod => "wordMod"
  | .wordEq => "wordEq"
  | .wordGt => "wordGt"
  | .wordAnd => "wordAnd"
  | .wordOr => "wordOr"
  | .wordXor => "wordXor"
  | .wordShl => "wordShl"
  | .wordShr => "wordShr"

def decodeBinaryOpAt (path : DecodePath) (json : Lean.Json) : DecodeResult BinaryOp := do
  let name ← decodeStringAt path json
  match name with
  | "wordAdd" => pure .wordAdd
  | "wordSub" => pure .wordSub
  | "wordMul" => pure .wordMul
  | "wordDiv" => pure .wordDiv
  | "wordMod" => pure .wordMod
  | "wordEq" => pure .wordEq
  | "wordGt" => pure .wordGt
  | "wordAnd" => pure .wordAnd
  | "wordOr" => pure .wordOr
  | "wordXor" => pure .wordXor
  | "wordShl" => pure .wordShl
  | "wordShr" => pure .wordShr
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", name),
        ("allowed", .arr #[
          "wordAdd",
          "wordSub",
          "wordMul",
          "wordDiv",
          "wordMod",
          "wordEq",
          "wordGt",
          "wordAnd",
          "wordOr",
          "wordXor",
          "wordShl",
          "wordShr"
        ])
      ])

def decodeBinaryOp (json : Lean.Json) : DecodeResult BinaryOp :=
  decodeBinaryOpAt .root json

@[simp] theorem decodeBinaryOp_encodeBinaryOp (op : BinaryOp) :
    decodeBinaryOp (encodeBinaryOp op) = .ok op := by
  cases op <;> rfl

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

private def encodeHexDigits : Nat → Nat → List Char
  | 0, _ => []
  | width + 1, value =>
      Nat.digitChar (value / 16 ^ width) ::
        encodeHexDigits width (value % 16 ^ width)

private theorem encodeHexDigits_length (width value : Nat) :
    (encodeHexDigits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [encodeHexDigits, ih]

def encodeWordText (value : Word) : String :=
  "0x" ++ String.ofList (encodeHexDigits 64 value.val)

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

private theorem hexDigitValue_digitChar
    (value : Nat)
    (inRange : value < 16) :
    hexDigitValue? (Nat.digitChar value) = some value := by
  have cases :
      value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 ∨
      value = 4 ∨ value = 5 ∨ value = 6 ∨ value = 7 ∨
      value = 8 ∨ value = 9 ∨ value = 10 ∨ value = 11 ∨
      value = 12 ∨ value = 13 ∨ value = 14 ∨ value = 15 := by
    omega
  rcases cases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst value <;> rfl

private def parseHexDigits : Nat → List Char → Option Nat
  | 0, [] => some 0
  | 0, _ :: _ => none
  | _ + 1, [] => none
  | width + 1, digit :: rest => do
      let value ← hexDigitValue? digit
      let suffix ← parseHexDigits width rest
      some (value * 16 ^ width + suffix)

private theorem parseHexDigits_encodeHexDigits
    (width value : Nat)
    (inRange : value < 16 ^ width) :
    parseHexDigits width (encodeHexDigits width value) = some value := by
  induction width generalizing value with
  | zero =>
      have valueZero : value = 0 := by simpa using inRange
      subst value
      rfl
  | succ width ih =>
      have powerPositive : 0 < 16 ^ width := Nat.pow_pos (by decide)
      have quotientInRange : value / 16 ^ width < 16 := by
        apply (Nat.div_lt_iff_lt_mul powerPositive).2
        simpa [Nat.pow_succ'] using inRange
      have remainderInRange : value % 16 ^ width < 16 ^ width :=
        Nat.mod_lt value powerPositive
      simp [
        encodeHexDigits,
        parseHexDigits,
        hexDigitValue_digitChar _ quotientInRange,
        ih _ remainderInRange
      ]
      simpa [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div' value (16 ^ width)

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
        match parseHexDigits 64 digits with
        | none =>
            failAt path .invalidWord (.mkObj [("reason", "lowercase-hex")])
        | some value =>
            match Word.ofNat? value with
            | some word => pure word
            | none => failAt path .invalidWord (.mkObj [("reason", "range")])
  | _ => failAt path .invalidWord (.mkObj [("reason", "prefix")])

def decodeWordText (text : String) : DecodeResult Word :=
  decodeWordTextAt .root text

@[simp] theorem decodeWordTextAt_encodeWordText
    (path : DecodePath)
    (value : Word) :
    decodeWordTextAt path (encodeWordText value) = .ok value := by
  have inRange : value.val < 16 ^ 64 := by
    rw [show (16 : Nat) ^ 64 = wordModulus by decide]
    exact value.isLt
  have reconstructed : Word.ofNat? value.val = some value := by
    simp [Word.ofNat?, value.isLt]
  simp [
    decodeWordTextAt,
    encodeWordText,
    String.toList_append,
    encodeHexDigits_length,
    parseHexDigits_encodeHexDigits _ _ inRange,
    reconstructed
  ]
  rfl

@[simp] theorem decodeWordText_encodeWordText (value : Word) :
    decodeWordText (encodeWordText value) = .ok value :=
  decodeWordTextAt_encodeWordText .root value

def encodeWord (value : Word) : Lean.Json :=
  encodeWordText value

def decodeWordAt (path : DecodePath) (json : Lean.Json) : DecodeResult Word := do
  decodeWordTextAt path (← decodeStringAt path json)

def decodeWord (json : Lean.Json) : DecodeResult Word :=
  decodeWordAt .root json

@[simp] theorem decodeWordAt_encodeWord (path : DecodePath) (value : Word) :
    decodeWordAt path (encodeWord value) = .ok value := by
  simp [decodeWordAt, encodeWord, decodeStringAt]

@[simp] theorem decodeWord_encodeWord (value : Word) :
    decodeWord (encodeWord value) = .ok value :=
  decodeWordAt_encodeWord .root value

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
  | .unary op operand =>
      .mkObj [
        ("tag", "unary"),
        ("op", encodeUnaryOp op),
        ("operand", encodeExpr operand)
      ]
  | .binary op left right =>
      .mkObj [
        ("tag", "binary"),
        ("op", encodeBinaryOp op),
        ("left", encodeExpr left),
        ("right", encodeExpr right)
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
          "condition", "thenBranch", "elseBranch", "op", "operand",
          "left", "right"]
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
      | "unary" =>
          ensureExactObject path json
            ["tag", "op", "operand"] ["tag", "op", "operand"]
          let opPath := path.field "op"
          let op ← decodeUnaryOpAt opPath (← requireField path json "op")
          let operandPath := path.field "operand"
          let (operand, afterOperand) ←
            decodeExprAt limits depth nodes operandPath
              (← requireField path json "operand")
          pure (.unary op operand, afterOperand)
      | "binary" =>
          ensureExactObject path json
            ["tag", "op", "left", "right"] ["tag", "op", "left", "right"]
          let opPath := path.field "op"
          let op ← decodeBinaryOpAt opPath (← requireField path json "op")
          let leftPath := path.field "left"
          let (left, afterLeft) ←
            decodeExprAt limits depth nodes leftPath
              (← requireField path json "left")
          let rightPath := path.field "right"
          let (right, afterRight) ←
            decodeExprAt limits depth afterLeft rightPath
              (← requireField path json "right")
          pure (.binary op left right, afterRight)
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
            ("allowed", .arr #[
              "unit", "bool", "word", "var", "unary", "binary", "let", "if"
            ])
          ])

def exprDepth : Expr → Nat
  | .unit | .bool _ | .word _ | .var _ => 1
  | .unary _ operand => exprDepth operand + 1
  | .binary _ left right =>
      Nat.max (exprDepth left) (exprDepth right) + 1
  | .letE initializer body =>
      Nat.max (exprDepth initializer) (exprDepth body) + 1
  | .ifE condition thenBranch elseBranch =>
      Nat.max (exprDepth condition) (Nat.max (exprDepth thenBranch) (exprDepth elseBranch)) + 1

def exprNodes : Expr → Nat
  | .unit | .bool _ | .word _ | .var _ => 1
  | .unary _ operand => 1 + exprNodes operand
  | .binary _ left right => 1 + exprNodes left + exprNodes right
  | .letE initializer body =>
      1 + exprNodes initializer + exprNodes body
  | .ifE condition thenBranch elseBranch =>
      1 + exprNodes condition + exprNodes thenBranch + exprNodes elseBranch

@[simp] private theorem decodeExprAt_encodeUnitStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath) :
    decodeExprAt limits (depth + 1) (nodes + 1) path (encodeExpr .unit) =
      .ok (.unit, nodes) := by
  rfl

@[simp] private theorem decodeExprAt_encodeBoolStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (value : Bool) :
    decodeExprAt limits (depth + 1) (nodes + 1) path (encodeExpr (.bool value)) =
      .ok (.bool value, nodes) := by
  cases value <;> rfl

@[simp] private theorem decodeExprAt_encodeWordStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (value : Word) :
    decodeExprAt limits (depth + 1) (nodes + 1) path (encodeExpr (.word value)) =
      .ok (.word value, nodes) := by
  change (do
    let decoded ← decodeWordAt (path.field "value") (encodeWord value)
    pure (Expr.word decoded, nodes)) = .ok (Expr.word value, nodes)
  simp
  rfl

@[simp] private theorem decodeExprAt_encodeVarStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (index : Nat) :
    decodeExprAt limits (depth + 1) (nodes + 1) path (encodeExpr (.var index)) =
      .ok (.var index, nodes) := by
  change (do
    let decoded ← decodeNatAt (path.field "index") (Lean.toJson index)
    pure (Expr.var decoded, nodes)) = .ok (Expr.var index, nodes)
  simp [decodeNatAt]
  rfl

private theorem decodeExprAt_encodeUnaryStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (op : UnaryOp)
    (operand : Expr) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.unary op operand)) = (do
      let (decodedOperand, afterOperand) ←
        decodeExprAt limits depth nodes (path.field "operand") (encodeExpr operand)
      pure (.unary op decodedOperand, afterOperand)) := by
  cases op <;> rfl

private theorem decodeExprAt_encodeBinaryStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (op : BinaryOp)
    (left right : Expr) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.binary op left right)) = (do
      let (decodedLeft, afterLeft) ←
        decodeExprAt limits depth nodes (path.field "left") (encodeExpr left)
      let (decodedRight, afterRight) ←
        decodeExprAt limits depth afterLeft (path.field "right") (encodeExpr right)
      pure (.binary op decodedLeft decodedRight, afterRight)) := by
  cases op <;> rfl

private theorem decodeExprAt_encodeLetStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (initializer body : Expr) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.letE initializer body)) = (do
      let (decodedInitializer, afterInitializer) ←
        decodeExprAt limits depth nodes (path.field "initializer") (encodeExpr initializer)
      let (decodedBody, afterBody) ←
        decodeExprAt limits depth afterInitializer (path.field "body") (encodeExpr body)
      pure (.letE decodedInitializer decodedBody, afterBody)) := by
  rfl

private theorem decodeExprAt_encodeIfStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (condition thenBranch elseBranch : Expr) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.ifE condition thenBranch elseBranch)) = (do
      let (decodedCondition, afterCondition) ←
        decodeExprAt limits depth nodes (path.field "condition") (encodeExpr condition)
      let (decodedThen, afterThen) ←
        decodeExprAt limits depth afterCondition (path.field "thenBranch")
          (encodeExpr thenBranch)
      let (decodedElse, afterElse) ←
        decodeExprAt limits depth afterThen (path.field "elseBranch") (encodeExpr elseBranch)
      pure (.ifE decodedCondition decodedThen decodedElse, afterElse)) := by
  rfl

private theorem decodeExprAt_encodeExpr
    (limits : DecodeLimits)
    (expr : Expr)
    (path : DecodePath)
    (depthBudget nodesBudget : Nat)
    (depthEnough : exprDepth expr ≤ depthBudget)
    (nodesEnough : exprNodes expr ≤ nodesBudget) :
    decodeExprAt limits depthBudget nodesBudget path (encodeExpr expr) =
      .ok (expr, nodesBudget - exprNodes expr) := by
  induction expr generalizing depthBudget nodesBudget path with
  | unit =>
      cases depthBudget with
      | zero => simp [exprDepth] at depthEnough
      | succ depth =>
          cases nodesBudget with
          | zero => simp [exprNodes] at nodesEnough
          | succ nodes => simp [exprNodes]
  | bool value =>
      cases depthBudget with
      | zero => simp [exprDepth] at depthEnough
      | succ depth =>
          cases nodesBudget with
          | zero => simp [exprNodes] at nodesEnough
          | succ nodes => simp [exprNodes]
  | word value =>
      cases depthBudget with
      | zero => simp [exprDepth] at depthEnough
      | succ depth =>
          cases nodesBudget with
          | zero => simp [exprNodes] at nodesEnough
          | succ nodes => simp [exprNodes]
  | var index =>
      cases depthBudget with
      | zero => simp [exprDepth] at depthEnough
      | succ depth =>
          cases nodesBudget with
          | zero => simp [exprNodes] at nodesEnough
          | succ nodes => simp [exprNodes]
  | unary op operand operandIH =>
      cases depthBudget with
      | zero => simp [exprDepth] at depthEnough
      | succ depth =>
          cases nodesBudget with
          | zero => simp [exprNodes] at nodesEnough
          | succ nodes =>
              have operandDepth : exprDepth operand ≤ depth := by
                simp [exprDepth] at depthEnough
                omega
              have operandNodes : exprNodes operand ≤ nodes := by
                simp [exprNodes] at nodesEnough
                omega
              rw [decodeExprAt_encodeUnaryStep]
              rw [operandIH
                (path := path.field "operand")
                (depthBudget := depth)
                (nodesBudget := nodes)
                operandDepth operandNodes]
              change Except.ok (Expr.unary op operand, nodes - exprNodes operand) =
                Except.ok (Expr.unary op operand,
                  nodes + 1 - (1 + exprNodes operand))
              congr 2
              omega
  | binary op left right leftIH rightIH =>
      cases depthBudget with
      | zero => simp [exprDepth] at depthEnough
      | succ depth =>
          cases nodesBudget with
          | zero => simp [exprNodes] at nodesEnough
          | succ nodes =>
              have bothDepth :
                  Nat.max (exprDepth left) (exprDepth right) ≤ depth := by
                simpa [exprDepth] using depthEnough
              have leftDepth : exprDepth left ≤ depth :=
                (Nat.max_le.mp bothDepth).1
              have rightDepth : exprDepth right ≤ depth :=
                (Nat.max_le.mp bothDepth).2
              have combinedNodes :
                  exprNodes left + exprNodes right ≤ nodes := by
                simp [exprNodes] at nodesEnough
                omega
              have leftNodes : exprNodes left ≤ nodes := by
                omega
              have rightNodes :
                  exprNodes right ≤ nodes - exprNodes left := by
                omega
              rw [decodeExprAt_encodeBinaryStep]
              rw [leftIH
                (path := path.field "left")
                (depthBudget := depth)
                (nodesBudget := nodes)
                leftDepth leftNodes]
              change (do
                let (decodedRight, afterRight) ←
                  decodeExprAt limits depth (nodes - exprNodes left)
                    (path.field "right") (encodeExpr right)
                pure (Expr.binary op left decodedRight, afterRight)) =
                  .ok (Expr.binary op left right,
                    nodes + 1 - exprNodes (Expr.binary op left right))
              rw [rightIH
                (path := path.field "right")
                (depthBudget := depth)
                (nodesBudget := nodes - exprNodes left)
                rightDepth rightNodes]
              change Except.ok (Expr.binary op left right,
                (nodes - exprNodes left) - exprNodes right) =
                  Except.ok (Expr.binary op left right,
                    nodes + 1 - (1 + exprNodes left + exprNodes right))
              congr 2
              omega
  | letE initializer body initializerIH bodyIH =>
      cases depthBudget with
      | zero => simp [exprDepth] at depthEnough
      | succ depth =>
          cases nodesBudget with
          | zero => simp [exprNodes] at nodesEnough
          | succ nodes =>
              have bothDepth :
                  Nat.max (exprDepth initializer) (exprDepth body) ≤ depth := by
                simpa [exprDepth] using depthEnough
              have initializerDepth : exprDepth initializer ≤ depth :=
                (Nat.max_le.mp bothDepth).1
              have bodyDepth : exprDepth body ≤ depth :=
                (Nat.max_le.mp bothDepth).2
              have combinedNodes :
                  exprNodes initializer + exprNodes body ≤ nodes := by
                simp [exprNodes] at nodesEnough
                omega
              have initializerNodes : exprNodes initializer ≤ nodes := by
                omega
              have bodyNodes :
                  exprNodes body ≤ nodes - exprNodes initializer := by
                omega
              rw [decodeExprAt_encodeLetStep]
              rw [initializerIH
                (path := path.field "initializer")
                (depthBudget := depth)
                (nodesBudget := nodes)
                initializerDepth initializerNodes]
              change (do
                let (decodedBody, afterBody) ←
                  decodeExprAt limits depth (nodes - exprNodes initializer)
                    (path.field "body") (encodeExpr body)
                pure (Expr.letE initializer decodedBody, afterBody)) =
                  .ok (Expr.letE initializer body,
                    nodes + 1 - exprNodes (Expr.letE initializer body))
              rw [bodyIH
                (path := path.field "body")
                (depthBudget := depth)
                (nodesBudget := nodes - exprNodes initializer)
                bodyDepth bodyNodes]
              change Except.ok (Expr.letE initializer body,
                (nodes - exprNodes initializer) - exprNodes body) =
                  Except.ok (Expr.letE initializer body,
                    nodes + 1 - (1 + exprNodes initializer + exprNodes body))
              congr 2
              omega
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      cases depthBudget with
      | zero => simp [exprDepth] at depthEnough
      | succ depth =>
          cases nodesBudget with
          | zero => simp [exprNodes] at nodesEnough
          | succ nodes =>
              have allDepth :
                  Nat.max (exprDepth condition)
                    (Nat.max (exprDepth thenBranch) (exprDepth elseBranch)) ≤ depth := by
                simpa [exprDepth] using depthEnough
              have conditionDepth : exprDepth condition ≤ depth :=
                (Nat.max_le.mp allDepth).1
              have branchDepths :
                  Nat.max (exprDepth thenBranch) (exprDepth elseBranch) ≤ depth :=
                (Nat.max_le.mp allDepth).2
              have thenDepth : exprDepth thenBranch ≤ depth :=
                (Nat.max_le.mp branchDepths).1
              have elseDepth : exprDepth elseBranch ≤ depth :=
                (Nat.max_le.mp branchDepths).2
              have combinedNodes :
                  exprNodes condition + exprNodes thenBranch + exprNodes elseBranch ≤ nodes := by
                simp [exprNodes] at nodesEnough
                omega
              have conditionNodes : exprNodes condition ≤ nodes := by
                omega
              have thenNodes :
                  exprNodes thenBranch ≤ nodes - exprNodes condition := by
                omega
              have elseNodes :
                  exprNodes elseBranch ≤
                    (nodes - exprNodes condition) - exprNodes thenBranch := by
                omega
              rw [decodeExprAt_encodeIfStep]
              rw [conditionIH
                (path := path.field "condition")
                (depthBudget := depth)
                (nodesBudget := nodes)
                conditionDepth conditionNodes]
              change (do
                let (decodedThen, afterThen) ←
                  decodeExprAt limits depth (nodes - exprNodes condition)
                    (path.field "thenBranch") (encodeExpr thenBranch)
                let (decodedElse, afterElse) ←
                  decodeExprAt limits depth afterThen
                    (path.field "elseBranch") (encodeExpr elseBranch)
                pure (Expr.ifE condition decodedThen decodedElse, afterElse)) =
                  .ok (Expr.ifE condition thenBranch elseBranch,
                    nodes + 1 - exprNodes (Expr.ifE condition thenBranch elseBranch))
              rw [thenIH
                (path := path.field "thenBranch")
                (depthBudget := depth)
                (nodesBudget := nodes - exprNodes condition)
                thenDepth thenNodes]
              change (do
                let (decodedElse, afterElse) ←
                  decodeExprAt limits depth
                    ((nodes - exprNodes condition) - exprNodes thenBranch)
                    (path.field "elseBranch") (encodeExpr elseBranch)
                pure (Expr.ifE condition thenBranch decodedElse, afterElse)) =
                  .ok (Expr.ifE condition thenBranch elseBranch,
                    nodes + 1 - exprNodes (Expr.ifE condition thenBranch elseBranch))
              rw [elseIH
                (path := path.field "elseBranch")
                (depthBudget := depth)
                (nodesBudget :=
                  (nodes - exprNodes condition) - exprNodes thenBranch)
                elseDepth elseNodes]
              change Except.ok (Expr.ifE condition thenBranch elseBranch,
                ((nodes - exprNodes condition) - exprNodes thenBranch) -
                  exprNodes elseBranch) =
                    Except.ok (Expr.ifE condition thenBranch elseBranch,
                      nodes + 1 -
                        (1 + exprNodes condition + exprNodes thenBranch +
                          exprNodes elseBranch))
              congr 2
              omega

def decodeExprWith (limits : DecodeLimits) (json : Lean.Json) : DecodeResult Expr := do
  let (expr, _) ←
    decodeExprAt limits limits.maxDepth limits.maxNodes .root json
  pure expr

theorem decodeExprWith_encodeExpr
    (limits : DecodeLimits)
    (expr : Expr)
    (depthEnough : exprDepth expr ≤ limits.maxDepth)
    (nodesEnough : exprNodes expr ≤ limits.maxNodes) :
    decodeExprWith limits (encodeExpr expr) = .ok expr := by
  rw [decodeExprWith]
  rw [decodeExprAt_encodeExpr
    limits expr .root limits.maxDepth limits.maxNodes depthEnough nodesEnough]
  rfl

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
  exact decodeExprWith_encodeExpr
    DecodeLimits.default
    (.var index)
    (by simp [exprDepth, DecodeLimits.default])
    (by simp [exprNodes, DecodeLimits.default])

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

@[simp] theorem decodeValue_encodeWord (value : Word) :
    decodeValue (encodeValue (.word value)) = .ok (.word value) := by
  change (do
    let decoded ← decodeWordAt (DecodePath.root.field "value") (encodeWord value)
    pure (Value.word decoded)) = .ok (Value.word value)
  simp
  rfl

theorem decodeValue_encodeValue (value : Value) :
    decodeValue (encodeValue value) = .ok value := by
  cases value with
  | unit => exact decodeValue_encodeUnit
  | bool value => exact decodeValue_encodeBool value
  | word value => exact decodeValue_encodeWord value

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

private theorem decodeProgramWith_encodeProgramStep
    (limits : DecodeLimits)
    (program : Program) :
    decodeProgramWith limits (encodeProgram program) = (do
      let (body, _) ←
        decodeExprAt limits limits.maxDepth limits.maxNodes
          (DecodePath.root.field "body") (encodeExpr program.body)
      pure { resultType := program.resultType, body }) := by
  cases program with
  | mk resultType body =>
      cases resultType <;> rfl

theorem decodeProgramWith_encodeProgram
    (limits : DecodeLimits)
    (program : Program)
    (depthEnough : exprDepth program.body ≤ limits.maxDepth)
    (nodesEnough : exprNodes program.body ≤ limits.maxNodes) :
    decodeProgramWith limits (encodeProgram program) = .ok program := by
  rw [decodeProgramWith_encodeProgramStep]
  rw [decodeExprAt_encodeExpr
    limits program.body (DecodePath.root.field "body")
      limits.maxDepth limits.maxNodes depthEnough nodesEnough]
  cases program
  rfl

def canonicalizeProgramWith
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult Lean.Json :=
  encodeProgram <$> decodeProgramWith limits json

def canonicalizeProgram (json : Lean.Json) : DecodeResult Lean.Json :=
  canonicalizeProgramWith DecodeLimits.default json

theorem canonicalizeProgramWith_encodeProgram
    (limits : DecodeLimits)
    (program : Program)
    (depthEnough : exprDepth program.body ≤ limits.maxDepth)
    (nodesEnough : exprNodes program.body ≤ limits.maxNodes) :
    canonicalizeProgramWith limits (encodeProgram program) =
      .ok (encodeProgram program) := by
  simp [
    canonicalizeProgramWith,
    decodeProgramWith_encodeProgram limits program depthEnough nodesEnough
  ]
  rfl

theorem canonicalizeProgramWith_idempotent
    (limits : DecodeLimits)
    (json : Lean.Json)
    (program : Program)
    (decoded : decodeProgramWith limits json = .ok program)
    (depthEnough : exprDepth program.body ≤ limits.maxDepth)
    (nodesEnough : exprNodes program.body ≤ limits.maxNodes) :
    canonicalizeProgramWith limits json >>=
        canonicalizeProgramWith limits =
      canonicalizeProgramWith limits json := by
  simp [canonicalizeProgramWith, decoded]
  exact canonicalizeProgramWith_encodeProgram
    limits program depthEnough nodesEnough

end Solcore.Core.Wire.V2
