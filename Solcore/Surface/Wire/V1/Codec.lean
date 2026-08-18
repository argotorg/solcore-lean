import Lean.Data.Json
import Solcore.Foundation.Json
import Solcore.Surface.Wire.V1.Syntax

set_option autoImplicit false

namespace Solcore.Surface.Wire.V1

def schemaVersion : String := "solcore-surface/v1"

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

private def segmentToken : PathSegment -> String
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
  | expectedNatural
  | missingField
  | unknownField
  | invalidSchema
  | invalidTag
  | invalidIdentifierText
  | invalidDecimalDigits
  | invalidHexadecimalDigits
  | depthLimitExceeded
  | nodeLimitExceeded
  deriving Repr, BEq, DecidableEq

namespace DecodeErrorCode

def wireName : DecodeErrorCode -> String
  | .expectedObject => "expected-object"
  | .expectedArray => "expected-array"
  | .expectedString => "expected-string"
  | .expectedNatural => "expected-natural"
  | .missingField => "missing-field"
  | .unknownField => "unknown-field"
  | .invalidSchema => "invalid-schema"
  | .invalidTag => "invalid-tag"
  | .invalidIdentifierText => "invalid-identifier-text"
  | .invalidDecimalDigits => "invalid-decimal-digits"
  | .invalidHexadecimalDigits => "invalid-hexadecimal-digits"
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

abbrev DecodeResult (α : Type) := Except DecodeError α

private def failAt {α : Type}
    (path : DecodePath)
    (code : DecodeErrorCode)
    (arguments : Lean.Json := .null) :
    DecodeResult α :=
  .error { path, code, arguments }

private def jsonKind : Lean.Json -> String
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

private def ensureExactObject
    (path : DecodePath)
    (json : Lean.Json)
    (allowed required : List String) :
    DecodeResult Unit := do
  let fields <-
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
      | .error _ =>
          failAt (path.field name) .missingField (.mkObj [("field", name)])
  | _ => failAt path .expectedObject (expectedArguments "object" json)

private def decodeStringAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult String :=
  match json with
  | .str value => pure value
  | _ => failAt path .expectedString (expectedArguments "string" json)

private def decodeNatAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Nat :=
  match Foundation.jsonNatural? json with
  | some value => pure value
  | none => failAt path .expectedNatural (expectedArguments "natural" json)

private def consumeNode
    (limits : DecodeLimits)
    (path : DecodePath) :
    Nat -> DecodeResult Nat
  | 0 =>
      failAt path .nodeLimitExceeded (.mkObj [("limit", limits.maxNodes)])
  | nodes + 1 => pure nodes

private def decodeListAt {α : Type}
    (decodeValue : Nat -> DecodePath -> Lean.Json -> DecodeResult (α × Nat))
    (path : DecodePath) :
    Nat -> Nat -> List Lean.Json -> DecodeResult (List α × Nat)
  | _, nodes, [] => pure ([], nodes)
  | index, nodes, json :: rest => do
      let (value, afterValue) <- decodeValue nodes (path.index index) json
      let (values, afterRest) <-
        decodeListAt decodeValue path (index + 1) afterValue rest
      pure (value :: values, afterRest)

private def decodeArrayAt {α : Type}
    (decodeValue : Nat -> DecodePath -> Lean.Json -> DecodeResult (α × Nat))
    (path : DecodePath)
    (nodes : Nat)
    (json : Lean.Json) :
    DecodeResult (List α × Nat) :=
  match json with
  | .arr values => decodeListAt decodeValue path 0 nodes values.toList
  | _ => failAt path .expectedArray (expectedArguments "array" json)

def encodeIdentifierText (text : IdentifierText) : Lean.Json :=
  text.value

def decodeIdentifierTextAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult IdentifierText := do
  let value <- decodeStringAt path json
  match IdentifierText.ofString? value with
  | some text => pure text
  | none =>
      failAt path .invalidIdentifierText (.mkObj [("actual", value)])

def decodeIdentifierText (json : Lean.Json) : DecodeResult IdentifierText :=
  decodeIdentifierTextAt .root json

def encodeDecimalDigits (digits : DecimalDigits) : Lean.Json :=
  digits.value

def decodeDecimalDigitsAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult DecimalDigits := do
  let value <- decodeStringAt path json
  match DecimalDigits.ofString? value with
  | some digits => pure digits
  | none =>
      failAt path .invalidDecimalDigits (.mkObj [("actual", value)])

def decodeDecimalDigits (json : Lean.Json) : DecodeResult DecimalDigits :=
  decodeDecimalDigitsAt .root json

def encodeHexadecimalDigits (digits : HexadecimalDigits) : Lean.Json :=
  digits.value

def decodeHexadecimalDigitsAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult HexadecimalDigits := do
  let value <- decodeStringAt path json
  match HexadecimalDigits.ofString? value with
  | some digits => pure digits
  | none =>
      failAt path .invalidHexadecimalDigits (.mkObj [("actual", value)])

def decodeHexadecimalDigits (json : Lean.Json) :
    DecodeResult HexadecimalDigits :=
  decodeHexadecimalDigitsAt .root json

def encodeSourceSpan (span : SourceSpan) : Lean.Json :=
  .mkObj [
    ("source", span.source),
    ("startByte", span.startByte),
    ("endByte", span.endByte)
  ]

def decodeSourceSpanAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult SourceSpan := do
  ensureExactObject path json
    ["source", "startByte", "endByte"]
    ["source", "startByte", "endByte"]
  let sourcePath := path.field "source"
  let source <- decodeStringAt sourcePath (← requireField path json "source")
  let startPath := path.field "startByte"
  let startByte <- decodeNatAt startPath (← requireField path json "startByte")
  let endPath := path.field "endByte"
  let endByte <- decodeNatAt endPath (← requireField path json "endByte")
  pure { source, startByte, endByte }

def decodeSourceSpan (json : Lean.Json) : DecodeResult SourceSpan :=
  decodeSourceSpanAt .root json

def encodeName (name : Name) : Lean.Json :=
  .mkObj [
    ("span", encodeSourceSpan name.span),
    ("text", encodeIdentifierText name.text)
  ]

private def decodeNameAt
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (Name × Nat) := do
  let nodes <- consumeNode limits path nodes
  ensureExactObject path json ["span", "text"] ["span", "text"]
  let spanPath := path.field "span"
  let span <- decodeSourceSpanAt spanPath (← requireField path json "span")
  let textPath := path.field "text"
  let text <- decodeIdentifierTextAt textPath (← requireField path json "text")
  pure ({ span, text }, nodes)

def decodeName
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult Name := do
  let (name, _) <- decodeNameAt limits limits.maxNodes .root json
  pure name

def encodeTypeSpelling : TypeSpelling -> Lean.Json
  | .bool => "bool"
  | .word => "word"

def decodeTypeSpellingAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult TypeSpelling := do
  let value <- decodeStringAt path json
  match value with
  | "bool" => pure .bool
  | "word" => pure .word
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", value),
        ("allowed", .arr #["bool", "word"])
      ])

def decodeTypeSpelling (json : Lean.Json) : DecodeResult TypeSpelling :=
  decodeTypeSpellingAt .root json

def encodeTypeSpellingOccurrence
    (occurrence : TypeSpellingOccurrence) :
    Lean.Json :=
  .mkObj [
    ("span", encodeSourceSpan occurrence.span),
    ("text", encodeTypeSpelling occurrence.text)
  ]

private def decodeTypeSpellingOccurrenceAt
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (TypeSpellingOccurrence × Nat) := do
  let nodes <- consumeNode limits path nodes
  ensureExactObject path json ["span", "text"] ["span", "text"]
  let spanPath := path.field "span"
  let span <- decodeSourceSpanAt spanPath (← requireField path json "span")
  let textPath := path.field "text"
  let text <- decodeTypeSpellingAt textPath (← requireField path json "text")
  pure ({ span, text }, nodes)

def decodeTypeSpellingOccurrence
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult TypeSpellingOccurrence := do
  let (occurrence, _) <-
    decodeTypeSpellingOccurrenceAt limits limits.maxNodes .root json
  pure occurrence

def encodeTypeSyntax : TypeSyntax -> Lean.Json
  | .unit span =>
      .mkObj [
        ("tag", "unit"),
        ("span", encodeSourceSpan span)
      ]
  | .named name =>
      .mkObj [
        ("tag", "named"),
        ("name", encodeTypeSpellingOccurrence name)
      ]

private def decodeTypeSyntaxAt
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (TypeSyntax × Nat) := do
  let nodes <- consumeNode limits path nodes
  ensureExactObject path json ["tag", "span", "name"] ["tag"]
  let tagPath := path.field "tag"
  let tag <- decodeStringAt tagPath (← requireField path json "tag")
  match tag with
  | "unit" =>
      ensureExactObject path json ["tag", "span"] ["tag", "span"]
      let spanPath := path.field "span"
      let span <- decodeSourceSpanAt spanPath (← requireField path json "span")
      pure (.unit span, nodes)
  | "named" =>
      ensureExactObject path json ["tag", "name"] ["tag", "name"]
      let namePath := path.field "name"
      let (name, nodes) <-
        decodeTypeSpellingOccurrenceAt limits nodes namePath
          (← requireField path json "name")
      pure (.named name, nodes)
  | _ =>
      failAt tagPath .invalidTag (.mkObj [
        ("actual", tag),
        ("allowed", .arr #["unit", "named"])
      ])

def decodeTypeSyntax
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult TypeSyntax := do
  let (type, _) <- decodeTypeSyntaxAt limits limits.maxNodes .root json
  pure type

def encodeIntegerLiteral : IntegerLiteral -> Lean.Json
  | .decimal span digits =>
      .mkObj [
        ("span", encodeSourceSpan span),
        ("base", "decimal"),
        ("digits", encodeDecimalDigits digits)
      ]
  | .hexadecimal span digits =>
      .mkObj [
        ("span", encodeSourceSpan span),
        ("base", "hexadecimal"),
        ("digits", encodeHexadecimalDigits digits)
      ]

private def decodeIntegerLiteralAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult IntegerLiteral := do
  ensureExactObject path json
    ["span", "base", "digits"] ["span", "base", "digits"]
  let spanPath := path.field "span"
  let span <- decodeSourceSpanAt spanPath (← requireField path json "span")
  let basePath := path.field "base"
  let base <- decodeStringAt basePath (← requireField path json "base")
  let digitsPath := path.field "digits"
  let digitsJson <- requireField path json "digits"
  match base with
  | "decimal" =>
      pure (.decimal span (← decodeDecimalDigitsAt digitsPath digitsJson))
  | "hexadecimal" =>
      pure (.hexadecimal span
        (← decodeHexadecimalDigitsAt digitsPath digitsJson))
  | _ =>
      failAt basePath .invalidTag (.mkObj [
        ("actual", base),
        ("allowed", .arr #["decimal", "hexadecimal"])
      ])

def decodeIntegerLiteral (json : Lean.Json) :
    DecodeResult IntegerLiteral :=
  decodeIntegerLiteralAt .root json

def encodeUnaryOp : UnaryOp -> Lean.Json
  | .not => "not"

def decodeUnaryOpAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult UnaryOp := do
  let value <- decodeStringAt path json
  match value with
  | "not" => pure .not
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", value),
        ("allowed", .arr #["not"])
      ])

def decodeUnaryOp (json : Lean.Json) : DecodeResult UnaryOp :=
  decodeUnaryOpAt .root json

def encodeBinaryOp : BinaryOp -> Lean.Json
  | .mul => "mul"
  | .div => "div"
  | .mod => "mod"
  | .add => "add"
  | .sub => "sub"
  | .bitAnd => "bitAnd"
  | .bitXor => "bitXor"
  | .bitOr => "bitOr"
  | .lt => "lt"
  | .gt => "gt"
  | .le => "le"
  | .ge => "ge"
  | .eq => "eq"
  | .ne => "ne"

def decodeBinaryOpAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult BinaryOp := do
  let value <- decodeStringAt path json
  match value with
  | "mul" => pure .mul
  | "div" => pure .div
  | "mod" => pure .mod
  | "add" => pure .add
  | "sub" => pure .sub
  | "bitAnd" => pure .bitAnd
  | "bitXor" => pure .bitXor
  | "bitOr" => pure .bitOr
  | "lt" => pure .lt
  | "gt" => pure .gt
  | "le" => pure .le
  | "ge" => pure .ge
  | "eq" => pure .eq
  | "ne" => pure .ne
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", value),
        ("allowed", .arr #[
          "mul", "div", "mod", "add", "sub", "bitAnd", "bitXor",
          "bitOr", "lt", "gt", "le", "ge", "eq", "ne"
        ])
      ])

def decodeBinaryOp (json : Lean.Json) : DecodeResult BinaryOp :=
  decodeBinaryOpAt .root json

def encodeUnaryOperator (operator : UnaryOperator) : Lean.Json :=
  .mkObj [
    ("span", encodeSourceSpan operator.span),
    ("operator", encodeUnaryOp operator.operator)
  ]

private def decodeUnaryOperatorAt
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (UnaryOperator × Nat) := do
  let nodes <- consumeNode limits path nodes
  ensureExactObject path json ["span", "operator"] ["span", "operator"]
  let spanPath := path.field "span"
  let span <- decodeSourceSpanAt spanPath (← requireField path json "span")
  let operatorPath := path.field "operator"
  let operator <- decodeUnaryOpAt operatorPath
    (← requireField path json "operator")
  pure ({ span, operator }, nodes)

def decodeUnaryOperator
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult UnaryOperator := do
  let (operator, _) <-
    decodeUnaryOperatorAt limits limits.maxNodes .root json
  pure operator

def encodeBinaryOperator (operator : BinaryOperator) : Lean.Json :=
  .mkObj [
    ("span", encodeSourceSpan operator.span),
    ("operator", encodeBinaryOp operator.operator)
  ]

private def decodeBinaryOperatorAt
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (BinaryOperator × Nat) := do
  let nodes <- consumeNode limits path nodes
  ensureExactObject path json ["span", "operator"] ["span", "operator"]
  let spanPath := path.field "span"
  let span <- decodeSourceSpanAt spanPath (← requireField path json "span")
  let operatorPath := path.field "operator"
  let operator <- decodeBinaryOpAt operatorPath
    (← requireField path json "operator")
  pure ({ span, operator }, nodes)

def decodeBinaryOperator
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult BinaryOperator := do
  let (operator, _) <-
    decodeBinaryOperatorAt limits limits.maxNodes .root json
  pure operator

def encodeExpr : Expr -> Lean.Json
  | .unit span =>
      .mkObj [
        ("tag", "unit"),
        ("span", encodeSourceSpan span)
      ]
  | .integer (.decimal span digits) =>
      .mkObj [
        ("tag", "integer"),
        ("span", encodeSourceSpan span),
        ("base", "decimal"),
        ("digits", encodeDecimalDigits digits)
      ]
  | .integer (.hexadecimal span digits) =>
      .mkObj [
        ("tag", "integer"),
        ("span", encodeSourceSpan span),
        ("base", "hexadecimal"),
        ("digits", encodeHexadecimalDigits digits)
      ]
  | .name name =>
      .mkObj [
        ("tag", "name"),
        ("name", encodeName name)
      ]
  | .group span inner =>
      .mkObj [
        ("tag", "group"),
        ("span", encodeSourceSpan span),
        ("inner", encodeExpr inner)
      ]
  | .call span callee arguments =>
      .mkObj [
        ("tag", "call"),
        ("span", encodeSourceSpan span),
        ("callee", encodeName callee),
        ("arguments", .arr (arguments.map encodeExpr).toArray)
      ]
  | .unary span operator operand =>
      .mkObj [
        ("tag", "unary"),
        ("span", encodeSourceSpan span),
        ("operator", encodeUnaryOperator operator),
        ("operand", encodeExpr operand)
      ]
  | .binary span operator left right =>
      .mkObj [
        ("tag", "binary"),
        ("span", encodeSourceSpan span),
        ("operator", encodeBinaryOperator operator),
        ("left", encodeExpr left),
        ("right", encodeExpr right)
      ]
  | .ifThenElse span condition thenBranch elseBranch =>
      .mkObj [
        ("tag", "ifThenElse"),
        ("span", encodeSourceSpan span),
        ("condition", encodeExpr condition),
        ("thenBranch", encodeExpr thenBranch),
        ("elseBranch", encodeExpr elseBranch)
      ]
termination_by expression => sizeOf expression

private def decodeExprAt
    (limits : DecodeLimits) :
    Nat -> Nat -> DecodePath -> Lean.Json -> DecodeResult (Expr × Nat)
  | 0, _, path, _ =>
      failAt path .depthLimitExceeded (.mkObj [("limit", limits.maxDepth)])
  | depth + 1, nodes, path, json => do
      let nodes <- consumeNode limits path nodes
      ensureExactObject path json
        ["tag", "span", "base", "digits", "name", "inner", "callee",
          "arguments", "operator", "operand", "left", "right",
          "condition", "thenBranch", "elseBranch"]
        ["tag"]
      let tagPath := path.field "tag"
      let tag <- decodeStringAt tagPath (← requireField path json "tag")
      match tag with
      | "unit" =>
          ensureExactObject path json ["tag", "span"] ["tag", "span"]
          let spanPath := path.field "span"
          let span <-
            decodeSourceSpanAt spanPath (← requireField path json "span")
          pure (.unit span, nodes)
      | "integer" =>
          ensureExactObject path json
            ["tag", "span", "base", "digits"]
            ["tag", "span", "base", "digits"]
          let spanPath := path.field "span"
          let span <-
            decodeSourceSpanAt spanPath (← requireField path json "span")
          let basePath := path.field "base"
          let base <- decodeStringAt basePath (← requireField path json "base")
          let digitsPath := path.field "digits"
          let digitsJson <- requireField path json "digits"
          match base with
          | "decimal" =>
              let digits <- decodeDecimalDigitsAt digitsPath digitsJson
              pure (.integer (.decimal span digits), nodes)
          | "hexadecimal" =>
              let digits <- decodeHexadecimalDigitsAt digitsPath digitsJson
              pure (.integer (.hexadecimal span digits), nodes)
          | _ =>
              failAt basePath .invalidTag (.mkObj [
                ("actual", base),
                ("allowed", .arr #["decimal", "hexadecimal"])
              ])
      | "name" =>
          ensureExactObject path json ["tag", "name"] ["tag", "name"]
          let namePath := path.field "name"
          let (name, nodes) <- decodeNameAt limits nodes namePath
            (← requireField path json "name")
          pure (.name name, nodes)
      | "group" =>
          ensureExactObject path json
            ["tag", "span", "inner"] ["tag", "span", "inner"]
          let spanPath := path.field "span"
          let span <-
            decodeSourceSpanAt spanPath (← requireField path json "span")
          let innerPath := path.field "inner"
          let (inner, nodes) <- decodeExprAt limits depth nodes innerPath
            (← requireField path json "inner")
          pure (.group span inner, nodes)
      | "call" =>
          ensureExactObject path json
            ["tag", "span", "callee", "arguments"]
            ["tag", "span", "callee", "arguments"]
          let spanPath := path.field "span"
          let span <-
            decodeSourceSpanAt spanPath (← requireField path json "span")
          let calleePath := path.field "callee"
          let (callee, nodes) <- decodeNameAt limits nodes calleePath
            (← requireField path json "callee")
          let argumentsPath := path.field "arguments"
          let (arguments, nodes) <-
            decodeArrayAt
              (fun nodes argumentPath argumentJson =>
                decodeExprAt limits depth nodes argumentPath argumentJson)
              argumentsPath nodes (← requireField path json "arguments")
          pure (.call span callee arguments, nodes)
      | "unary" =>
          ensureExactObject path json
            ["tag", "span", "operator", "operand"]
            ["tag", "span", "operator", "operand"]
          let spanPath := path.field "span"
          let span <-
            decodeSourceSpanAt spanPath (← requireField path json "span")
          let operatorPath := path.field "operator"
          let (operator, nodes) <-
            decodeUnaryOperatorAt limits nodes operatorPath
              (← requireField path json "operator")
          let operandPath := path.field "operand"
          let (operand, nodes) <- decodeExprAt limits depth nodes operandPath
            (← requireField path json "operand")
          pure (.unary span operator operand, nodes)
      | "binary" =>
          ensureExactObject path json
            ["tag", "span", "operator", "left", "right"]
            ["tag", "span", "operator", "left", "right"]
          let spanPath := path.field "span"
          let span <-
            decodeSourceSpanAt spanPath (← requireField path json "span")
          let operatorPath := path.field "operator"
          let (operator, nodes) <-
            decodeBinaryOperatorAt limits nodes operatorPath
              (← requireField path json "operator")
          let leftPath := path.field "left"
          let (left, nodes) <- decodeExprAt limits depth nodes leftPath
            (← requireField path json "left")
          let rightPath := path.field "right"
          let (right, nodes) <- decodeExprAt limits depth nodes rightPath
            (← requireField path json "right")
          pure (.binary span operator left right, nodes)
      | "ifThenElse" =>
          ensureExactObject path json
            ["tag", "span", "condition", "thenBranch", "elseBranch"]
            ["tag", "span", "condition", "thenBranch", "elseBranch"]
          let spanPath := path.field "span"
          let span <-
            decodeSourceSpanAt spanPath (← requireField path json "span")
          let conditionPath := path.field "condition"
          let (condition, nodes) <-
            decodeExprAt limits depth nodes conditionPath
              (← requireField path json "condition")
          let thenPath := path.field "thenBranch"
          let (thenBranch, nodes) <-
            decodeExprAt limits depth nodes thenPath
              (← requireField path json "thenBranch")
          let elsePath := path.field "elseBranch"
          let (elseBranch, nodes) <-
            decodeExprAt limits depth nodes elsePath
              (← requireField path json "elseBranch")
          pure (.ifThenElse span condition thenBranch elseBranch, nodes)
      | _ =>
          failAt tagPath .invalidTag (.mkObj [
            ("actual", tag),
            ("allowed", .arr #[
              "unit", "integer", "name", "group", "call", "unary",
              "binary", "ifThenElse"
            ])
          ])

def decodeExpr
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult Expr := do
  let (expression, _) <-
    decodeExprAt limits limits.maxDepth limits.maxNodes .root json
  pure expression

def encodeLetStatement (statement : LetStatement) : Lean.Json :=
  .mkObj [
    ("span", encodeSourceSpan statement.span),
    ("name", encodeName statement.name),
    ("type", encodeTypeSyntax statement.type),
    ("value", encodeExpr statement.value)
  ]

private def decodeLetStatementAt
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (LetStatement × Nat) := do
  let nodes <- consumeNode limits path nodes
  ensureExactObject path json
    ["span", "name", "type", "value"]
    ["span", "name", "type", "value"]
  let spanPath := path.field "span"
  let span <- decodeSourceSpanAt spanPath (← requireField path json "span")
  let namePath := path.field "name"
  let (name, nodes) <- decodeNameAt limits nodes namePath
    (← requireField path json "name")
  let typePath := path.field "type"
  let (type, nodes) <- decodeTypeSyntaxAt limits nodes typePath
    (← requireField path json "type")
  let valuePath := path.field "value"
  let (value, nodes) <-
    decodeExprAt limits limits.maxDepth nodes valuePath
      (← requireField path json "value")
  pure ({ span, name, type, value }, nodes)

def decodeLetStatement
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult LetStatement := do
  let (statement, _) <-
    decodeLetStatementAt limits limits.maxNodes .root json
  pure statement

def encodeReturnStatement (statement : ReturnStatement) : Lean.Json :=
  .mkObj [
    ("span", encodeSourceSpan statement.span),
    ("value", encodeExpr statement.value)
  ]

private def decodeReturnStatementAt
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (ReturnStatement × Nat) := do
  let nodes <- consumeNode limits path nodes
  ensureExactObject path json ["span", "value"] ["span", "value"]
  let spanPath := path.field "span"
  let span <- decodeSourceSpanAt spanPath (← requireField path json "span")
  let valuePath := path.field "value"
  let (value, nodes) <-
    decodeExprAt limits limits.maxDepth nodes valuePath
      (← requireField path json "value")
  pure ({ span, value }, nodes)

def decodeReturnStatement
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult ReturnStatement := do
  let (statement, _) <-
    decodeReturnStatementAt limits limits.maxNodes .root json
  pure statement

def encodeFunctionDecl (declaration : FunctionDecl) : Lean.Json :=
  .mkObj [
    ("span", encodeSourceSpan declaration.span),
    ("name", encodeName declaration.name),
    ("returnType", encodeTypeSyntax declaration.returnType),
    ("bindings", .arr
      (declaration.bindings.map encodeLetStatement).toArray),
    ("result", encodeReturnStatement declaration.result)
  ]

private def decodeFunctionDeclAt
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (FunctionDecl × Nat) := do
  let nodes <- consumeNode limits path nodes
  ensureExactObject path json
    ["span", "name", "returnType", "bindings", "result"]
    ["span", "name", "returnType", "bindings", "result"]
  let spanPath := path.field "span"
  let span <- decodeSourceSpanAt spanPath (← requireField path json "span")
  let namePath := path.field "name"
  let (name, nodes) <- decodeNameAt limits nodes namePath
    (← requireField path json "name")
  let returnTypePath := path.field "returnType"
  let (returnType, nodes) <-
    decodeTypeSyntaxAt limits nodes returnTypePath
      (← requireField path json "returnType")
  let bindingsPath := path.field "bindings"
  let (bindings, nodes) <-
    decodeArrayAt
      (fun nodes bindingPath bindingJson =>
        decodeLetStatementAt limits nodes bindingPath bindingJson)
      bindingsPath nodes (← requireField path json "bindings")
  let resultPath := path.field "result"
  let (result, nodes) <-
    decodeReturnStatementAt limits nodes resultPath
      (← requireField path json "result")
  pure ({ span, name, returnType, bindings, result }, nodes)

def decodeFunctionDecl
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult FunctionDecl := do
  let (declaration, _) <-
    decodeFunctionDeclAt limits limits.maxNodes .root json
  pure declaration

def encodeCommentKind : CommentKind -> Lean.Json
  | .line => "line"
  | .block => "block"

def decodeCommentKindAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult CommentKind := do
  let value <- decodeStringAt path json
  match value with
  | "line" => pure .line
  | "block" => pure .block
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", value),
        ("allowed", .arr #["line", "block"])
      ])

def decodeCommentKind (json : Lean.Json) : DecodeResult CommentKind :=
  decodeCommentKindAt .root json

def encodeComment (comment : Comment) : Lean.Json :=
  .mkObj [
    ("kind", encodeCommentKind comment.kind),
    ("span", encodeSourceSpan comment.span)
  ]

private def decodeCommentAt
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (Comment × Nat) := do
  let nodes <- consumeNode limits path nodes
  ensureExactObject path json ["kind", "span"] ["kind", "span"]
  let kindPath := path.field "kind"
  let kind <- decodeCommentKindAt kindPath (← requireField path json "kind")
  let spanPath := path.field "span"
  let span <- decodeSourceSpanAt spanPath (← requireField path json "span")
  pure ({ kind, span }, nodes)

def decodeComment
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult Comment := do
  let (comment, _) <- decodeCommentAt limits limits.maxNodes .root json
  pure comment

def encodeFile (file : File) : Lean.Json :=
  .mkObj [
    ("schema", schemaVersion),
    ("span", encodeSourceSpan file.span),
    ("function", encodeFunctionDecl file.function),
    ("comments", .arr (file.comments.map encodeComment).toArray)
  ]

private def decodeFileWithBudgetAt
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (File × Nat) := do
  let nodes <- consumeNode limits path nodes
  ensureExactObject path json
    ["schema", "span", "function", "comments"]
    ["schema", "span", "function", "comments"]
  let schemaPath := path.field "schema"
  let actualSchema <-
    decodeStringAt schemaPath (← requireField path json "schema")
  unless actualSchema == schemaVersion do
    failAt schemaPath .invalidSchema (.mkObj [
      ("expected", schemaVersion),
      ("actual", actualSchema)
    ])
  let spanPath := path.field "span"
  let span <- decodeSourceSpanAt spanPath (← requireField path json "span")
  let functionPath := path.field "function"
  let (function, nodes) <-
    decodeFunctionDeclAt limits nodes functionPath
      (← requireField path json "function")
  let commentsPath := path.field "comments"
  let (comments, nodes) <-
    decodeArrayAt
      (fun nodes commentPath commentJson =>
        decodeCommentAt limits nodes commentPath commentJson)
      commentsPath nodes (← requireField path json "comments")
  pure ({ span, function, comments }, nodes)

def decodeFileAt
    (limits : DecodeLimits)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult File := do
  let (file, _) <-
    decodeFileWithBudgetAt limits limits.maxNodes path json
  pure file

def decodeFile
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult File :=
  decodeFileAt limits .root json

mutual

  def exprDepth : Expr -> Nat
    | .unit _ | .integer _ | .name _ => 1
    | .group _ inner => exprDepth inner + 1
    | .call _ _ arguments => exprListDepth arguments + 1
    | .unary _ _ operand => exprDepth operand + 1
    | .binary _ _ left right =>
        Nat.max (exprDepth left) (exprDepth right) + 1
    | .ifThenElse _ condition thenBranch elseBranch =>
        Nat.max (exprDepth condition)
          (Nat.max (exprDepth thenBranch) (exprDepth elseBranch)) + 1

  def exprListDepth : List Expr -> Nat
    | [] => 0
    | expression :: rest => Nat.max (exprDepth expression) (exprListDepth rest)

end

def typeSyntaxNodes : TypeSyntax -> Nat
  | .unit _ => 1
  | .named _ => 2

mutual

  def exprNodes : Expr -> Nat
    | .unit _ | .integer _ => 1
    | .name _ => 2
    | .group _ inner => 1 + exprNodes inner
    | .call _ _ arguments => 2 + exprListNodes arguments
    | .unary _ _ operand => 2 + exprNodes operand
    | .binary _ _ left right => 2 + exprNodes left + exprNodes right
    | .ifThenElse _ condition thenBranch elseBranch =>
        1 + exprNodes condition + exprNodes thenBranch + exprNodes elseBranch

  def exprListNodes : List Expr -> Nat
    | [] => 0
    | expression :: rest => exprNodes expression + exprListNodes rest

end

def letStatementNodes (statement : LetStatement) : Nat :=
  2 + typeSyntaxNodes statement.type + exprNodes statement.value

def returnStatementNodes (statement : ReturnStatement) : Nat :=
  1 + exprNodes statement.value

def letStatementListNodes : List LetStatement -> Nat
  | [] => 0
  | statement :: rest =>
      letStatementNodes statement + letStatementListNodes rest

def functionDeclNodes (declaration : FunctionDecl) : Nat :=
  2 + typeSyntaxNodes declaration.returnType +
    letStatementListNodes declaration.bindings +
    returnStatementNodes declaration.result

def fileNodes (file : File) : Nat :=
  1 + functionDeclNodes file.function + file.comments.length

def letStatementListDepth : List LetStatement -> Nat
  | [] => 0
  | statement :: rest =>
      Nat.max (exprDepth statement.value) (letStatementListDepth rest)

def functionDeclDepth (declaration : FunctionDecl) : Nat :=
  Nat.max (letStatementListDepth declaration.bindings)
    (exprDepth declaration.result.value)

def fileDepth (file : File) : Nat :=
  functionDeclDepth file.function

@[simp] theorem decodeIdentifierTextAt_encodeIdentifierText
    (path : DecodePath)
    (text : IdentifierText) :
    decodeIdentifierTextAt path (encodeIdentifierText text) = .ok text := by
  simp [decodeIdentifierTextAt, encodeIdentifierText, decodeStringAt]
  rfl

@[simp] theorem decodeDecimalDigitsAt_encodeDecimalDigits
    (path : DecodePath)
    (digits : DecimalDigits) :
    decodeDecimalDigitsAt path (encodeDecimalDigits digits) = .ok digits := by
  simp [decodeDecimalDigitsAt, encodeDecimalDigits, decodeStringAt]
  rfl

@[simp] theorem decodeHexadecimalDigitsAt_encodeHexadecimalDigits
    (path : DecodePath)
    (digits : HexadecimalDigits) :
    decodeHexadecimalDigitsAt path (encodeHexadecimalDigits digits) =
      .ok digits := by
  simp [decodeHexadecimalDigitsAt, encodeHexadecimalDigits, decodeStringAt]
  rfl

@[simp] theorem decodeSourceSpanAt_encodeSourceSpan
    (path : DecodePath)
    (span : SourceSpan) :
    decodeSourceSpanAt path (encodeSourceSpan span) = .ok span := by
  cases span with
  | mk source startByte endByte =>
      change (do
        let decodedStart <-
          decodeNatAt (path.field "startByte") (Lean.toJson startByte)
        let decodedEnd <-
          decodeNatAt (path.field "endByte") (Lean.toJson endByte)
        pure (SourceSpan.mk source decodedStart decodedEnd)) = .ok _
      simp [decodeNatAt]
      rfl

@[simp] theorem decodeTypeSpellingAt_encodeTypeSpelling
    (path : DecodePath)
    (spelling : TypeSpelling) :
    decodeTypeSpellingAt path (encodeTypeSpelling spelling) = .ok spelling := by
  cases spelling <;> rfl

@[simp] theorem decodeUnaryOpAt_encodeUnaryOp
    (path : DecodePath)
    (operator : UnaryOp) :
    decodeUnaryOpAt path (encodeUnaryOp operator) = .ok operator := by
  cases operator
  rfl

@[simp] theorem decodeBinaryOpAt_encodeBinaryOp
    (path : DecodePath)
    (operator : BinaryOp) :
    decodeBinaryOpAt path (encodeBinaryOp operator) = .ok operator := by
  cases operator <;> rfl

@[simp] theorem decodeCommentKindAt_encodeCommentKind
    (path : DecodePath)
    (kind : CommentKind) :
    decodeCommentKindAt path (encodeCommentKind kind) = .ok kind := by
  cases kind <;> rfl

@[simp] theorem decodeIntegerLiteralAt_encodeIntegerLiteral
    (path : DecodePath)
    (literal : IntegerLiteral) :
    decodeIntegerLiteralAt path (encodeIntegerLiteral literal) = .ok literal := by
  cases literal with
  | decimal span digits =>
      change (do
        let decodedSpan <-
          decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
        let decodedDigits <-
          decodeDecimalDigitsAt (path.field "digits")
            (encodeDecimalDigits digits)
        pure (IntegerLiteral.decimal decodedSpan decodedDigits)) = .ok _
      simp
      rfl
  | hexadecimal span digits =>
      change (do
        let decodedSpan <-
          decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
        let decodedDigits <-
          decodeHexadecimalDigitsAt (path.field "digits")
            (encodeHexadecimalDigits digits)
        pure (IntegerLiteral.hexadecimal decodedSpan decodedDigits)) = .ok _
      simp
      rfl

private theorem decodeNameAt_encodeName
    (limits : DecodeLimits)
    (name : Name)
    (extraNodes : Nat)
    (path : DecodePath) :
    decodeNameAt limits (extraNodes + 1) path (encodeName name) =
      .ok (name, extraNodes) := by
  cases name with
  | mk span text =>
      change (do
        let decodedSpan <-
          decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
        let decodedText <-
          decodeIdentifierTextAt (path.field "text")
            (encodeIdentifierText text)
        pure (Name.mk decodedSpan decodedText, extraNodes)) = .ok _
      simp
      rfl

private theorem decodeTypeSpellingOccurrenceAt_encode
    (limits : DecodeLimits)
    (occurrence : TypeSpellingOccurrence)
    (extraNodes : Nat)
    (path : DecodePath) :
    decodeTypeSpellingOccurrenceAt limits (extraNodes + 1) path
      (encodeTypeSpellingOccurrence occurrence) =
      .ok (occurrence, extraNodes) := by
  cases occurrence with
  | mk span text =>
      change (do
        let decodedSpan <-
          decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
        let decodedText <-
          decodeTypeSpellingAt (path.field "text") (encodeTypeSpelling text)
        pure (TypeSpellingOccurrence.mk decodedSpan decodedText,
          extraNodes)) = .ok _
      simp
      rfl

private theorem decodeTypeSyntaxAt_encodeTypeSyntax
    (limits : DecodeLimits)
    (type : TypeSyntax)
    (extraNodes : Nat)
    (path : DecodePath) :
    decodeTypeSyntaxAt limits (extraNodes + typeSyntaxNodes type) path
        (encodeTypeSyntax type) =
      .ok (type, extraNodes) := by
  cases type with
  | unit span =>
      change (do
        let decodedSpan <-
          decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
        pure (TypeSyntax.unit decodedSpan, extraNodes)) = .ok _
      simp
      rfl
  | named occurrence =>
      change (do
        let (decodedOccurrence, nodes) <-
          decodeTypeSpellingOccurrenceAt limits (extraNodes + 1)
            (path.field "name") (encodeTypeSpellingOccurrence occurrence)
        pure (TypeSyntax.named decodedOccurrence, nodes)) = .ok _
      rw [decodeTypeSpellingOccurrenceAt_encode]
      rfl

private theorem decodeUnaryOperatorAt_encodeUnaryOperator
    (limits : DecodeLimits)
    (operator : UnaryOperator)
    (extraNodes : Nat)
    (path : DecodePath) :
    decodeUnaryOperatorAt limits (extraNodes + 1) path
      (encodeUnaryOperator operator) =
      .ok (operator, extraNodes) := by
  cases operator with
  | mk span operator =>
      change (do
        let decodedSpan <-
          decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
        let decodedOperator <-
          decodeUnaryOpAt (path.field "operator") (encodeUnaryOp operator)
        pure (UnaryOperator.mk decodedSpan decodedOperator,
          extraNodes)) = .ok _
      simp
      rfl

private theorem decodeBinaryOperatorAt_encodeBinaryOperator
    (limits : DecodeLimits)
    (operator : BinaryOperator)
    (extraNodes : Nat)
    (path : DecodePath) :
    decodeBinaryOperatorAt limits (extraNodes + 1) path
      (encodeBinaryOperator operator) =
      .ok (operator, extraNodes) := by
  cases operator with
  | mk span operator =>
      change (do
        let decodedSpan <-
          decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
        let decodedOperator <-
          decodeBinaryOpAt (path.field "operator") (encodeBinaryOp operator)
        pure (BinaryOperator.mk decodedSpan decodedOperator,
          extraNodes)) = .ok _
      simp
      rfl

private theorem decodeCommentAt_encodeComment
    (limits : DecodeLimits)
    (comment : Comment)
    (extraNodes : Nat)
    (path : DecodePath) :
    decodeCommentAt limits (extraNodes + 1) path (encodeComment comment) =
      .ok (comment, extraNodes) := by
  cases comment with
  | mk kind span =>
      change (do
        let decodedKind <-
          decodeCommentKindAt (path.field "kind") (encodeCommentKind kind)
        let decodedSpan <-
          decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
        pure (Comment.mk decodedKind decodedSpan, extraNodes)) = .ok _
      simp
      rfl

private theorem decodeExprAt_encodeUnitStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (span : SourceSpan) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.unit span)) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
      pure (.unit decodedSpan, nodes)) := by
  simp only [encodeExpr]
  rfl

private theorem decodeExprAt_encodeDecimalStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (span : SourceSpan)
    (digits : DecimalDigits) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.integer (.decimal span digits))) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
      let decodedDigits <-
        decodeDecimalDigitsAt (path.field "digits")
          (encodeDecimalDigits digits)
      pure (.integer (.decimal decodedSpan decodedDigits), nodes)) := by
  simp only [encodeExpr]
  rfl

private theorem decodeExprAt_encodeHexadecimalStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (span : SourceSpan)
    (digits : HexadecimalDigits) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.integer (.hexadecimal span digits))) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
      let decodedDigits <-
        decodeHexadecimalDigitsAt (path.field "digits")
          (encodeHexadecimalDigits digits)
      pure (.integer (.hexadecimal decodedSpan decodedDigits), nodes)) := by
  simp only [encodeExpr]
  rfl

private theorem decodeExprAt_encodeNameStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (name : Name) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.name name)) = (do
      let (decodedName, nodes) <-
        decodeNameAt limits nodes (path.field "name") (encodeName name)
      pure (.name decodedName, nodes)) := by
  simp only [encodeExpr]
  rfl

private theorem decodeExprAt_encodeGroupStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (span : SourceSpan)
    (inner : Expr) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.group span inner)) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
      let (decodedInner, nodes) <-
        decodeExprAt limits depth nodes (path.field "inner")
          (encodeExpr inner)
      pure (.group decodedSpan decodedInner, nodes)) := by
  simp only [encodeExpr]
  rfl

private theorem decodeExprAt_encodeCallStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (span : SourceSpan)
    (callee : Name)
    (arguments : List Expr) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.call span callee arguments)) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
      let (decodedCallee, nodes) <-
        decodeNameAt limits nodes (path.field "callee") (encodeName callee)
      let (decodedArguments, nodes) <-
        decodeArrayAt
          (fun nodes argumentPath argumentJson =>
            decodeExprAt limits depth nodes argumentPath argumentJson)
          (path.field "arguments") nodes
          (.arr (arguments.map encodeExpr).toArray)
      pure (.call decodedSpan decodedCallee decodedArguments, nodes)) := by
  simp only [encodeExpr]
  rfl

private theorem decodeExprAt_encodeUnaryStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (span : SourceSpan)
    (operator : UnaryOperator)
    (operand : Expr) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.unary span operator operand)) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
      let (decodedOperator, nodes) <-
        decodeUnaryOperatorAt limits nodes (path.field "operator")
          (encodeUnaryOperator operator)
      let (decodedOperand, nodes) <-
        decodeExprAt limits depth nodes (path.field "operand")
          (encodeExpr operand)
      pure (.unary decodedSpan decodedOperator decodedOperand, nodes)) := by
  simp only [encodeExpr]
  rfl

private theorem decodeExprAt_encodeBinaryStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (span : SourceSpan)
    (operator : BinaryOperator)
    (left right : Expr) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr (.binary span operator left right)) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
      let (decodedOperator, nodes) <-
        decodeBinaryOperatorAt limits nodes (path.field "operator")
          (encodeBinaryOperator operator)
      let (decodedLeft, nodes) <-
        decodeExprAt limits depth nodes (path.field "left") (encodeExpr left)
      let (decodedRight, nodes) <-
        decodeExprAt limits depth nodes (path.field "right") (encodeExpr right)
      pure (.binary decodedSpan decodedOperator decodedLeft decodedRight,
        nodes)) := by
  simp only [encodeExpr]
  rfl

private theorem decodeExprAt_encodeIfThenElseStep
    (limits : DecodeLimits)
    (depth nodes : Nat)
    (path : DecodePath)
    (span : SourceSpan)
    (condition thenBranch elseBranch : Expr) :
    decodeExprAt limits (depth + 1) (nodes + 1) path
        (encodeExpr
          (.ifThenElse span condition thenBranch elseBranch)) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span") (encodeSourceSpan span)
      let (decodedCondition, nodes) <-
        decodeExprAt limits depth nodes (path.field "condition")
          (encodeExpr condition)
      let (decodedThen, nodes) <-
        decodeExprAt limits depth nodes (path.field "thenBranch")
          (encodeExpr thenBranch)
      let (decodedElse, nodes) <-
        decodeExprAt limits depth nodes (path.field "elseBranch")
          (encodeExpr elseBranch)
      pure (.ifThenElse decodedSpan decodedCondition decodedThen decodedElse,
        nodes)) := by
  simp only [encodeExpr]
  rfl

mutual

  private theorem decodeExprAt_encodeExpr
      (limits : DecodeLimits) :
      (expression : Expr) ->
      (extraNodes : Nat) ->
      (path : DecodePath) ->
      (depthBudget : Nat) ->
      exprDepth expression <= depthBudget ->
      decodeExprAt limits depthBudget (extraNodes + exprNodes expression)
          path (encodeExpr expression) =
        .ok (expression, extraNodes)
    | .unit span, extraNodes, path, depthBudget, depthEnough => by
        cases depthBudget with
        | zero => simp [exprDepth] at depthEnough
        | succ depth =>
            rw [show extraNodes + exprNodes (.unit span) =
              extraNodes + 1 by rfl]
            rw [decodeExprAt_encodeUnitStep]
            simp
            rfl
    | .integer (.decimal span digits), extraNodes, path, depthBudget,
        depthEnough => by
        cases depthBudget with
        | zero => simp [exprDepth] at depthEnough
        | succ depth =>
            rw [show extraNodes + exprNodes
              (.integer (.decimal span digits)) = extraNodes + 1 by rfl]
            rw [decodeExprAt_encodeDecimalStep]
            simp
            rfl
    | .integer (.hexadecimal span digits), extraNodes, path, depthBudget,
        depthEnough => by
        cases depthBudget with
        | zero => simp [exprDepth] at depthEnough
        | succ depth =>
            rw [show extraNodes + exprNodes
              (.integer (.hexadecimal span digits)) = extraNodes + 1 by rfl]
            rw [decodeExprAt_encodeHexadecimalStep]
            simp
            rfl
    | .name name, extraNodes, path, depthBudget, depthEnough => by
        cases depthBudget with
        | zero => simp [exprDepth] at depthEnough
        | succ depth =>
            rw [show extraNodes + exprNodes (.name name) =
              (extraNodes + 1) + 1 by simp [exprNodes]]
            rw [decodeExprAt_encodeNameStep]
            rw [decodeNameAt_encodeName]
            rfl
    | .group span inner, extraNodes, path, depthBudget, depthEnough => by
        cases depthBudget with
        | zero => simp [exprDepth] at depthEnough
        | succ depth =>
            have innerDepth : exprDepth inner <= depth := by
              simp [exprDepth] at depthEnough
              omega
            rw [show extraNodes + exprNodes (.group span inner) =
              (extraNodes + exprNodes inner) + 1 by
                simp [exprNodes]
                omega]
            rw [decodeExprAt_encodeGroupStep]
            simp
            rw [decodeExprAt_encodeExpr limits inner extraNodes
              (path.field "inner") depth innerDepth]
            rfl
    | .call span callee arguments, extraNodes, path, depthBudget,
        depthEnough => by
        cases depthBudget with
        | zero => simp [exprDepth] at depthEnough
        | succ depth =>
            have argumentsDepth : exprListDepth arguments <= depth := by
              simp [exprDepth] at depthEnough
              omega
            rw [show extraNodes + exprNodes (.call span callee arguments) =
              ((extraNodes + exprListNodes arguments) + 1) + 1 by
                simp [exprNodes]
                omega]
            rw [decodeExprAt_encodeCallStep]
            simp
            rw [decodeNameAt_encodeName limits callee
              (extraNodes + exprListNodes arguments) (path.field "callee")]
            change (do
              let (decodedArguments, nodes) <-
                decodeListAt
                  (fun nodes argumentPath argumentJson =>
                    decodeExprAt limits depth nodes argumentPath argumentJson)
                  (path.field "arguments") 0
                  (extraNodes + exprListNodes arguments)
                  (arguments.map encodeExpr)
              pure (Expr.call span callee decodedArguments, nodes)) = .ok _
            rw [decodeExprListAt_encodeExprList limits arguments extraNodes
              (path.field "arguments") 0 depth argumentsDepth]
            rfl
    | .unary span operator operand, extraNodes, path, depthBudget,
        depthEnough => by
        cases depthBudget with
        | zero => simp [exprDepth] at depthEnough
        | succ depth =>
            have operandDepth : exprDepth operand <= depth := by
              simp [exprDepth] at depthEnough
              omega
            rw [show extraNodes + exprNodes (.unary span operator operand) =
              ((extraNodes + exprNodes operand) + 1) + 1 by
                simp [exprNodes]
                omega]
            rw [decodeExprAt_encodeUnaryStep]
            simp
            rw [decodeUnaryOperatorAt_encodeUnaryOperator limits operator
              (extraNodes + exprNodes operand) (path.field "operator")]
            change (do
              let (decodedOperand, nodes) <-
                decodeExprAt limits depth
                  (extraNodes + exprNodes operand) (path.field "operand")
                  (encodeExpr operand)
              pure (Expr.unary span operator decodedOperand, nodes)) = .ok _
            rw [decodeExprAt_encodeExpr limits operand extraNodes
              (path.field "operand") depth operandDepth]
            rfl
    | .binary span operator left right, extraNodes, path, depthBudget,
        depthEnough => by
        cases depthBudget with
        | zero => simp [exprDepth] at depthEnough
        | succ depth =>
            have bothDepth :
                Nat.max (exprDepth left) (exprDepth right) <= depth := by
              simpa [exprDepth] using depthEnough
            have leftDepth : exprDepth left <= depth :=
              (Nat.max_le.mp bothDepth).1
            have rightDepth : exprDepth right <= depth :=
              (Nat.max_le.mp bothDepth).2
            rw [show extraNodes +
                exprNodes (.binary span operator left right) =
              ((((extraNodes + exprNodes right) + exprNodes left) + 1) + 1)
                by
                  simp [exprNodes]
                  omega]
            rw [decodeExprAt_encodeBinaryStep]
            simp
            rw [decodeBinaryOperatorAt_encodeBinaryOperator limits operator
              ((extraNodes + exprNodes right) + exprNodes left)
              (path.field "operator")]
            change (do
              let (decodedLeft, nodes) <-
                decodeExprAt limits depth
                  ((extraNodes + exprNodes right) + exprNodes left)
                  (path.field "left") (encodeExpr left)
              let (decodedRight, nodes) <-
                decodeExprAt limits depth nodes (path.field "right")
                  (encodeExpr right)
              pure (Expr.binary span operator decodedLeft decodedRight,
                nodes)) = .ok _
            rw [decodeExprAt_encodeExpr limits left
              (extraNodes + exprNodes right) (path.field "left") depth
              leftDepth]
            change (do
              let (decodedRight, nodes) <-
                decodeExprAt limits depth (extraNodes + exprNodes right)
                  (path.field "right") (encodeExpr right)
              pure (Expr.binary span operator left decodedRight, nodes)) = .ok _
            rw [decodeExprAt_encodeExpr limits right extraNodes
              (path.field "right") depth rightDepth]
            rfl
    | .ifThenElse span condition thenBranch elseBranch, extraNodes, path,
        depthBudget, depthEnough => by
        cases depthBudget with
        | zero => simp [exprDepth] at depthEnough
        | succ depth =>
            have allDepth :
                Nat.max (exprDepth condition)
                  (Nat.max (exprDepth thenBranch) (exprDepth elseBranch)) <=
                    depth := by
              simpa [exprDepth] using depthEnough
            have conditionDepth : exprDepth condition <= depth :=
              (Nat.max_le.mp allDepth).1
            have branchDepth :
                Nat.max (exprDepth thenBranch) (exprDepth elseBranch) <=
                  depth :=
              (Nat.max_le.mp allDepth).2
            have thenDepth : exprDepth thenBranch <= depth :=
              (Nat.max_le.mp branchDepth).1
            have elseDepth : exprDepth elseBranch <= depth :=
              (Nat.max_le.mp branchDepth).2
            rw [show extraNodes + exprNodes
                (.ifThenElse span condition thenBranch elseBranch) =
              (((extraNodes + exprNodes elseBranch) +
                exprNodes thenBranch) + exprNodes condition) + 1 by
                  simp [exprNodes]
                  omega]
            rw [decodeExprAt_encodeIfThenElseStep]
            simp
            rw [decodeExprAt_encodeExpr limits condition
              ((extraNodes + exprNodes elseBranch) + exprNodes thenBranch)
              (path.field "condition") depth conditionDepth]
            change (do
              let (decodedThen, nodes) <-
                decodeExprAt limits depth
                  ((extraNodes + exprNodes elseBranch) + exprNodes thenBranch)
                  (path.field "thenBranch") (encodeExpr thenBranch)
              let (decodedElse, nodes) <-
                decodeExprAt limits depth nodes (path.field "elseBranch")
                  (encodeExpr elseBranch)
              pure (Expr.ifThenElse span condition decodedThen decodedElse,
                nodes)) = .ok _
            rw [decodeExprAt_encodeExpr limits thenBranch
              (extraNodes + exprNodes elseBranch) (path.field "thenBranch")
              depth thenDepth]
            change (do
              let (decodedElse, nodes) <-
                decodeExprAt limits depth (extraNodes + exprNodes elseBranch)
                  (path.field "elseBranch") (encodeExpr elseBranch)
              pure (Expr.ifThenElse span condition thenBranch decodedElse,
                nodes)) = .ok _
            rw [decodeExprAt_encodeExpr limits elseBranch extraNodes
              (path.field "elseBranch") depth elseDepth]
            rfl

  private theorem decodeExprListAt_encodeExprList
      (limits : DecodeLimits) :
      (expressions : List Expr) ->
      (extraNodes : Nat) ->
      (path : DecodePath) ->
      (index : Nat) ->
      (depthBudget : Nat) ->
      exprListDepth expressions <= depthBudget ->
      decodeListAt
          (fun nodes expressionPath json =>
            decodeExprAt limits depthBudget nodes expressionPath json)
          path index (extraNodes + exprListNodes expressions)
          (expressions.map encodeExpr) =
        .ok (expressions, extraNodes)
    | [], extraNodes, _, _, _, _ => by
        rfl
    | expression :: rest, extraNodes, path, index, depthBudget,
        depthEnough => by
        have bothDepth :
            Nat.max (exprDepth expression) (exprListDepth rest) <=
              depthBudget := by
          simpa [exprListDepth] using depthEnough
        have expressionDepth : exprDepth expression <= depthBudget :=
          (Nat.max_le.mp bothDepth).1
        have restDepth : exprListDepth rest <= depthBudget :=
          (Nat.max_le.mp bothDepth).2
        rw [show extraNodes + exprListNodes (expression :: rest) =
          (extraNodes + exprListNodes rest) + exprNodes expression by
            simp [exprListNodes]
            omega]
        change (do
          let (decodedExpression, nodes) <-
            decodeExprAt limits depthBudget
              ((extraNodes + exprListNodes rest) + exprNodes expression)
              (path.index index) (encodeExpr expression)
          let (decodedRest, nodes) <-
            decodeListAt
              (fun nodes expressionPath json =>
                decodeExprAt limits depthBudget nodes expressionPath json)
              path (index + 1) nodes (rest.map encodeExpr)
          pure (decodedExpression :: decodedRest, nodes)) = .ok _
        rw [decodeExprAt_encodeExpr limits expression
          (extraNodes + exprListNodes rest) (path.index index) depthBudget
          expressionDepth]
        change (do
          let (decodedRest, nodes) <-
            decodeListAt
              (fun nodes expressionPath json =>
                decodeExprAt limits depthBudget nodes expressionPath json)
              path (index + 1) (extraNodes + exprListNodes rest)
              (rest.map encodeExpr)
          pure (expression :: decodedRest, nodes)) = .ok _
        rw [decodeExprListAt_encodeExprList limits rest extraNodes path
          (index + 1) depthBudget restDepth]
        simp
        rfl

end

private theorem decodeLetStatementAt_encodeStep
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (statement : LetStatement) :
    decodeLetStatementAt limits (nodes + 1) path
        (encodeLetStatement statement) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span")
          (encodeSourceSpan statement.span)
      let (decodedName, nodes) <-
        decodeNameAt limits nodes (path.field "name")
          (encodeName statement.name)
      let (decodedType, nodes) <-
        decodeTypeSyntaxAt limits nodes (path.field "type")
          (encodeTypeSyntax statement.type)
      let (decodedValue, nodes) <-
        decodeExprAt limits limits.maxDepth nodes (path.field "value")
          (encodeExpr statement.value)
      pure (LetStatement.mk decodedSpan decodedName decodedType decodedValue,
        nodes)) := by
  simp only [encodeLetStatement]
  rfl

private theorem decodeReturnStatementAt_encodeStep
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (statement : ReturnStatement) :
    decodeReturnStatementAt limits (nodes + 1) path
        (encodeReturnStatement statement) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span")
          (encodeSourceSpan statement.span)
      let (decodedValue, nodes) <-
        decodeExprAt limits limits.maxDepth nodes (path.field "value")
          (encodeExpr statement.value)
      pure (ReturnStatement.mk decodedSpan decodedValue, nodes)) := by
  simp only [encodeReturnStatement]
  rfl

private theorem decodeFunctionDeclAt_encodeStep
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (declaration : FunctionDecl) :
    decodeFunctionDeclAt limits (nodes + 1) path
        (encodeFunctionDecl declaration) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span")
          (encodeSourceSpan declaration.span)
      let (decodedName, nodes) <-
        decodeNameAt limits nodes (path.field "name")
          (encodeName declaration.name)
      let (decodedReturnType, nodes) <-
        decodeTypeSyntaxAt limits nodes (path.field "returnType")
          (encodeTypeSyntax declaration.returnType)
      let (decodedBindings, nodes) <-
        decodeArrayAt
          (fun nodes bindingPath bindingJson =>
            decodeLetStatementAt limits nodes bindingPath bindingJson)
          (path.field "bindings") nodes
          (.arr (declaration.bindings.map encodeLetStatement).toArray)
      let (decodedResult, nodes) <-
        decodeReturnStatementAt limits nodes (path.field "result")
          (encodeReturnStatement declaration.result)
      pure (FunctionDecl.mk decodedSpan decodedName decodedReturnType
        decodedBindings decodedResult, nodes)) := by
  simp only [encodeFunctionDecl]
  rfl

private theorem decodeFileWithBudgetAt_encodeStep
    (limits : DecodeLimits)
    (nodes : Nat)
    (path : DecodePath)
    (file : File) :
    decodeFileWithBudgetAt limits (nodes + 1) path (encodeFile file) = (do
      let decodedSpan <-
        decodeSourceSpanAt (path.field "span") (encodeSourceSpan file.span)
      let (decodedFunction, nodes) <-
        decodeFunctionDeclAt limits nodes (path.field "function")
          (encodeFunctionDecl file.function)
      let (decodedComments, nodes) <-
        decodeArrayAt
          (fun nodes commentPath commentJson =>
            decodeCommentAt limits nodes commentPath commentJson)
          (path.field "comments") nodes
          (.arr (file.comments.map encodeComment).toArray)
      pure (File.mk decodedSpan decodedFunction decodedComments, nodes)) := by
  simp only [encodeFile, schemaVersion]
  rfl

private theorem decodeLetStatementAt_encodeLetStatement
    (limits : DecodeLimits)
    (statement : LetStatement)
    (extraNodes : Nat)
    (path : DecodePath)
    (depthEnough : exprDepth statement.value <= limits.maxDepth) :
    decodeLetStatementAt limits
        (extraNodes + letStatementNodes statement) path
        (encodeLetStatement statement) =
      .ok (statement, extraNodes) := by
  cases statement with
  | mk span name type value =>
      rw [show extraNodes + letStatementNodes
          (LetStatement.mk span name type value) =
        ((((extraNodes + exprNodes value) + typeSyntaxNodes type) + 1) + 1)
          by
            simp [letStatementNodes]
            omega]
      rw [decodeLetStatementAt_encodeStep]
      simp
      rw [decodeNameAt_encodeName limits name
        ((extraNodes + exprNodes value) + typeSyntaxNodes type)
        (path.field "name")]
      change (do
        let (decodedType, nodes) <-
          decodeTypeSyntaxAt limits
            ((extraNodes + exprNodes value) + typeSyntaxNodes type)
            (path.field "type") (encodeTypeSyntax type)
        let (decodedValue, nodes) <-
          decodeExprAt limits limits.maxDepth nodes (path.field "value")
            (encodeExpr value)
        pure (LetStatement.mk span name decodedType decodedValue,
          nodes)) = .ok _
      rw [decodeTypeSyntaxAt_encodeTypeSyntax limits type
        (extraNodes + exprNodes value) (path.field "type")]
      change (do
        let (decodedValue, nodes) <-
          decodeExprAt limits limits.maxDepth (extraNodes + exprNodes value)
            (path.field "value") (encodeExpr value)
        pure (LetStatement.mk span name type decodedValue, nodes)) = .ok _
      rw [decodeExprAt_encodeExpr limits value extraNodes
        (path.field "value") limits.maxDepth depthEnough]
      rfl

private theorem decodeReturnStatementAt_encodeReturnStatement
    (limits : DecodeLimits)
    (statement : ReturnStatement)
    (extraNodes : Nat)
    (path : DecodePath)
    (depthEnough : exprDepth statement.value <= limits.maxDepth) :
    decodeReturnStatementAt limits
        (extraNodes + returnStatementNodes statement) path
        (encodeReturnStatement statement) =
      .ok (statement, extraNodes) := by
  cases statement with
  | mk span value =>
      rw [show extraNodes + returnStatementNodes
          (ReturnStatement.mk span value) =
        (extraNodes + exprNodes value) + 1 by
          simp [returnStatementNodes]
          omega]
      rw [decodeReturnStatementAt_encodeStep]
      simp
      rw [decodeExprAt_encodeExpr limits value extraNodes
        (path.field "value") limits.maxDepth depthEnough]
      rfl

private theorem decodeLetStatementListAt_encode
    (limits : DecodeLimits) :
    (statements : List LetStatement) ->
    (extraNodes : Nat) ->
    (path : DecodePath) ->
    (index : Nat) ->
    letStatementListDepth statements <= limits.maxDepth ->
    decodeListAt
        (fun nodes statementPath json =>
          decodeLetStatementAt limits nodes statementPath json)
        path index (extraNodes + letStatementListNodes statements)
        (statements.map encodeLetStatement) =
      .ok (statements, extraNodes)
  | [], _, _, _, _ => by
      rfl
  | statement :: rest, extraNodes, path, index, depthEnough => by
      have bothDepth :
          Nat.max (exprDepth statement.value)
            (letStatementListDepth rest) <= limits.maxDepth := by
        simpa [letStatementListDepth] using depthEnough
      have statementDepth :
          exprDepth statement.value <= limits.maxDepth :=
        (Nat.max_le.mp bothDepth).1
      have restDepth :
          letStatementListDepth rest <= limits.maxDepth :=
        (Nat.max_le.mp bothDepth).2
      rw [show extraNodes +
          letStatementListNodes (statement :: rest) =
        (extraNodes + letStatementListNodes rest) +
          letStatementNodes statement by
            simp [letStatementListNodes]
            omega]
      change (do
        let (decodedStatement, nodes) <-
          decodeLetStatementAt limits
            ((extraNodes + letStatementListNodes rest) +
              letStatementNodes statement)
            (path.index index) (encodeLetStatement statement)
        let (decodedRest, nodes) <-
          decodeListAt
            (fun nodes statementPath json =>
              decodeLetStatementAt limits nodes statementPath json)
            path (index + 1) nodes (rest.map encodeLetStatement)
        pure (decodedStatement :: decodedRest, nodes)) = .ok _
      rw [decodeLetStatementAt_encodeLetStatement limits statement
        (extraNodes + letStatementListNodes rest) (path.index index)
        statementDepth]
      change (do
        let (decodedRest, nodes) <-
          decodeListAt
            (fun nodes statementPath json =>
              decodeLetStatementAt limits nodes statementPath json)
            path (index + 1) (extraNodes + letStatementListNodes rest)
            (rest.map encodeLetStatement)
        pure (statement :: decodedRest, nodes)) = .ok _
      rw [decodeLetStatementListAt_encode limits rest extraNodes path
        (index + 1) restDepth]
      rfl

private theorem decodeFunctionDeclAt_encodeFunctionDecl
    (limits : DecodeLimits)
    (declaration : FunctionDecl)
    (extraNodes : Nat)
    (path : DecodePath)
    (depthEnough : functionDeclDepth declaration <= limits.maxDepth) :
    decodeFunctionDeclAt limits
        (extraNodes + functionDeclNodes declaration) path
        (encodeFunctionDecl declaration) =
      .ok (declaration, extraNodes) := by
  cases declaration with
  | mk span name returnType bindings result =>
      have bothDepth :
          Nat.max (letStatementListDepth bindings)
            (exprDepth result.value) <= limits.maxDepth := by
        simpa [functionDeclDepth] using depthEnough
      have bindingsDepth :
          letStatementListDepth bindings <= limits.maxDepth :=
        (Nat.max_le.mp bothDepth).1
      have resultDepth : exprDepth result.value <= limits.maxDepth :=
        (Nat.max_le.mp bothDepth).2
      rw [show extraNodes + functionDeclNodes
          (FunctionDecl.mk span name returnType bindings result) =
        (((((extraNodes + returnStatementNodes result) +
          letStatementListNodes bindings) + typeSyntaxNodes returnType) + 1) + 1)
            by
              simp [functionDeclNodes]
              omega]
      rw [decodeFunctionDeclAt_encodeStep]
      simp
      rw [decodeNameAt_encodeName limits name
        (((extraNodes + returnStatementNodes result) +
          letStatementListNodes bindings) + typeSyntaxNodes returnType)
        (path.field "name")]
      change (do
        let (decodedReturnType, nodes) <-
          decodeTypeSyntaxAt limits
            (((extraNodes + returnStatementNodes result) +
              letStatementListNodes bindings) +
                typeSyntaxNodes returnType)
            (path.field "returnType") (encodeTypeSyntax returnType)
        let (decodedBindings, nodes) <-
          decodeArrayAt
            (fun nodes bindingPath bindingJson =>
              decodeLetStatementAt limits nodes bindingPath bindingJson)
            (path.field "bindings") nodes
            (.arr (bindings.map encodeLetStatement).toArray)
        let (decodedResult, nodes) <-
          decodeReturnStatementAt limits nodes (path.field "result")
            (encodeReturnStatement result)
        pure (FunctionDecl.mk span name decodedReturnType decodedBindings
          decodedResult, nodes)) = .ok _
      rw [decodeTypeSyntaxAt_encodeTypeSyntax limits returnType
        ((extraNodes + returnStatementNodes result) +
          letStatementListNodes bindings) (path.field "returnType")]
      change (do
        let (decodedBindings, nodes) <-
          decodeListAt
            (fun nodes bindingPath bindingJson =>
              decodeLetStatementAt limits nodes bindingPath bindingJson)
            (path.field "bindings") 0
            ((extraNodes + returnStatementNodes result) +
              letStatementListNodes bindings)
            (bindings.map encodeLetStatement)
        let (decodedResult, nodes) <-
          decodeReturnStatementAt limits nodes (path.field "result")
            (encodeReturnStatement result)
        pure (FunctionDecl.mk span name returnType decodedBindings
          decodedResult, nodes)) = .ok _
      rw [decodeLetStatementListAt_encode limits bindings
        (extraNodes + returnStatementNodes result) (path.field "bindings") 0
        bindingsDepth]
      change (do
        let (decodedResult, nodes) <-
          decodeReturnStatementAt limits
            (extraNodes + returnStatementNodes result)
            (path.field "result") (encodeReturnStatement result)
        pure (FunctionDecl.mk span name returnType bindings decodedResult,
          nodes)) = .ok _
      rw [decodeReturnStatementAt_encodeReturnStatement limits result
        extraNodes (path.field "result") resultDepth]
      rfl

private theorem decodeCommentListAt_encode
    (limits : DecodeLimits) :
    (comments : List Comment) ->
    (extraNodes : Nat) ->
    (path : DecodePath) ->
    (index : Nat) ->
    decodeListAt
        (fun nodes commentPath json =>
          decodeCommentAt limits nodes commentPath json)
        path index (extraNodes + comments.length)
        (comments.map encodeComment) =
      .ok (comments, extraNodes)
  | [], _, _, _ => by
      rfl
  | comment :: rest, extraNodes, path, index => by
      rw [show extraNodes + (comment :: rest).length =
        (extraNodes + rest.length) + 1 by
          simp
          omega]
      change (do
        let (decodedComment, nodes) <-
          decodeCommentAt limits ((extraNodes + rest.length) + 1)
            (path.index index) (encodeComment comment)
        let (decodedRest, nodes) <-
          decodeListAt
            (fun nodes commentPath json =>
              decodeCommentAt limits nodes commentPath json)
            path (index + 1) nodes (rest.map encodeComment)
        pure (decodedComment :: decodedRest, nodes)) = .ok _
      rw [decodeCommentAt_encodeComment limits comment
        (extraNodes + rest.length) (path.index index)]
      change (do
        let (decodedRest, nodes) <-
          decodeListAt
            (fun nodes commentPath json =>
              decodeCommentAt limits nodes commentPath json)
            path (index + 1) (extraNodes + rest.length)
            (rest.map encodeComment)
        pure (comment :: decodedRest, nodes)) = .ok _
      rw [decodeCommentListAt_encode limits rest extraNodes path (index + 1)]
      rfl

private theorem decodeFileWithBudgetAt_encodeFile
    (limits : DecodeLimits)
    (file : File)
    (extraNodes : Nat)
    (path : DecodePath)
    (depthEnough : fileDepth file <= limits.maxDepth) :
    decodeFileWithBudgetAt limits (extraNodes + fileNodes file) path
        (encodeFile file) =
      .ok (file, extraNodes) := by
  cases file with
  | mk span function comments =>
      have functionDepth :
          functionDeclDepth function <= limits.maxDepth := by
        simpa [fileDepth] using depthEnough
      rw [show extraNodes + fileNodes (File.mk span function comments) =
        ((extraNodes + comments.length) + functionDeclNodes function) + 1 by
          simp [fileNodes]
          omega]
      rw [decodeFileWithBudgetAt_encodeStep]
      simp
      rw [decodeFunctionDeclAt_encodeFunctionDecl limits function
        (extraNodes + comments.length) (path.field "function")
        functionDepth]
      change (do
        let (decodedComments, nodes) <-
          decodeListAt
            (fun nodes commentPath commentJson =>
              decodeCommentAt limits nodes commentPath commentJson)
            (path.field "comments") 0 (extraNodes + comments.length)
            (comments.map encodeComment)
        pure (File.mk span function decodedComments, nodes)) = .ok _
      rw [decodeCommentListAt_encode limits comments extraNodes
        (path.field "comments") 0]
      rfl

theorem decodeExpr_encodeExpr
    (limits : DecodeLimits)
    (expression : Expr)
    (depthEnough : exprDepth expression <= limits.maxDepth)
    (nodesEnough : exprNodes expression <= limits.maxNodes) :
    decodeExpr limits (encodeExpr expression) = .ok expression := by
  rw [decodeExpr]
  have nodesEquation :
      limits.maxNodes =
        (limits.maxNodes - exprNodes expression) + exprNodes expression := by
    omega
  rw [nodesEquation]
  rw [decodeExprAt_encodeExpr limits expression
    (limits.maxNodes - exprNodes expression) .root limits.maxDepth
    depthEnough]
  rfl

@[simp] theorem decodeIdentifierText_encodeIdentifierText
    (text : IdentifierText) :
    decodeIdentifierText (encodeIdentifierText text) = .ok text :=
  decodeIdentifierTextAt_encodeIdentifierText .root text

@[simp] theorem decodeDecimalDigits_encodeDecimalDigits
    (digits : DecimalDigits) :
    decodeDecimalDigits (encodeDecimalDigits digits) = .ok digits :=
  decodeDecimalDigitsAt_encodeDecimalDigits .root digits

@[simp] theorem decodeHexadecimalDigits_encodeHexadecimalDigits
    (digits : HexadecimalDigits) :
    decodeHexadecimalDigits (encodeHexadecimalDigits digits) = .ok digits :=
  decodeHexadecimalDigitsAt_encodeHexadecimalDigits .root digits

@[simp] theorem decodeSourceSpan_encodeSourceSpan
    (span : SourceSpan) :
    decodeSourceSpan (encodeSourceSpan span) = .ok span :=
  decodeSourceSpanAt_encodeSourceSpan .root span

@[simp] theorem decodeTypeSpelling_encodeTypeSpelling
    (spelling : TypeSpelling) :
    decodeTypeSpelling (encodeTypeSpelling spelling) = .ok spelling :=
  decodeTypeSpellingAt_encodeTypeSpelling .root spelling

@[simp] theorem decodeIntegerLiteral_encodeIntegerLiteral
    (literal : IntegerLiteral) :
    decodeIntegerLiteral (encodeIntegerLiteral literal) = .ok literal :=
  decodeIntegerLiteralAt_encodeIntegerLiteral .root literal

@[simp] theorem decodeUnaryOp_encodeUnaryOp
    (operator : UnaryOp) :
    decodeUnaryOp (encodeUnaryOp operator) = .ok operator :=
  decodeUnaryOpAt_encodeUnaryOp .root operator

@[simp] theorem decodeBinaryOp_encodeBinaryOp
    (operator : BinaryOp) :
    decodeBinaryOp (encodeBinaryOp operator) = .ok operator :=
  decodeBinaryOpAt_encodeBinaryOp .root operator

@[simp] theorem decodeCommentKind_encodeCommentKind
    (kind : CommentKind) :
    decodeCommentKind (encodeCommentKind kind) = .ok kind :=
  decodeCommentKindAt_encodeCommentKind .root kind

theorem decodeName_encodeName
    (limits : DecodeLimits)
    (name : Name)
    (nodesEnough : 1 <= limits.maxNodes) :
    decodeName limits (encodeName name) = .ok name := by
  rw [decodeName]
  have nodesEquation :
      limits.maxNodes = (limits.maxNodes - 1) + 1 := by
    omega
  rw [nodesEquation]
  rw [decodeNameAt_encodeName limits name (limits.maxNodes - 1) .root]
  rfl

theorem decodeTypeSpellingOccurrence_encodeTypeSpellingOccurrence
    (limits : DecodeLimits)
    (occurrence : TypeSpellingOccurrence)
    (nodesEnough : 1 <= limits.maxNodes) :
    decodeTypeSpellingOccurrence limits
        (encodeTypeSpellingOccurrence occurrence) =
      .ok occurrence := by
  rw [decodeTypeSpellingOccurrence]
  have nodesEquation :
      limits.maxNodes = (limits.maxNodes - 1) + 1 := by
    omega
  rw [nodesEquation]
  rw [decodeTypeSpellingOccurrenceAt_encode limits occurrence
    (limits.maxNodes - 1) .root]
  rfl

theorem decodeTypeSyntax_encodeTypeSyntax
    (limits : DecodeLimits)
    (type : TypeSyntax)
    (nodesEnough : typeSyntaxNodes type <= limits.maxNodes) :
    decodeTypeSyntax limits (encodeTypeSyntax type) = .ok type := by
  rw [decodeTypeSyntax]
  have nodesEquation :
      limits.maxNodes =
        (limits.maxNodes - typeSyntaxNodes type) + typeSyntaxNodes type := by
    omega
  rw [nodesEquation]
  rw [decodeTypeSyntaxAt_encodeTypeSyntax limits type
    (limits.maxNodes - typeSyntaxNodes type) .root]
  rfl

theorem decodeUnaryOperator_encodeUnaryOperator
    (limits : DecodeLimits)
    (operator : UnaryOperator)
    (nodesEnough : 1 <= limits.maxNodes) :
    decodeUnaryOperator limits (encodeUnaryOperator operator) =
      .ok operator := by
  rw [decodeUnaryOperator]
  have nodesEquation :
      limits.maxNodes = (limits.maxNodes - 1) + 1 := by
    omega
  rw [nodesEquation]
  rw [decodeUnaryOperatorAt_encodeUnaryOperator limits operator
    (limits.maxNodes - 1) .root]
  rfl

theorem decodeBinaryOperator_encodeBinaryOperator
    (limits : DecodeLimits)
    (operator : BinaryOperator)
    (nodesEnough : 1 <= limits.maxNodes) :
    decodeBinaryOperator limits (encodeBinaryOperator operator) =
      .ok operator := by
  rw [decodeBinaryOperator]
  have nodesEquation :
      limits.maxNodes = (limits.maxNodes - 1) + 1 := by
    omega
  rw [nodesEquation]
  rw [decodeBinaryOperatorAt_encodeBinaryOperator limits operator
    (limits.maxNodes - 1) .root]
  rfl

theorem decodeLetStatement_encodeLetStatement
    (limits : DecodeLimits)
    (statement : LetStatement)
    (depthEnough : exprDepth statement.value <= limits.maxDepth)
    (nodesEnough : letStatementNodes statement <= limits.maxNodes) :
    decodeLetStatement limits (encodeLetStatement statement) =
      .ok statement := by
  rw [decodeLetStatement]
  have nodesEquation :
      limits.maxNodes =
        (limits.maxNodes - letStatementNodes statement) +
          letStatementNodes statement := by
    omega
  rw [nodesEquation]
  rw [decodeLetStatementAt_encodeLetStatement limits statement
    (limits.maxNodes - letStatementNodes statement) .root depthEnough]
  rfl

theorem decodeReturnStatement_encodeReturnStatement
    (limits : DecodeLimits)
    (statement : ReturnStatement)
    (depthEnough : exprDepth statement.value <= limits.maxDepth)
    (nodesEnough : returnStatementNodes statement <= limits.maxNodes) :
    decodeReturnStatement limits (encodeReturnStatement statement) =
      .ok statement := by
  rw [decodeReturnStatement]
  have nodesEquation :
      limits.maxNodes =
        (limits.maxNodes - returnStatementNodes statement) +
          returnStatementNodes statement := by
    omega
  rw [nodesEquation]
  rw [decodeReturnStatementAt_encodeReturnStatement limits statement
    (limits.maxNodes - returnStatementNodes statement) .root depthEnough]
  rfl

theorem decodeFunctionDecl_encodeFunctionDecl
    (limits : DecodeLimits)
    (declaration : FunctionDecl)
    (depthEnough : functionDeclDepth declaration <= limits.maxDepth)
    (nodesEnough : functionDeclNodes declaration <= limits.maxNodes) :
    decodeFunctionDecl limits (encodeFunctionDecl declaration) =
      .ok declaration := by
  rw [decodeFunctionDecl]
  have nodesEquation :
      limits.maxNodes =
        (limits.maxNodes - functionDeclNodes declaration) +
          functionDeclNodes declaration := by
    omega
  rw [nodesEquation]
  rw [decodeFunctionDeclAt_encodeFunctionDecl limits declaration
    (limits.maxNodes - functionDeclNodes declaration) .root depthEnough]
  rfl

theorem decodeComment_encodeComment
    (limits : DecodeLimits)
    (comment : Comment)
    (nodesEnough : 1 <= limits.maxNodes) :
    decodeComment limits (encodeComment comment) = .ok comment := by
  rw [decodeComment]
  have nodesEquation :
      limits.maxNodes = (limits.maxNodes - 1) + 1 := by
    omega
  rw [nodesEquation]
  rw [decodeCommentAt_encodeComment limits comment
    (limits.maxNodes - 1) .root]
  rfl

theorem decodeFileAt_encodeFile
    (limits : DecodeLimits)
    (path : DecodePath)
    (file : File)
    (depthEnough : fileDepth file <= limits.maxDepth)
    (nodesEnough : fileNodes file <= limits.maxNodes) :
    decodeFileAt limits path (encodeFile file) = .ok file := by
  rw [decodeFileAt]
  have nodesEquation :
      limits.maxNodes =
        (limits.maxNodes - fileNodes file) + fileNodes file := by
    omega
  rw [nodesEquation]
  rw [decodeFileWithBudgetAt_encodeFile limits file
    (limits.maxNodes - fileNodes file) path depthEnough]
  rfl

theorem decodeFile_encodeFile
    (limits : DecodeLimits)
    (file : File)
    (depthEnough : fileDepth file <= limits.maxDepth)
    (nodesEnough : fileNodes file <= limits.maxNodes) :
    decodeFile limits (encodeFile file) = .ok file := by
  exact decodeFileAt_encodeFile limits .root file depthEnough nodesEnough

def canonicalizeFile
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult Lean.Json :=
  encodeFile <$> decodeFile limits json

theorem canonicalizeFile_encodeFile
    (limits : DecodeLimits)
    (file : File)
    (depthEnough : fileDepth file <= limits.maxDepth)
    (nodesEnough : fileNodes file <= limits.maxNodes) :
    canonicalizeFile limits (encodeFile file) = .ok (encodeFile file) := by
  simp [canonicalizeFile,
    decodeFile_encodeFile limits file depthEnough nodesEnough]
  rfl

theorem canonicalizeFile_idempotent
    (limits : DecodeLimits)
    (json : Lean.Json)
    (file : File)
    (decoded : decodeFile limits json = .ok file)
    (depthEnough : fileDepth file <= limits.maxDepth)
    (nodesEnough : fileNodes file <= limits.maxNodes) :
    canonicalizeFile limits json >>= canonicalizeFile limits =
      canonicalizeFile limits json := by
  simp [canonicalizeFile, decoded]
  exact canonicalizeFile_encodeFile limits file depthEnough nodesEnough

end Solcore.Surface.Wire.V1
