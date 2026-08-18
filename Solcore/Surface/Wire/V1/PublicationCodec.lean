import Solcore.Surface.Wire.V1.Codec
import Solcore.Surface.Wire.V1.Diagnostic
import Solcore.Surface.Wire.V1.ParseResult

set_option autoImplicit false

namespace Solcore.Surface.Wire.V1

/-!
Canonical JSON codecs for the closed diagnostic and parse-result publication
values.  The decoders share the Surface codec's path representation and exact
object checks so every failure identifies the rejected JSON location.
-/

private def invalidTagAt {α : Type}
    (path : DecodePath)
    (actual : String)
    (allowed : Array Lean.Json) :
    DecodeResult α :=
  failAt path .invalidTag (.mkObj [
    ("actual", actual),
    ("allowed", .arr allowed)
  ])

private def requireLiteralAt
    (path : DecodePath)
    (json : Lean.Json)
    (expected : String) :
    DecodeResult Unit := do
  let actual <- decodeStringAt path json
  unless actual == expected do
    invalidTagAt path actual #[expected]

def encodeTokenKind : TokenKind -> Lean.Json
  | .keywordFunction => .mkObj [("kind", "keywordFunction")]
  | .keywordLet => .mkObj [("kind", "keywordLet")]
  | .keywordIf => .mkObj [("kind", "keywordIf")]
  | .keywordElse => .mkObj [("kind", "keywordElse")]
  | .keywordReturn => .mkObj [("kind", "keywordReturn")]
  | .identifier text => .mkObj [
      ("kind", "identifier"),
      ("text", encodeIdentifierText text)
    ]
  | .decimal digits => .mkObj [
      ("kind", "decimal"),
      ("digits", encodeDecimalDigits digits)
    ]
  | .hexadecimal digits => .mkObj [
      ("kind", "hexadecimal"),
      ("digits", encodeHexadecimalDigits digits)
    ]
  | .arrow => .mkObj [("kind", "arrow")]
  | .equal => .mkObj [("kind", "equal")]
  | .equalEqual => .mkObj [("kind", "equalEqual")]
  | .bang => .mkObj [("kind", "bang")]
  | .bangEqual => .mkObj [("kind", "bangEqual")]
  | .less => .mkObj [("kind", "less")]
  | .lessEqual => .mkObj [("kind", "lessEqual")]
  | .greater => .mkObj [("kind", "greater")]
  | .greaterEqual => .mkObj [("kind", "greaterEqual")]
  | .plus => .mkObj [("kind", "plus")]
  | .minus => .mkObj [("kind", "minus")]
  | .star => .mkObj [("kind", "star")]
  | .slash => .mkObj [("kind", "slash")]
  | .percent => .mkObj [("kind", "percent")]
  | .ampersand => .mkObj [("kind", "ampersand")]
  | .caret => .mkObj [("kind", "caret")]
  | .pipe => .mkObj [("kind", "pipe")]
  | .leftParen => .mkObj [("kind", "leftParen")]
  | .rightParen => .mkObj [("kind", "rightParen")]
  | .leftBrace => .mkObj [("kind", "leftBrace")]
  | .rightBrace => .mkObj [("kind", "rightBrace")]
  | .colon => .mkObj [("kind", "colon")]
  | .semicolon => .mkObj [("kind", "semicolon")]
  | .comma => .mkObj [("kind", "comma")]

def decodeTokenKindAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult TokenKind := do
  ensureExactObject path json ["kind", "text", "digits"] ["kind"]
  let kindPath := path.field "kind"
  let kind <- decodeStringAt kindPath (← requireField path json "kind")
  match kind with
  | "identifier" =>
      ensureExactObject path json ["kind", "text"] ["kind", "text"]
      let textPath := path.field "text"
      pure (.identifier
        (← decodeIdentifierTextAt textPath (← requireField path json "text")))
  | "decimal" =>
      ensureExactObject path json ["kind", "digits"] ["kind", "digits"]
      let digitsPath := path.field "digits"
      pure (.decimal
        (← decodeDecimalDigitsAt digitsPath (← requireField path json "digits")))
  | "hexadecimal" =>
      ensureExactObject path json ["kind", "digits"] ["kind", "digits"]
      let digitsPath := path.field "digits"
      pure (.hexadecimal
        (← decodeHexadecimalDigitsAt digitsPath
          (← requireField path json "digits")))
  | "keywordFunction" => simple .keywordFunction
  | "keywordLet" => simple .keywordLet
  | "keywordIf" => simple .keywordIf
  | "keywordElse" => simple .keywordElse
  | "keywordReturn" => simple .keywordReturn
  | "arrow" => simple .arrow
  | "equal" => simple .equal
  | "equalEqual" => simple .equalEqual
  | "bang" => simple .bang
  | "bangEqual" => simple .bangEqual
  | "less" => simple .less
  | "lessEqual" => simple .lessEqual
  | "greater" => simple .greater
  | "greaterEqual" => simple .greaterEqual
  | "plus" => simple .plus
  | "minus" => simple .minus
  | "star" => simple .star
  | "slash" => simple .slash
  | "percent" => simple .percent
  | "ampersand" => simple .ampersand
  | "caret" => simple .caret
  | "pipe" => simple .pipe
  | "leftParen" => simple .leftParen
  | "rightParen" => simple .rightParen
  | "leftBrace" => simple .leftBrace
  | "rightBrace" => simple .rightBrace
  | "colon" => simple .colon
  | "semicolon" => simple .semicolon
  | "comma" => simple .comma
  | _ =>
      invalidTagAt kindPath kind #[
        "keywordFunction", "keywordLet", "keywordIf", "keywordElse",
        "keywordReturn", "identifier", "decimal", "hexadecimal", "arrow",
        "equal", "equalEqual", "bang", "bangEqual", "less", "lessEqual",
        "greater", "greaterEqual", "plus", "minus", "star", "slash",
        "percent", "ampersand", "caret", "pipe", "leftParen",
        "rightParen", "leftBrace", "rightBrace", "colon", "semicolon",
        "comma"
      ]
where
  simple (value : TokenKind) : DecodeResult TokenKind := do
    ensureExactObject path json ["kind"] ["kind"]
    pure value

def decodeTokenKind (json : Lean.Json) : DecodeResult TokenKind :=
  decodeTokenKindAt .root json

def encodeParseExpectation : ParseExpectation -> Lean.Json
  | .token token => .mkObj [
      ("kind", "token"),
      ("token", encodeTokenKind token)
    ]
  | .identifier => .mkObj [("kind", "identifier")]
  | .type => .mkObj [("kind", "type")]
  | .expression => .mkObj [("kind", "expression")]
  | .argumentOrRightParen => .mkObj [("kind", "argumentOrRightParen")]
  | .commaOrRightParen => .mkObj [("kind", "commaOrRightParen")]
  | .bindingOrReturn => .mkObj [("kind", "bindingOrReturn")]
  | .endOfFile => .mkObj [("kind", "endOfFile")]

def decodeParseExpectationAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult ParseExpectation := do
  ensureExactObject path json ["kind", "token"] ["kind"]
  let kindPath := path.field "kind"
  let kind <- decodeStringAt kindPath (← requireField path json "kind")
  match kind with
  | "token" =>
      ensureExactObject path json ["kind", "token"] ["kind", "token"]
      let tokenPath := path.field "token"
      pure (.token
        (← decodeTokenKindAt tokenPath (← requireField path json "token")))
  | "identifier" => simple .identifier
  | "type" => simple .type
  | "expression" => simple .expression
  | "argumentOrRightParen" => simple .argumentOrRightParen
  | "commaOrRightParen" => simple .commaOrRightParen
  | "bindingOrReturn" => simple .bindingOrReturn
  | "endOfFile" => simple .endOfFile
  | _ =>
      invalidTagAt kindPath kind #[
        "token", "identifier", "type", "expression",
        "argumentOrRightParen", "commaOrRightParen", "bindingOrReturn",
        "endOfFile"
      ]
where
  simple (value : ParseExpectation) : DecodeResult ParseExpectation := do
    ensureExactObject path json ["kind"] ["kind"]
    pure value

def decodeParseExpectation
    (json : Lean.Json) :
    DecodeResult ParseExpectation :=
  decodeParseExpectationAt .root json

def encodeDiagnosticPhase : DiagnosticPhase -> Lean.Json
  | .surfaceLexing => "surfaceLexing"
  | .surfaceParsing => "surfaceParsing"

def encodeDiagnosticSeverity : DiagnosticSeverity -> Lean.Json
  | .error => "error"

private def encodeCharacter (character : Char) : Lean.Json :=
  String.singleton character

private def decodeCharacterAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Char := do
  let value <- decodeStringAt path json
  match value.toList with
  | [character] => pure character
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", value),
        ("expected", "single-unicode-scalar")
      ])

def encodeNonAssociativeBinaryOp
    (operator : NonAssociativeBinaryOp) : Lean.Json :=
  encodeBinaryOp operator.toBinaryOp

def decodeNonAssociativeBinaryOpAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult NonAssociativeBinaryOp := do
  let value <- decodeStringAt path json
  match value with
  | "lt" => pure .lt
  | "gt" => pure .gt
  | "le" => pure .le
  | "ge" => pure .ge
  | "eq" => pure .eq
  | "ne" => pure .ne
  | _ => invalidTagAt path value #["lt", "gt", "le", "ge", "eq", "ne"]

def decodeNonAssociativeBinaryOp
    (json : Lean.Json) :
    DecodeResult NonAssociativeBinaryOp :=
  decodeNonAssociativeBinaryOpAt .root json

private def encodeOptionalTokenKind : Option TokenKind -> Lean.Json
  | none => .null
  | some kind => encodeTokenKind kind

private def decodeOptionalTokenKindAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (Option TokenKind) :=
  if json.isNull then
    pure none
  else
    some <$> decodeTokenKindAt path json

def encodeDiagnosticArguments : DiagnosticArguments -> Lean.Json
  | .invalidCharacter character => .mkObj [
      ("character", encodeCharacter character)
    ]
  | .unterminatedBlockComment => .mkObj []
  | .expected expectation found => .mkObj [
      ("expectation", encodeParseExpectation expectation),
      ("found", encodeOptionalTokenKind found)
    ]
  | .nonAssociative operator => .mkObj [
      ("operator", encodeNonAssociativeBinaryOp operator)
    ]

private def decodeInvalidCharacterArgumentsAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Char := do
  ensureExactObject path json ["character"] ["character"]
  let characterPath := path.field "character"
  decodeCharacterAt characterPath (← requireField path json "character")

private def decodeUnterminatedBlockCommentArgumentsAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Unit :=
  ensureExactObject path json [] []

private def decodeExpectedArgumentsAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (ParseExpectation × Option TokenKind) := do
  ensureExactObject path json
    ["expectation", "found"] ["expectation", "found"]
  let expectationPath := path.field "expectation"
  let expectation <- decodeParseExpectationAt expectationPath
    (← requireField path json "expectation")
  let foundPath := path.field "found"
  let found <- decodeOptionalTokenKindAt foundPath
    (← requireField path json "found")
  pure (expectation, found)

private def decodeNonAssociativeArgumentsAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult NonAssociativeBinaryOp := do
  ensureExactObject path json ["operator"] ["operator"]
  let operatorPath := path.field "operator"
  decodeNonAssociativeBinaryOpAt operatorPath
    (← requireField path json "operator")

private def encodeDisplay : Option String -> Lean.Json
  | none => .null
  | some display => display

private def decodeDisplayAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (Option String) :=
  match json with
  | .null => pure none
  | .str value => pure (some value)
  | _ => failAt path .expectedString (.mkObj [
      ("expected", "string-or-null")
    ])

def encodeDiagnostic (diagnostic : Diagnostic) : Lean.Json :=
  .mkObj [
    ("code", diagnostic.code),
    ("severity", encodeDiagnosticSeverity diagnostic.severity),
    ("phase", encodeDiagnosticPhase diagnostic.phase),
    ("primary", encodeSourceSpan diagnostic.primary),
    ("arguments", encodeDiagnosticArguments diagnostic.arguments),
    ("display", encodeDisplay diagnostic.display)
  ]

private def decodeDiagnosticKindAt
    (codePath phasePath argumentsPath : DecodePath)
    (code : String)
    (phaseJson argumentsJson : Lean.Json) :
    DecodeResult DiagnosticKind :=
  match code with
  | "SL0001" => do
      requireLiteralAt phasePath phaseJson "surfaceLexing"
      pure (.invalidCharacter
        (← decodeInvalidCharacterArgumentsAt argumentsPath argumentsJson))
  | "SL0002" => do
      requireLiteralAt phasePath phaseJson "surfaceLexing"
      decodeUnterminatedBlockCommentArgumentsAt argumentsPath argumentsJson
      pure .unterminatedBlockComment
  | "SP0001" => do
      requireLiteralAt phasePath phaseJson "surfaceParsing"
      let (expectation, found) <-
        decodeExpectedArgumentsAt argumentsPath argumentsJson
      pure (.expected expectation found)
  | "SP0002" => do
      requireLiteralAt phasePath phaseJson "surfaceParsing"
      pure (.nonAssociative
        (← decodeNonAssociativeArgumentsAt argumentsPath argumentsJson))
  | _ =>
      invalidTagAt codePath code #["SL0001", "SL0002", "SP0001", "SP0002"]

def decodeDiagnosticAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Diagnostic := do
  ensureExactObject path json
    ["code", "severity", "phase", "primary", "arguments", "display"]
    ["code", "severity", "phase", "primary", "arguments", "display"]
  let codePath := path.field "code"
  let code <- decodeStringAt codePath (← requireField path json "code")
  let severityPath := path.field "severity"
  requireLiteralAt severityPath (← requireField path json "severity") "error"
  let phasePath := path.field "phase"
  let phaseJson <- requireField path json "phase"
  let primaryPath := path.field "primary"
  let primary <- decodeSourceSpanAt primaryPath
    (← requireField path json "primary")
  let argumentsPath := path.field "arguments"
  let argumentsJson <- requireField path json "arguments"
  let displayPath := path.field "display"
  let display <- decodeDisplayAt displayPath
    (← requireField path json "display")
  let kind <- decodeDiagnosticKindAt codePath phasePath argumentsPath
    code phaseJson argumentsJson
  pure { primary, kind, display }

def decodeDiagnostic (json : Lean.Json) : DecodeResult Diagnostic :=
  decodeDiagnosticAt .root json

def encodeParseResult (result : ParseResult) : Lean.Json :=
  .mkObj [
    ("schema", parseResultSchemaVersion),
    ("value", encodeFile result.value)
  ]

def decodeParseResultAt
    (limits : DecodeLimits)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult ParseResult := do
  ensureExactObject path json ["schema", "value"] ["schema", "value"]
  let schemaPath := path.field "schema"
  let actualSchema <-
    decodeStringAt schemaPath (← requireField path json "schema")
  unless actualSchema == parseResultSchemaVersion do
    failAt schemaPath .invalidSchema (.mkObj [
      ("expected", parseResultSchemaVersion),
      ("actual", actualSchema)
    ])
  let valuePath := path.field "value"
  let value <- decodeFileAt limits valuePath (← requireField path json "value")
  pure { value }

def decodeParseResult
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult ParseResult :=
  decodeParseResultAt limits .root json

def canonicalizeParseResult
    (limits : DecodeLimits)
    (json : Lean.Json) :
    DecodeResult Lean.Json :=
  encodeParseResult <$> decodeParseResult limits json

@[simp] theorem decodeTokenKindAt_encodeTokenKind
    (path : DecodePath)
    (kind : TokenKind) :
    decodeTokenKindAt path (encodeTokenKind kind) = .ok kind := by
  cases kind with
  | identifier text =>
      change (do
        let decoded <- decodeIdentifierTextAt (path.field "text")
          (encodeIdentifierText text)
        pure (TokenKind.identifier decoded)) = .ok _
      simp
      rfl
  | decimal digits =>
      change (do
        let decoded <- decodeDecimalDigitsAt (path.field "digits")
          (encodeDecimalDigits digits)
        pure (TokenKind.decimal decoded)) = .ok _
      simp
      rfl
  | hexadecimal digits =>
      change (do
        let decoded <- decodeHexadecimalDigitsAt (path.field "digits")
          (encodeHexadecimalDigits digits)
        pure (TokenKind.hexadecimal decoded)) = .ok _
      simp
      rfl
  | keywordFunction | keywordLet | keywordIf | keywordElse | keywordReturn |
    arrow | equal | equalEqual | bang | bangEqual | less | lessEqual |
    greater | greaterEqual | plus | minus | star | slash | percent |
    ampersand | caret | pipe | leftParen | rightParen | leftBrace |
    rightBrace | colon | semicolon | comma => rfl

@[simp] theorem decodeTokenKind_encodeTokenKind
    (kind : TokenKind) :
    decodeTokenKind (encodeTokenKind kind) = .ok kind :=
  decodeTokenKindAt_encodeTokenKind .root kind

@[simp] theorem decodeParseExpectationAt_encodeParseExpectation
    (path : DecodePath)
    (expectation : ParseExpectation) :
    decodeParseExpectationAt path (encodeParseExpectation expectation) =
      .ok expectation := by
  cases expectation with
  | token kind =>
      change (do
        let decoded <- decodeTokenKindAt (path.field "token")
          (encodeTokenKind kind)
        pure (ParseExpectation.token decoded)) = .ok _
      rw [decodeTokenKindAt_encodeTokenKind]
      rfl
  | identifier | type | expression | argumentOrRightParen |
    commaOrRightParen | bindingOrReturn | endOfFile => rfl

@[simp] theorem decodeParseExpectation_encodeParseExpectation
    (expectation : ParseExpectation) :
    decodeParseExpectation (encodeParseExpectation expectation) =
      .ok expectation :=
  decodeParseExpectationAt_encodeParseExpectation .root expectation

private theorem decodeCharacterAt_encodeCharacter
    (path : DecodePath)
    (character : Char) :
    decodeCharacterAt path (encodeCharacter character) = .ok character := by
  simp [decodeCharacterAt, encodeCharacter, decodeStringAt]
  rfl

@[simp] theorem decodeNonAssociativeBinaryOpAt_encode
    (path : DecodePath)
    (operator : NonAssociativeBinaryOp) :
    decodeNonAssociativeBinaryOpAt path
      (encodeNonAssociativeBinaryOp operator) = .ok operator := by
  cases operator <;> rfl

@[simp] theorem decodeNonAssociativeBinaryOp_encode
    (operator : NonAssociativeBinaryOp) :
    decodeNonAssociativeBinaryOp (encodeNonAssociativeBinaryOp operator) =
      .ok operator :=
  decodeNonAssociativeBinaryOpAt_encode .root operator

private theorem decodeOptionalTokenKindAt_encode
    (path : DecodePath)
    (found : Option TokenKind) :
    decodeOptionalTokenKindAt path (encodeOptionalTokenKind found) =
      .ok found := by
  cases found with
  | none => rfl
  | some kind =>
      have notNull : (encodeTokenKind kind).isNull = false := by
        cases kind <;> simp [encodeTokenKind, Lean.Json.mkObj,
          Lean.Json.isNull]
      simp only [encodeOptionalTokenKind, decodeOptionalTokenKindAt, notNull,
        Bool.false_eq_true, ↓reduceIte]
      rw [decodeTokenKindAt_encodeTokenKind]
      rfl

private theorem decodeDisplayAt_encodeDisplay
    (path : DecodePath)
    (display : Option String) :
    decodeDisplayAt path (encodeDisplay display) = .ok display := by
  cases display <;> rfl

private theorem decodeInvalidCharacterArgumentsAt_encode
    (path : DecodePath)
    (character : Char) :
    decodeInvalidCharacterArgumentsAt path
      (encodeDiagnosticArguments (.invalidCharacter character)) =
      .ok character := by
  change decodeCharacterAt (path.field "character")
    (encodeCharacter character) = .ok character
  exact decodeCharacterAt_encodeCharacter _ _

private theorem decodeUnterminatedArgumentsAt_encode
    (path : DecodePath) :
    decodeUnterminatedBlockCommentArgumentsAt path
      (encodeDiagnosticArguments .unterminatedBlockComment) = .ok () := by
  rfl

private theorem decodeExpectedArgumentsAt_encode
    (path : DecodePath)
    (expectation : ParseExpectation)
    (found : Option TokenKind) :
    decodeExpectedArgumentsAt path
      (encodeDiagnosticArguments (.expected expectation found)) =
      .ok (expectation, found) := by
  change (do
    let decodedExpectation <-
      decodeParseExpectationAt (path.field "expectation")
        (encodeParseExpectation expectation)
    let decodedFound <-
      decodeOptionalTokenKindAt (path.field "found")
        (encodeOptionalTokenKind found)
    pure (decodedExpectation, decodedFound)) = .ok _
  rw [decodeParseExpectationAt_encodeParseExpectation]
  rw [decodeOptionalTokenKindAt_encode]
  rfl

private theorem decodeNonAssociativeArgumentsAt_encode
    (path : DecodePath)
    (operator : NonAssociativeBinaryOp) :
    decodeNonAssociativeArgumentsAt path
      (encodeDiagnosticArguments (.nonAssociative operator)) =
      .ok operator := by
  change decodeNonAssociativeBinaryOpAt (path.field "operator")
    (encodeNonAssociativeBinaryOp operator) = .ok operator
  exact decodeNonAssociativeBinaryOpAt_encode _ _

private theorem decodeDiagnosticKindAt_encode
    (path : DecodePath)
    (kind : DiagnosticKind) :
    decodeDiagnosticKindAt
        (path.field "code")
        (path.field "phase")
        (path.field "arguments")
        kind.code
        (encodeDiagnosticPhase kind.phase)
        (encodeDiagnosticArguments kind.arguments) =
      .ok kind := by
  cases kind with
  | invalidCharacter character =>
      change (do
        let decodedCharacter <-
          decodeInvalidCharacterArgumentsAt (path.field "arguments")
            (encodeDiagnosticArguments (.invalidCharacter character))
        pure (DiagnosticKind.invalidCharacter decodedCharacter)) = .ok _
      rw [decodeInvalidCharacterArgumentsAt_encode]
      rfl
  | unterminatedBlockComment =>
      change (do
        decodeUnterminatedBlockCommentArgumentsAt (path.field "arguments")
          (encodeDiagnosticArguments .unterminatedBlockComment)
        pure DiagnosticKind.unterminatedBlockComment) = .ok _
      rw [decodeUnterminatedArgumentsAt_encode]
      rfl
  | expected expectation found =>
      change (do
        let (decodedExpectation, decodedFound) <-
          decodeExpectedArgumentsAt (path.field "arguments")
            (encodeDiagnosticArguments (.expected expectation found))
        pure (DiagnosticKind.expected decodedExpectation decodedFound)) =
          .ok _
      rw [decodeExpectedArgumentsAt_encode]
      rfl
  | nonAssociative operator =>
      change (do
        let decodedOperator <-
          decodeNonAssociativeArgumentsAt (path.field "arguments")
            (encodeDiagnosticArguments (.nonAssociative operator))
        pure (DiagnosticKind.nonAssociative decodedOperator)) = .ok _
      rw [decodeNonAssociativeArgumentsAt_encode]
      rfl

@[simp] theorem decodeDiagnosticAt_encodeDiagnostic
    (path : DecodePath)
    (diagnostic : Diagnostic) :
    decodeDiagnosticAt path (encodeDiagnostic diagnostic) = .ok diagnostic := by
  cases diagnostic with
  | mk primary kind display =>
      change (do
        let decodedPrimary <-
          decodeSourceSpanAt (path.field "primary")
            (encodeSourceSpan primary)
        let decodedDisplay <-
          decodeDisplayAt (path.field "display") (encodeDisplay display)
        let decodedKind <-
          decodeDiagnosticKindAt
            (path.field "code")
            (path.field "phase")
            (path.field "arguments")
            kind.code
            (encodeDiagnosticPhase kind.phase)
            (encodeDiagnosticArguments kind.arguments)
        pure ({
          primary := decodedPrimary
          kind := decodedKind
          display := decodedDisplay
        } : Diagnostic)) = .ok _
      rw [decodeSourceSpanAt_encodeSourceSpan]
      rw [decodeDisplayAt_encodeDisplay]
      rw [decodeDiagnosticKindAt_encode]
      rfl

@[simp] theorem decodeDiagnostic_encodeDiagnostic
    (diagnostic : Diagnostic) :
    decodeDiagnostic (encodeDiagnostic diagnostic) = .ok diagnostic :=
  decodeDiagnosticAt_encodeDiagnostic .root diagnostic

theorem decodeParseResultAt_encodeParseResult
    (limits : DecodeLimits)
    (path : DecodePath)
    (result : ParseResult)
    (depthEnough : fileDepth result.value <= limits.maxDepth)
    (nodesEnough : fileNodes result.value <= limits.maxNodes) :
    decodeParseResultAt limits path (encodeParseResult result) =
      .ok result := by
  cases result with
  | mk value =>
      change (do
        let decodedValue <-
          decodeFileAt limits (path.field "value") (encodeFile value)
        pure ({ value := decodedValue } : ParseResult)) = .ok _
      rw [decodeFileAt_encodeFile limits (path.field "value") value
        depthEnough nodesEnough]
      rfl

theorem decodeParseResult_encodeParseResult
    (limits : DecodeLimits)
    (result : ParseResult)
    (depthEnough : fileDepth result.value <= limits.maxDepth)
    (nodesEnough : fileNodes result.value <= limits.maxNodes) :
    decodeParseResult limits (encodeParseResult result) = .ok result :=
  decodeParseResultAt_encodeParseResult limits .root result
    depthEnough nodesEnough

theorem canonicalizeParseResult_encodeParseResult
    (limits : DecodeLimits)
    (result : ParseResult)
    (depthEnough : fileDepth result.value <= limits.maxDepth)
    (nodesEnough : fileNodes result.value <= limits.maxNodes) :
    canonicalizeParseResult limits (encodeParseResult result) =
      .ok (encodeParseResult result) := by
  simp [canonicalizeParseResult,
    decodeParseResult_encodeParseResult limits result depthEnough nodesEnough]
  rfl

theorem canonicalizeParseResult_idempotent
    (limits : DecodeLimits)
    (json : Lean.Json)
    (result : ParseResult)
    (decoded : decodeParseResult limits json = .ok result)
    (depthEnough : fileDepth result.value <= limits.maxDepth)
    (nodesEnough : fileNodes result.value <= limits.maxNodes) :
    canonicalizeParseResult limits json >>= canonicalizeParseResult limits =
      canonicalizeParseResult limits json := by
  simp [canonicalizeParseResult, decoded]
  exact canonicalizeParseResult_encodeParseResult limits result
    depthEnough nodesEnough

end Solcore.Surface.Wire.V1
