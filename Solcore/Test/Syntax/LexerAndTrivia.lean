import Solcore.Syntax.Identifier
import Solcore.Syntax.Lexer
import Solcore.Syntax.Lexer.Properties
import Solcore
import Solcore.Syntax.Lexer.Step
import Solcore.Syntax.Parser
import Solcore.Syntax.Parser.PublicOutputs
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.Internal.TypeTrace
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.ParseProperties
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Parser.Internal.TriviaProofs

/-!
# Lexer, tokens and trivia tests

The lexer and its token catalog, identifiers and reserved words, primitive tokens, source spans,
the parser's state and cursor, and how trivia attaches to declarations.
-/

section
-- leanmerge: from Solcore.Test.SyntaxIdentifier
/-! Public canonical identifier validation regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def assertEqual {α : Type} [BEq α] [Repr α]
    (actual expected : α) (message : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{message}: expected {reprStr expected}, got {reprStr actual}")

private def validIdentifiers : List String := [
  "value",
  "value_2",
  "λ",
  "fλ2",
  "comptime",
  "derive",
  "enum",
  "from",
  "hiding",
  "impl",
  "mapping",
  "returns",
  "trait",
  "where",
  "while"
]

private def invalidIdentifiers : List String := [
  "",
  "_",
  "_value",
  "$",
  "$value",
  "value$tail",
  "`templateValue`",
  "${templateValue}",
  "0",
  "0x2a",
  "2value",
  "return",
  "true",
  "false",
  "\"text\"",
  "__",
  "value-name",
  "two names",
  "value;",
  "value/*comment*/"
]

private def hardKeywords : List HardKeyword := [
  .contractKw,
  .importKw, .exportKw, .asKw, .letKw, .dataKw, .classKw,
  .forallKw, .instanceKw, .ifKw, .elseKw, .forKw, .switchKw,
  .typeKw, .caseKw, .defaultKw, .matchKw, .publicKw, .payableKw,
  .functionKw, .constructorKw, .fallbackKw, .returnKw, .leaveKw,
  .continueKw, .breakKw, .lamKw, .assemblyKw, .pragmaKw,
  .trueKw, .falseKw
]

private def contextualKeywords : List ContextualKeyword := [
  .comptime,
  .derive, .enum, .from, .hiding, .impl, .mapping, .returns,
  .trait, .where, .while
]

example : validIdentifiers.all isValidIdentifier = true := by
  native_decide

example : invalidIdentifiers.any isValidIdentifier = false := by
  native_decide

example : hardKeywords.any (isValidIdentifier ·.spelling) = false := by
  native_decide

example : contextualKeywords.all (isValidIdentifier ·.spelling) = true := by
  native_decide

/-- Run ordinary-identifier validation regressions pinned to solcore-rs PR #20. -/
def testSyntaxIdentifier : IO Unit := do
  for text in validIdentifiers do
    assertEqual (isValidIdentifier text) true
      s!"identifier {text.quote} should be valid"
  for text in invalidIdentifiers do
    assertEqual (isValidIdentifier text) false
      s!"identifier {text.quote} should be invalid"
  for keyword in hardKeywords do
    assertEqual (isValidIdentifier keyword.spelling) false
      s!"hard keyword {keyword.spelling.quote} should be invalid"
  for keyword in contextualKeywords do
    assertEqual (isValidIdentifier keyword.spelling) true
      s!"contextual word {keyword.spelling.quote} should be valid"

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxLexerCatalog
/-! Canonical Solcore lexer catalog regressions, pinned to solcore-rs PR #20. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def catalogSource : SourceId := {
  origin := .main
  path := "catalog.sol"
}

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def expectSingle (spelling : String) (expected : TokenKind) : IO Unit := do
  let file : SourceFile := { id := catalogSource, content := spelling }
  match Lexer.lex file with
  | .error diagnostic =>
      throw (IO.userError
        s!"catalog spelling {spelling.quote} exhausted lexer fuel: {reprStr diagnostic}")
  | .ok output =>
      assertTrue output.comments.isEmpty
        s!"catalog spelling {spelling.quote} unexpectedly produced comments"
      assertTrue output.diagnostics.isEmpty
        s!"catalog spelling {spelling.quote} produced {reprStr output.diagnostics}"
      match output.tokens with
      | [token] =>
          assertTrue (token.value == expected)
            s!"catalog spelling {spelling.quote} produced {reprStr token.value}"
          assertTrue
            ((token.span.startByte, token.span.endByte) ==
              (0, spelling.utf8ByteSize))
            s!"catalog spelling {spelling.quote} had span {reprStr token.span}"
          assertTrue (token.span.isValidFor file)
            s!"catalog spelling {spelling.quote} had an invalid UTF-8 span"
      | tokens =>
          throw (IO.userError
            s!"catalog spelling {spelling.quote} produced {tokens.length} tokens")

private def keywordCases : List (String × TokenKind) := [
  ("contract", .keyword .contractKw),
  ("import", .keyword .importKw),
  ("export", .keyword .exportKw),
  ("as", .keyword .asKw),
  ("let", .keyword .letKw),
  ("data", .keyword .dataKw),
  ("class", .keyword .classKw),
  ("forall", .keyword .forallKw),
  ("instance", .keyword .instanceKw),
  ("if", .keyword .ifKw),
  ("else", .keyword .elseKw),
  ("for", .keyword .forKw),
  ("switch", .keyword .switchKw),
  ("type", .keyword .typeKw),
  ("case", .keyword .caseKw),
  ("default", .keyword .defaultKw),
  ("match", .keyword .matchKw),
  ("public", .keyword .publicKw),
  ("payable", .keyword .payableKw),
  ("function", .keyword .functionKw),
  ("constructor", .keyword .constructorKw),
  ("fallback", .keyword .fallbackKw),
  ("return", .keyword .returnKw),
  ("leave", .keyword .leaveKw),
  ("continue", .keyword .continueKw),
  ("break", .keyword .breakKw),
  ("lam", .keyword .lamKw),
  ("assembly", .keyword .assemblyKw),
  ("pragma", .keyword .pragmaKw),
  ("true", .keyword .trueKw),
  ("false", .keyword .falseKw)
]

private def contextualCases : List String := [
  "comptime", "derive", "enum", "from", "hiding", "impl",
  "mapping", "returns", "trait", "where", "while"
]

private def symbolCases : List (String × TokenKind) := [
  (":=", .symbol .colonEqual),
  ("->", .symbol .arrow),
  ("=>", .symbol .fatArrow),
  ("==", .symbol .equalEqual),
  ("!=", .symbol .notEqual),
  (">=", .symbol .greaterEqual),
  ("<=", .symbol .lessEqual),
  ("&&", .symbol .logicalAnd),
  ("||", .symbol .logicalOr),
  ("+=", .symbol .plusEqual),
  ("-=", .symbol .minusEqual),
  ("*=", .symbol .starEqual),
  ("/=", .symbol .slashEqual),
  ("^=", .symbol .caretEqual),
  ("&=", .symbol .ampEqual),
  ("|=", .symbol .pipeEqual),
  ("%=", .symbol .percentEqual),
  ("~=", .symbol .tildeEqual),
  ("+", .symbol .plus),
  ("-", .symbol .minus),
  ("*", .symbol .star),
  ("/", .symbol .slash),
  ("%", .symbol .percent),
  ("!", .symbol .bang),
  ("~", .symbol .tilde),
  ("<", .symbol .less),
  (">", .symbol .greater),
  ("=", .symbol .equal),
  ("|", .symbol .pipe),
  ("&", .symbol .amp),
  ("^", .symbol .caret),
  ("@", .symbol .at),
  ("?", .symbol .question),
  ("#", .symbol .hash),
  (".", .symbol .dot),
  (":", .symbol .colon),
  (";", .symbol .semicolon),
  (",", .symbol .comma),
  ("(", .symbol .leftParen),
  (")", .symbol .rightParen),
  ("{", .symbol .leftBrace),
  ("}", .symbol .rightBrace),
  ("[", .symbol .leftBracket),
  ("]", .symbol .rightBracket),
  ("_", .symbol .underscore)
]

/-- Run exact recognition and span checks for every closed lexer catalog item. -/
def testSyntaxLexerCatalog : IO Unit := do
  for (spelling, expected) in keywordCases do
    expectSingle spelling expected
  for spelling in contextualCases do
    expectSingle spelling (.identifier spelling)
  for (spelling, expected) in symbolCases do
    expectSingle spelling expected

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxLexer
/-! Cross-cutting behavior and recovery regressions for the canonical lexer. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat
private abbrev CommentView := CommentKind × String × ByteRange
private abbrev DiagnosticView := LexicalErrorKind × ByteRange

private def lexerSource : SourceId := {
  origin := .main
  path := "lexer-regression.sol"
}

private def assertEqual_variant {α : Type} [BEq α] [Repr α]
    (actual expected : α) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def tokenRanges (output : LexedFile) : List ByteRange :=
  output.tokens.map fun token => byteRange token.span

private def tokenKinds (output : LexedFile) : List TokenKind :=
  output.tokens.map (·.value)

private def commentViews (output : LexedFile) : List CommentView :=
  output.comments.map fun comment =>
    (comment.kind, comment.text, byteRange comment.span)

private def diagnosticViews (output : LexedFile) : List DiagnosticView :=
  output.diagnostics.map fun diagnostic =>
    (diagnostic.kind, byteRange diagnostic.span)

private def checkedLex (label content : String) : IO LexedFile := do
  let file : SourceFile := { id := lexerSource, content }
  match Lexer.lex file with
  | .error diagnostic =>
      throw (IO.userError
        s!"{label}: public lexer exhausted fuel: {reprStr diagnostic}")
  | .ok output =>
      assertEqual_variant output.source file.id s!"{label} source owner"
      unless output.tokens.all (fun token => token.span.isValidFor file) do
        throw (IO.userError s!"{label}: token span escaped the source")
      unless output.comments.all (fun comment => comment.span.isValidFor file) do
        throw (IO.userError s!"{label}: comment span escaped the source")
      unless output.diagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: diagnostic span escaped the source")
      pure output

private def testMaximalMunch : IO Unit := do
  let output ← checkedLex "maximal munch" ":== &&& ~=~ 0x 0xz 0x1g"
  assertEqual_variant (tokenKinds output) [
      .symbol .colonEqual, .symbol .equal,
      .symbol .logicalAnd, .symbol .amp,
      .symbol .tildeEqual, .symbol .tilde,
      .decimalLiteral "0", .identifier "x",
      .decimalLiteral "0", .identifier "xz",
      .hexadecimalLiteral "0x1", .identifier "g"
    ] "maximal-munch tokens"
  assertEqual_variant (tokenRanges output) [
      (0, 2), (2, 3), (4, 6), (6, 7), (8, 10), (10, 11),
      (12, 13), (13, 14), (15, 16), (16, 18), (19, 22), (22, 23)
    ] "maximal-munch Rust spans"
  assertEqual_variant output.diagnostics [] "maximal-munch diagnostics"

private def testUnicode : IO Unit := do
  let output ← checkedLex "Unicode identifiers" "λ2 四٤_ 𐐀9 § z"
  assertEqual_variant (tokenKinds output) [
      .identifier "λ2", .identifier "四٤_", .identifier "𐐀9",
      .identifier "z"
    ] "Unicode identifier tokens"
  assertEqual_variant (tokenRanges output)
    [(0, 3), (4, 10), (11, 16), (20, 21)]
    "Unicode identifier Rust spans"
  assertEqual_variant (diagnosticViews output)
    [(.invalidToken, (17, 19))]
    "Unicode invalid-scalar span"

private def testYulAndMeta : IO Unit := do
  let output ← checkedLex "Yul names and meta"
    "λ2 := 0xF += _x $y value$tail `z` ${q}"
  assertEqual_variant (tokenKinds output) [
      .identifier "λ2", .symbol .colonEqual, .hexadecimalLiteral "0xF",
      .symbol .plusEqual, .yulIdentifier "_x", .yulIdentifier "$y",
      .yulIdentifier "value$tail", .yulMetaBacktick "`z`",
      .yulMetaInterpolation "${q}"
    ] "Yul and meta tokens"
  assertEqual_variant (tokenRanges output) [
      (0, 3), (4, 6), (7, 10), (11, 13), (14, 16), (17, 19),
      (20, 30), (31, 34), (35, 39)
    ] "Yul and meta Rust spans"
  assertEqual_variant output.diagnostics [] "Yul and meta diagnostics"

  let interpolation ← checkedLex "unterminated interpolation" "${unterminated"
  assertEqual_variant (tokenKinds interpolation) [
      .yulIdentifier "$", .symbol .leftBrace, .identifier "unterminated"
    ] "unterminated interpolation fallback"
  assertEqual_variant (tokenRanges interpolation) [(0, 1), (1, 2), (2, 14)]
    "unterminated interpolation Rust spans"

  let backtick ← checkedLex "unterminated backtick" "`unterminated"
  assertEqual_variant backtick.tokens [] "unterminated backtick tokens"
  assertEqual_variant (diagnosticViews backtick)
    [(.invalidToken, (0, 13))]
    "unterminated backtick Rust span"

private def testStringsAndRecovery : IO Unit := do
  let strings ← checkedLex "strings" "\"ok\\n\" \"bad\\q\" after"
  assertEqual_variant (tokenKinds strings)
    [.stringLiteral "\"ok\\n\"", .identifier "after"]
    "string recovery tokens"
  assertEqual_variant (tokenRanges strings) [(0, 6), (15, 20)]
    "string recovery token spans"
  assertEqual_variant (diagnosticViews strings)
    [(.invalidStringEscape, (7, 14))]
    "invalid string escape Rust span"

  let unterminated ← checkedLex "unterminated string" "\"unterminated after"
  assertEqual_variant unterminated.tokens [] "unterminated string tokens"
  assertEqual_variant (diagnosticViews unterminated)
    [(.invalidToken, (0, 19))]
    "unterminated string Rust span"

  let accumulated ← checkedLex "diagnostic accumulation" "§ \"bad\\q\" ¤ ok"
  assertEqual_variant (tokenKinds accumulated) [.identifier "ok"]
    "diagnostic accumulation tokens"
  assertEqual_variant (tokenRanges accumulated) [(14, 16)]
    "diagnostic accumulation token span"
  assertEqual_variant (diagnosticViews accumulated) [
      (.invalidToken, (0, 2)),
      (.invalidStringEscape, (3, 10)),
      (.invalidToken, (11, 13))
    ] "diagnostic accumulation order and Rust spans"

private def testComments : IO Unit := do
  let comments ← checkedLex "comments"
    "x // cr\r\ny /* outer /* inner */ end */ z"
  assertEqual_variant (tokenKinds comments)
    [.identifier "x", .identifier "y", .identifier "z"]
    "comment-separated tokens"
  assertEqual_variant (tokenRanges comments) [(0, 1), (9, 10), (39, 40)]
    "comment-separated Rust token spans"
  assertEqual_variant (commentViews comments) [
      (.line, " cr\r", (2, 8)),
      (.block, " outer /* inner */ end ", (11, 38))
    ] "comment text and Rust spans"
  assertEqual_variant comments.diagnostics [] "closed comment diagnostics"

  let unterminated ← checkedLex "unterminated block comment" "x /* no"
  assertEqual_variant (tokenKinds unterminated) [.identifier "x"]
    "unterminated block prefix token"
  assertEqual_variant unterminated.comments [] "unterminated block comments"
  assertEqual_variant (diagnosticViews unterminated)
    [(.unterminatedBlockComment, (2, 7))]
    "unterminated block Rust span"

private def testIdentifierBoundaries : IO Unit := do
  let words ← checkedLex "identifier boundaries"
    "if ifx xif if-x true$x foo-2 foo--bar"
  assertEqual_variant (tokenKinds words) [
      .keyword .ifKw, .identifier "ifx", .identifier "xif",
      .identifier "if-x", .yulIdentifier "true$x",
      .identifier "foo", .symbol .minus, .decimalLiteral "2",
      .identifier "foo", .symbol .minus, .symbol .minus, .identifier "bar"
    ] "keyword, hyphen, and Yul identifier boundaries"
  assertEqual_variant (tokenRanges words) [
      (0, 2), (3, 6), (7, 10), (11, 15), (16, 22),
      (23, 26), (26, 27), (27, 28),
      (29, 32), (32, 33), (33, 34), (34, 37)
    ] "identifier-boundary Rust spans"

  let marked ← checkedLex "marked identifiers" "_ $ _$value"
  assertEqual_variant (tokenKinds marked)
    [.symbol .underscore, .yulIdentifier "$", .yulIdentifier "_$value"]
    "lone underscore and marked identifiers"
  assertEqual_variant (tokenRanges marked) [(0, 1), (2, 3), (4, 11)]
    "marked-identifier Rust spans"

private def testWhitespaceAndStringNewlines : IO Unit := do
  let whitespace ← checkedLex "ASCII whitespace" "a \t\n\r\u000c b"
  assertEqual_variant (tokenKinds whitespace) [.identifier "a", .identifier "b"]
    "ASCII whitespace tokens"
  assertEqual_variant (tokenRanges whitespace) [(0, 1), (7, 8)]
    "ASCII whitespace spans"

  let rawNewline ← checkedLex "raw string newline" "\"line\nbreak\" after"
  assertEqual_variant (tokenKinds rawNewline)
    [.stringLiteral "\"line\nbreak\"", .identifier "after"]
    "raw-newline string tokens"
  assertEqual_variant (tokenRanges rawNewline) [(0, 12), (13, 18)]
    "raw-newline string Rust spans"
  assertEqual_variant rawNewline.diagnostics [] "raw-newline string diagnostics"

  let escapedLf ← checkedLex "escaped LF string prefix" "\"bad\\\nafter"
  assertEqual_variant (tokenKinds escapedLf) [.identifier "after"]
    "escaped-LF recovery token"
  assertEqual_variant (tokenRanges escapedLf) [(6, 11)]
    "escaped-LF recovery token span"
  assertEqual_variant (diagnosticViews escapedLf)
    [(.invalidToken, (0, 5))]
    "escaped-LF invalid-prefix span"

private def testEmptyComments : IO Unit := do
  let output ← checkedLex "empty comments" "//\n/**///"
  assertEqual_variant output.tokens [] "empty-comment tokens"
  assertEqual_variant (commentViews output) [
      (.line, "", (0, 2)),
      (.block, "", (3, 7)),
      (.line, "", (7, 9))
    ] "empty and EOF comment spans"
  assertEqual_variant output.diagnostics [] "empty-comment diagnostics"

private def hyphenNameChars : Nat → List Char → List Char
  | 0, reversed => reversed.reverse
  | count + 1, reversed =>
      hyphenNameChars count ('a' :: '-' :: reversed)

private def testLongScans : IO Unit := do
  let longName := String.ofList (List.replicate 100000 'a')
  let nameOutput ← checkedLex "long identifier" longName
  match nameOutput.tokens with
  | [{ value := .identifier text, .. }] =>
      assertEqual_variant text.length 100000 "long identifier length"
  | tokens =>
      throw (IO.userError
        s!"long identifier produced {tokens.length} tokens")

  let commentOutput ← checkedLex "long line comment" ("//" ++ longName)
  match commentOutput.comments with
  | [{ kind := .line, text, .. }] =>
      assertEqual_variant text.length 100000 "long line-comment length"
  | comments =>
      throw (IO.userError
        s!"long line comment produced {comments.length} comments")

  let hyphenName := String.ofList (hyphenNameChars 10000 ['a'])
  let hyphenOutput ← checkedLex "long hyphen identifier" hyphenName
  assertEqual_variant hyphenOutput.tokens.length 1
    "long hyphen identifier token count"
  assertEqual_variant hyphenOutput.diagnostics []
    "long hyphen identifier diagnostics"

private def testInternalFuelBranch : IO Unit := do
  let file : SourceFile := { id := lexerSource, content := "x" }
  match Lexer.lexLoop file 0 (Lexer.State.initial file) with
  | .ok output =>
      throw (IO.userError
        s!"zero-fuel lexer unexpectedly succeeded: {reprStr output}")
  | .error diagnostic =>
      assertEqual_variant diagnostic.kind .internalFuelExhausted
        "zero-fuel internal diagnostic"
      assertEqual_variant (byteRange diagnostic.span) (0, 0)
        "zero-fuel internal diagnostic span"
      unless diagnostic.span.isValidFor file do
        throw (IO.userError "zero-fuel internal diagnostic span is invalid")

/-- Run the canonical lexer catalog, behavior, span, and recovery regressions. -/
def testSyntaxLexer : IO Unit := do
  testSyntaxLexerCatalog
  testMaximalMunch
  testUnicode
  testYulAndMeta
  testStringsAndRecovery
  testComments
  testIdentifierBoundaries
  testWhitespaceAndStringNewlines
  testEmptyComments
  testLongScans
  testInternalFuelBranch

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxLexerContractProperties
/-! External compile consumers for the public lexical contract. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Lexer

example {α : Type} (file : SourceFile) (spanOf : α → SourceSpan)
    (items : List α)
    (spanValid : ∀ item ∈ items, (spanOf item).ValidFor file)
    (spanNonempty : ∀ item ∈ items,
      (spanOf item).startByte < (spanOf item).endByte)
    (ordered : items.Pairwise fun left right =>
      (spanOf left).endByte ≤ (spanOf right).startByte) :
    SpanSequence.ValidFor file spanOf 0 items :=
  SpanSequence.ValidFor.of_forall_pairwise spanValid
    (fun item _member => Nat.zero_le (spanOf item).startByte)
    spanNonempty ordered

example (file : SourceFile) (state : State)
    (ordered : state.OrderedValidFor file) :
    (state.finish file).ValidFor file :=
  ordered.finish_validFor

example (file : SourceFile) (fuel : Nat) (state : State)
    (lexed : LexedFile) (ordered : state.OrderedValidFor file)
    (result : lexLoop file fuel state = .ok lexed) :
    lexed.ValidFor file :=
  lexLoop_ok_validFor file fuel state lexed ordered result

example (file : SourceFile) (lexed : LexedFile)
    (result : lex file = .ok lexed) : lexed.ValidFor file :=
  lex_ok_validFor file lexed result

example (file : SourceFile) :
    ∃ lexed, lex file = .ok lexed ∧ lexed.ValidFor file :=
  lex_total_validFor file

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxLexerScannerProperties
/-! External compile consumers for canonical lexer scanner laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Lexer

example (leading trailing : List Char) :
    byteSize (leading ++ trailing) =
      byteSize leading + byteSize trailing :=
  byteSize_append leading trailing

example (predicate : Char → Bool) (characters : List Char) :
    characters =
      (takeWhile predicate characters).consumed ++
        (takeWhile predicate characters).remaining :=
  takeWhile_partition predicate characters

example (predicate : Char → Bool) (startByte : Nat)
    (characters : List Char) :
    let scan := takeWhile predicate characters
    Advances startByte characters
      (startByte + byteSize scan.consumed) scan.remaining :=
  takeWhile_advances predicate startByte characters

example (text : String) (keyword : HardKeyword)
    (recognized : HardKeyword.ofString? text = some keyword) :
    keyword.spelling = text :=
  HardKeyword.spelling_eq_of_ofString?_eq_some text keyword recognized

example (file : SourceFile) :
    CursorSuffix file 0 file.content.toList :=
  CursorSuffix.initial file

example (file : SourceFile) (cursor : Nat) (remaining : List Char)
    (suffix : CursorSuffix file cursor remaining) :
    file.content.utf8ByteSize = cursor + byteSize remaining :=
  suffix.remainingByteSize

example (file : SourceFile) (cursor : Nat) (remaining : List Char)
    (suffix : CursorSuffix file cursor remaining) :
    isUtf8Boundary file.content cursor = true :=
  suffix.boundary

example (file : SourceFile) (startByte : Nat) (input : List Char)
    (suffix : CursorSuffix file startByte input)
    (predicate : Char → Bool) :
    let scan := takeWhile predicate input
    (sourceSpan file startByte
      (startByte + byteSize scan.consumed)).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (takeWhile_advances predicate startByte input)

example (file : SourceFile) (cursor : Nat) (characters : List Char)
    (suffix : CursorSuffix file cursor characters) :
    let scan := scanLineComment cursor characters
    (sourceSpan file cursor scan.endByte).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (scanLineComment_advances cursor characters)

example (file : SourceFile) (cursor depth : Nat)
    (characters bodyRev : List Char) (endByte : Nat)
    (body remaining : List Char)
    (suffix : CursorSuffix file cursor characters)
    (result : scanBlockComment cursor depth characters bodyRev =
      .closed endByte body remaining) :
    (sourceSpan file cursor endByte).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (scanBlockComment_closed_advances cursor depth characters bodyRev
      endByte body remaining result)

example (file : SourceFile) (closing : Char) (cursor : Nat)
    (characters spellingRev : List Char) (scan : MetaScan)
    (suffix : CursorSuffix file cursor characters)
    (result : scanDelimitedMeta closing cursor characters spellingRev =
      some scan) :
    (sourceSpan file cursor scan.endByte).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (scanDelimitedMeta_some_advances closing cursor characters spellingRev
      scan result)

example (file : SourceFile) (startByte endByte : Nat)
    (input remaining : List Char) (spelling decoded : String)
    (suffix : CursorSuffix file startByte ('"' :: input))
    (result : scanQuotedString startByte input =
      .closed endByte spelling decoded remaining) :
    (sourceSpan file startByte endByte).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (scanQuotedString_closed_advances startByte input endByte spelling
      decoded remaining result)

example (file : SourceFile) (cursor : Nat) (first : Char)
    (remaining : List Char)
    (suffix : CursorSuffix file cursor (first :: remaining)) :
    let scan := scanLetterIdentifier first remaining
    (sourceSpan file cursor
      (cursor + scan.kind.spelling.utf8ByteSize)).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (scanLetterIdentifier_advances cursor first remaining)

example (file : SourceFile) (cursor : Nat) (first : Char)
    (remaining : List Char)
    (suffix : CursorSuffix file cursor (first :: remaining)) :
    let scan := scanMarkedYulIdentifier first remaining
    (sourceSpan file cursor
      (cursor + scan.kind.spelling.utf8ByteSize)).ValidFor file := by
  exact suffix.sourceSpan_validFor
    (scanMarkedYulIdentifier_advances cursor first remaining)

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxLexerStateOrderProperties
/-! External compile consumers for reverse-accumulator source ordering. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Lexer

example (file : SourceFile) :
    (State.initial file).OrderedValidFor file :=
  State.initial_orderedValidFor file

example (file : SourceFile) (state : State)
    (ordered : state.OrderedValidFor file) :
    (step file state).OrderedValidFor file :=
  step_orderedValidFor file state ordered

example (file : SourceFile) (state : State)
    (ordered : state.OrderedValidFor file) :
    state.tokensRev.Pairwise fun newer older =>
      older.span.endByte ≤ newer.span.startByte :=
  ordered.tokensRev_pairwise

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (ordered : state.OrderedValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.skipTo endByte remaining).OrderedValidFor file :=
  ordered.skipTo endByte remaining progress

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (kind : TokenKind)
    (ordered : state.OrderedValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining)
    (strict : state.cursor < endByte) :
    (state.emitToken file endByte remaining kind).OrderedValidFor file :=
  ordered.emitToken endByte remaining kind progress strict

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (kind : CommentKind) (text : String)
    (ordered : state.OrderedValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining)
    (strict : state.cursor < endByte) :
    (state.emitComment file endByte remaining kind text).OrderedValidFor file :=
  ordered.emitComment endByte remaining kind text progress strict

example (file : SourceFile) (state : State)
    (diagnosticStart diagnosticEnd nextByte : Nat)
    (remaining : List Char) (kind : LexicalErrorKind)
    (ordered : state.OrderedValidFor file)
    (progress : Advances state.cursor state.remaining nextByte remaining)
    (diagnosticValid :
      (sourceSpan file diagnosticStart diagnosticEnd).ValidFor file) :
    State.OrderedValidFor
      (state.recover file diagnosticStart diagnosticEnd nextByte remaining kind)
      file :=
  ordered.recover diagnosticStart diagnosticEnd nextByte remaining kind
    progress diagnosticValid

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxLexerStateProperties
/-! External compile consumers for canonical lexer state invariants. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Lexer

example (file : SourceFile) :
    (State.initial file).ValidFor file :=
  State.initial_validFor file

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (valid : state.ValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.skipTo endByte remaining).ValidFor file :=
  valid.skipTo endByte remaining progress

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (kind : TokenKind)
    (valid : state.ValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.emitToken file endByte remaining kind).ValidFor file :=
  valid.emitToken endByte remaining kind progress

example (file : SourceFile) (state : State) (endByte : Nat)
    (remaining : List Char) (kind : CommentKind) (text : String)
    (valid : state.ValidFor file)
    (progress : Advances state.cursor state.remaining endByte remaining) :
    (state.emitComment file endByte remaining kind text).ValidFor file :=
  valid.emitComment endByte remaining kind text progress

example (file : SourceFile) (state : State)
    (diagnosticStart diagnosticEnd nextByte : Nat)
    (remaining : List Char) (kind : LexicalErrorKind)
    (valid : state.ValidFor file)
    (progress : Advances state.cursor state.remaining nextByte remaining)
    (diagnosticValid :
      (sourceSpan file diagnosticStart diagnosticEnd).ValidFor file) :
    State.ValidFor
      (state.recover file diagnosticStart diagnosticEnd nextByte remaining kind)
      file :=
  valid.recover diagnosticStart diagnosticEnd nextByte remaining kind progress
    diagnosticValid

example (file : SourceFile) (state : State) (valid : state.ValidFor file) :
    let lexed := state.finish file
    lexed.source = file.id ∧
      (∀ token ∈ lexed.tokens, token.span.ValidFor file) ∧
      (∀ comment ∈ lexed.comments, comment.span.ValidFor file) ∧
      (∀ diagnostic ∈ lexed.diagnostics,
        diagnostic.span.ValidFor file) :=
  valid.finish

example (file : SourceFile) (state : State) (valid : state.ValidFor file) :
    (step file state).ValidFor file :=
  step_validFor file state valid

example (file : SourceFile) (state : State)
    (nonempty : state.remaining ≠ []) :
    (step file state).remaining.length < state.remaining.length :=
  step_remaining_length_lt file nonempty

example (file : SourceFile) (lexed : LexedFile)
    (result : lex file = .ok lexed) :
    lexed.source = file.id ∧
      (∀ token ∈ lexed.tokens, token.span.ValidFor file) ∧
      (∀ comment ∈ lexed.comments, comment.span.ValidFor file) ∧
      (∀ diagnostic ∈ lexed.diagnostics,
        diagnostic.span.ValidFor file) :=
  lex_ok_carrier_spans file lexed result

example (file : SourceFile) : ∃ lexed, lex file = .ok lexed :=
  lex_exists_ok file

example (file : SourceFile) (diagnostic : LexicalDiagnostic)
    (result : lex file = .error diagnostic) : False :=
  lex_error_impossible file diagnostic result

example (file : SourceFile) :
    ∃ lexed,
      lex file = .ok lexed ∧
      lexed.source = file.id ∧
      (∀ token ∈ lexed.tokens, token.span.ValidFor file) ∧
      (∀ comment ∈ lexed.comments, comment.span.ValidFor file) ∧
      (∀ diagnostic ∈ lexed.diagnostics,
        diagnostic.span.ValidFor file) :=
  lex_total_carrier_spans file

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDeclarationTrivia
/-! Nested declaration and enum-constructor comment regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def triviaSource : SourceId := {
  origin := .main
  path := "parser-declaration-trivia.sol"
}

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := triviaSource, content }
  match Parser.parse file with
  | .error error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual_variant output.lexicalDiagnostics []
        s!"{label} lexical diagnostics"
      pure output

private def commentTexts (comments : List Comment) : List String :=
  comments.map (·.text)

private def constructorComments
    (declaration : EnumDecl) : List (String × List String) :=
  declaration.value.constructors.map fun constructor =>
    (constructor.value.name.value,
      commentTexts constructor.value.leadingComments)

private def testMethodAndContractComments : IO Unit := do
  let output ← checkedParse "nested declaration comments" (String.intercalate "\n" [
    "trait Read<a> {",
    "  // trait method",
    "  function read(value: a) returns (a);",
    "}",
    "impl Read<word> {",
    "  // impl method",
    "  function read(value: word) returns (word) { value }",
    "}",
    "contract Store {",
    "  // contract field",
    "  value: word;",
    "  // contract function",
    "  function read() returns (word) { value }",
    "}"
  ])
  assertEqual_variant output.parseDiagnostics []
    "nested declaration diagnostics"
  match output.parsed.items with
  | [
      { value := .trait traitDeclaration, .. },
      { value := .impl implDeclaration, .. },
      { value := .contract contractDeclaration, .. }
    ] =>
      match traitDeclaration.value.methods with
      | [method] =>
          assertEqual_variant (commentTexts method.value.leadingComments)
            [" trait method"] "trait method comments"
      | methods => throw (IO.userError
          s!"trait method count changed: {reprStr methods}")
      match implDeclaration.value.methods with
      | [method] =>
          assertEqual_variant (commentTexts method.value.leadingComments)
            [" impl method"] "impl method comments"
      | methods => throw (IO.userError
          s!"impl method count changed: {reprStr methods}")
      match contractDeclaration.value.members with
      | [field, function] =>
          assertEqual_variant (commentTexts field.leadingComments)
            [" contract field"] "contract field comments"
          assertEqual_variant (commentTexts function.leadingComments)
            [" contract function"] "contract function comments"
      | members => throw (IO.userError
          s!"contract member count changed: {reprStr members}")
  | items => throw (IO.userError
      s!"nested declaration items changed: {reprStr items}")

private def testConstructorIntroducers : IO Unit := do
  let output ← checkedParse "constructor introducers" (String.intercalate "\n" [
    "enum Top { // top first after brace",
    "  First",
    "  // top before comma one",
    "  /* top before comma two */",
    "  , // top second after comma",
    "    Second",
    "}",
    "enum BraceChain",
    "// before brace one",
    "/* before brace two */",
    "{ Only }",
    "contract C {",
    "  enum Nested { // local first after brace",
    "    LocalFirst",
    "    // local before comma",
    "    , // local second after comma",
    "      LocalSecond",
    "  }",
    "}"
  ])
  assertEqual_variant output.parseDiagnostics [] "constructor introducer diagnostics"
  match output.parsed.items with
  | [
      { value := .enum top, .. },
      { value := .enum braceChain, .. },
      { value := .contract contract, .. }
    ] =>
      assertEqual_variant (constructorComments top) [
        ("First", [" top first after brace"]),
        ("Second", [
          " top before comma one",
          " top before comma two ",
          " top second after comma"
        ])
      ] "top constructor comments"
      assertEqual_variant (constructorComments braceChain) [
        ("Only", [" before brace one", " before brace two "])
      ] "pre-brace constructor chain"
      match contract.value.members with
      | [{ value := .enum nested, .. }] =>
          assertEqual_variant (constructorComments nested) [
            ("LocalFirst", [" local first after brace"]),
            ("LocalSecond", [
              " local before comma", " local second after comma"
            ])
          ] "contract enum constructor comments"
      | members => throw (IO.userError
          s!"nested enum member changed: {reprStr members}")
  | items => throw (IO.userError
      s!"constructor introducer items changed: {reprStr items}")

private def testConstructorBoundaries : IO Unit := do
  let output ← checkedParse "constructor comment boundaries"
    (String.intercalate "\n" [
      "enum Boundary {",
      "  First // code owns this comment",
      "  , Second",
      "  // blank before comma",
      "",
      "  , Third",
      "  , // blank after comma",
      "",
      "    Fourth",
      "}",
      "contract C {",
      "  enum Nested {",
      "    LocalFirst // local code owns this comment",
      "    , LocalSecond",
      "  }",
      "}"
    ])
  assertEqual_variant output.parseDiagnostics [] "constructor boundary diagnostics"
  match output.parsed.items with
  | [
      { value := .enum boundary, .. },
      { value := .contract contract, .. }
    ] =>
      assertEqual_variant (constructorComments boundary) [
        ("First", []), ("Second", []), ("Third", []), ("Fourth", [])
      ] "blank-line and same-line constructor boundaries"
      match contract.value.members with
      | [{ value := .enum nested, .. }] =>
          assertEqual_variant (constructorComments nested) [
            ("LocalFirst", []), ("LocalSecond", [])
          ] "contract constructor code boundary"
      | members => throw (IO.userError
          s!"contract boundary members changed: {reprStr members}")
  | items => throw (IO.userError
      s!"constructor boundary items changed: {reprStr items}")

private def testDeclarationBoundaries : IO Unit := do
  let output ← checkedParse "nested declaration boundaries"
    (String.intercalate "\n" [
      "trait T<a> {",
      "  function first(value: a); // trailing method",
      "  function second(value: a);",
      "  // detached method",
      "",
      "  function third(value: a);",
      "}",
      "impl T<word> {",
      "  function first(value: word) {} // trailing impl method",
      "  function second(value: word) {}",
      "}",
      "contract C {",
      "  first: word; // trailing field",
      "  second: word;",
      "  function firstFn() {} // trailing function",
      "  function secondFn() {}",
      "}"
    ])
  assertEqual_variant output.parseDiagnostics [] "nested boundary diagnostics"
  match output.parsed.items with
  | [
      { value := .trait traitDeclaration, .. },
      { value := .impl implDeclaration, .. },
      { value := .contract contractDeclaration, .. }
    ] =>
      assertEqual_variant (traitDeclaration.value.methods.map fun method =>
        commentTexts method.value.leadingComments) [[], [], []]
        "trait comment boundaries"
      assertEqual_variant (implDeclaration.value.methods.map fun method =>
        commentTexts method.value.leadingComments) [[], []]
        "impl comment boundaries"
      assertEqual_variant (contractDeclaration.value.members.map fun member =>
        commentTexts member.leadingComments) [[], [], [], []]
        "contract comment boundaries"
  | items => throw (IO.userError
      s!"nested boundary items changed: {reprStr items}")

private def testContractRecoveryComment : IO Unit := do
  let output ← checkedParse "contract recovery comment" (String.intercalate "\n" [
    "contract C {",
    "  // invalid contract item",
    "  unknown nested;",
    "  function valid() {}",
    "}"
  ])
  assertEqual_variant output.parseDiagnostics.length 1
    "contract recovery diagnostic count"
  match output.parsed.items with
  | [{ value := .contract declaration, .. }] =>
      match declaration.value.members with
      | [errorMember, validMember] =>
          assertEqual_variant errorMember.value .error "contract recovery member"
          assertEqual_variant (commentTexts errorMember.leadingComments)
            [" invalid contract item"] "contract recovery comments"
          assertEqual_variant validMember.leadingComments []
            "contract recovery comment leakage"
      | members => throw (IO.userError
          s!"contract recovery members changed: {reprStr members}")
  | items => throw (IO.userError
      s!"contract recovery items changed: {reprStr items}")

/-- Run canonical nested-declaration comment regressions. -/
def testSyntaxParserDeclarationTrivia : IO Unit := do
  testMethodAndContractComments
  testConstructorIntroducers
  testConstructorBoundaries
  testDeclarationBoundaries
  testContractRecoveryComment

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserEmptyTokensOutputProperties
/-! Complete empty-token outputs retain comments and lexical diagnostics. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserEmptyTokensOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example (comments : List Comment) (input : State)
    (atEnd : input.window.endIndex ≤ input.cursor) :
    sourceFile comments input = .ok {
      source := input.file.id
      span := SourceSpan.fullFile input.file
      items := []
      comments
    } input :=
  sourceFile_atWindowEnd_exact comments atEnd

example {file : SourceFile} {lexed : LexedFile}
    (empty : lexed.tokens = [])
    (accepted : LexedFileValidationAccepts file lexed) :
    parseLexed file lexed = .ok {
      parsed := {
        source := file.id
        span := SourceSpan.fullFile file
        items := []
        comments := lexed.comments
      }
      tokens := lexed.tokens
      lexicalDiagnostics := lexed.diagnostics
      parseDiagnostics := []
    } :=
  parseLexed_eq_ok_of_emptyTokens accepted empty

example {file : SourceFile} {lexed : LexedFile}
    (empty : lexed.tokens = [])
    (result : parseLexed file lexed = .ok (emptyTokensParseOutput file lexed)) :
    LexedFileValidationAccepts file lexed :=
  (parseLexed_eq_ok_emptyTokens_iff empty).mp result

example {file : SourceFile} {lexed : LexedFile}
    (lexing : Lexer.lex file = .ok lexed) (empty : lexed.tokens = []) :
    parse file = .ok (emptyTokensParseOutput file lexed) :=
  parse_eq_ok_of_emptyTokens lexing empty

end Solcore.Test.SyntaxParserEmptyTokensOutputProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExactTokenPrimitiveTraceProperties
/-! Compile-time consumers of grammar-derived token success and exact reports.
All examples permit arbitrary prior diagnostics and parser contexts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExactTokenPrimitiveTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @acceptToken_eq_ok_of_exactTokenParses
example := @acceptToken_success_diagnostics_eq
example := @acceptToken_exactToken_success_iff
example := @keyword_eq_ok_of_exactTokenParses
example := @symbol_eq_ok_of_exactTokenParses
example := @contextual_eq_ok_of_exactTokenParses
example := @keyword_exactToken_success_iff
example := @symbol_exactToken_success_iff
example := @contextual_exactToken_success_iff
example := @keyword_eq_rejectAt_of_tokenKindAbsent
example := @symbol_eq_rejectAt_of_tokenKindAbsent
example := @contextual_eq_rejectAt_of_tokenKindAbsent
example := @keyword_reject_reports_iff
example := @symbol_reject_reports_iff
example := @contextual_reject_reports_iff
example := @acceptToken_reject_reports
example := @keyword_reject_diagnostics_eq
example := @symbol_reject_diagnostics_eq
example := @contextual_reject_diagnostics_eq

private def exampleFile : SourceFile := {
  id := { origin := .main, path := "exact-token-trace.sol" }
  content := "pragma:from"
}

private def exampleSpan (startByte endByte : Nat) : SourceSpan := {
  source := exampleFile.id, startByte, endByte
}

private def exampleInput (cursor : Nat) (priorRev : List ParseDiagnostic) : State := {
  file := exampleFile
  tokens := #[{ span := exampleSpan 0 6, value := .keyword .pragmaKw },
    { span := exampleSpan 6 7, value := .symbol .colon },
    { span := exampleSpan 7 11, value := .identifier "from" }]
  cursor
  window := { endIndex := 3, endByte := 11 }
  diagnosticsRev := priorRev
}

/-- The exact hard-keyword carrier survives unchanged. -/
theorem keyword_success_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ output, keyword .pragmaKw context (exampleInput 0 priorRev) =
      .ok { span := exampleSpan 0 6, value := .keyword .pragmaKw } output ∧
      output.declarativeRemainder = (exampleInput 1 priorRev).declarativeRemainder ∧
      output.diagnostics = priorRev.reverse := by
  apply (keyword_exactToken_success_iff .pragmaKw context).mp
  simp [ExactTokenParses, TokenAt, State.declarativeRemainder, exampleInput]

/-- Symbols retain their own exact span and silent raw diagnostic trace. -/
theorem symbol_success_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ output, symbol .colon context (exampleInput 1 priorRev) =
      .ok { span := exampleSpan 6 7, value := .symbol .colon } output ∧
      output.declarativeRemainder = (exampleInput 2 priorRev).declarativeRemainder ∧
      output.diagnostics = priorRev.reverse := by
  apply (symbol_exactToken_success_iff .colon context).mp
  simp [ExactTokenParses, TokenAt, State.declarativeRemainder, exampleInput]

/-- A contextual word is still the supplied identifier token. -/
theorem contextual_success_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ output, contextual .from context (exampleInput 2 priorRev) =
      .ok { span := exampleSpan 7 11, value := .identifier "from" } output ∧
      output.declarativeRemainder = (exampleInput 3 priorRev).declarativeRemainder ∧
      output.diagnostics = priorRev.reverse := by
  apply (contextual_exactToken_success_iff .from context).mp
  simp [ExactTokenParses, TokenAt, State.declarativeRemainder, exampleInput,
    ContextualKeyword.spelling]

private theorem eofReport (expected : ParseExpectation) (context : ParseContext)
    (priorRev : List ParseDiagnostic) :
    RejectAtReports exampleFile.id 11 { head := expected, tail := [] } context
      (exampleInput 3 priorRev).declarativeRemainder {
        span := exampleSpan 11 11,
        kind := .unexpected none { head := expected, tail := [] } context
      } := by
  apply RejectAtReports.reported
  exact .windowEnd (by simp [State.declarativeRemainder, exampleInput])

/-- EOF failure fixes its expectation/context and keeps the entire input. -/
theorem keyword_rejection_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ failure, keyword .pragmaKw context (exampleInput 3 priorRev) =
      .reject failure (exampleInput 3 priorRev) ∧
      failure.toDiagnostic = {
        span := exampleSpan 11 11
        kind := .unexpected none { head := .keyword .pragmaKw, tail := [] } context } := by
  apply (keyword_reject_reports_iff .pragmaKw context).mp
  exact ⟨by simp [TokenKindAbsentAt, TokenAt, exampleInput],
    eofReport (.keyword .pragmaKw) context priorRev⟩

/-- Symbol EOF uses a symbol expectation without altering earlier diagnostics. -/
theorem symbol_rejection_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ failure, symbol .semicolon context (exampleInput 3 priorRev) =
      .reject failure (exampleInput 3 priorRev) ∧
      failure.toDiagnostic = {
        span := exampleSpan 11 11
        kind := .unexpected none { head := .symbol .semicolon, tail := [] } context } := by
  apply (symbol_reject_reports_iff .semicolon context).mp
  exact ⟨by simp [TokenKindAbsentAt, TokenAt, exampleInput],
    eofReport (.symbol .semicolon) context priorRev⟩

/-- A hard keyword is not a contextual spelling; the expected category remains
contextual while the actual hard keyword and its original span are preserved. -/
theorem contextual_rejection_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ failure, contextual .from context (exampleInput 0 priorRev) =
      .reject failure (exampleInput 0 priorRev) ∧
      failure.toDiagnostic = {
        span := exampleSpan 0 6
        kind := .unexpected (some (.keyword .pragmaKw))
          { head := .contextual .from, tail := [] } context } := by
  apply (contextual_reject_reports_iff .from context).mp
  refine ⟨by simp [TokenKindAbsentAt, TokenAt, exampleInput], ?_⟩
  apply RejectAtReports.reported
  apply CurrentInputAt.token (current := {
    span := exampleSpan 0 6, value := .keyword .pragmaKw })
  simp [TokenAt, State.declarativeRemainder, exampleInput]

end Solcore.Test.SyntaxParserExactTokenPrimitiveTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserIdentifierTraceProperties
/-! Exact identifier success traces and compatibility with rejection reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserIdentifierTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @identifierHyphenSpelling_iff_contains
example := @identifierDiagnosticTrace_total
example := @IdentifierDiagnosticTrace.trace_unique
example := @RawIdentifierTraceParses.result_unique
example := @IdentifierTraceParses.result_unique
example := @rawIdentifier_success_trace_sound
example := @identifier_success_diagnosticTrace
example := @identifier_success_trace_sound

example (span : SourceSpan) :
    IdentifierDiagnosticTrace { span, value := "a--b" }
      [{ span, kind := .invalidIdentifierHyphen "a--b" }] :=
  .hyphen (by change '-' ∈ "a--b".toList; decide)

example (span : SourceSpan) :
    IdentifierDiagnosticTrace { span, value := "a_b" } [] :=
  .clean (by change ¬ '-' ∈ "a_b".toList; decide)

example (context : ParseContext) {input output : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name output) :
    output.diagnostics = input.diagnostics :=
  rawIdentifier_success_diagnostics_eq context result

example (context : ParseContext) {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output)
    (hyphen : IdentifierHyphenSpelling name.value) :
    output.diagnostics = input.diagnostics ++
      [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] :=
  identifier_success_diagnostics_eq_of_trace context result (.hyphen hyphen)

example (context : ParseContext) {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output)
    (clean : ¬ IdentifierHyphenSpelling name.value) :
    output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using
    identifier_success_diagnostics_eq_of_trace context result (.clean clean)

example (context : ParseContext) {input : State} {name : Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (parsed : RawIdentifierTraceParses input.declarativeRemainder name remainder trace) :
    ∃ output, rawIdentifier context input = .ok name output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (rawIdentifier_trace_success_iff context).mp parsed

example (context : ParseContext) {input output : State} {name : Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (result : rawIdentifier context input = .ok name output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    RawIdentifierTraceParses input.declarativeRemainder name remainder trace :=
  (rawIdentifier_trace_success_iff context).mpr ⟨output, result, after, diagnostics⟩

example (context : ParseContext) {input : State} {name : Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (parsed : IdentifierTraceParses input.declarativeRemainder name remainder trace) :
    ∃ output, identifier context input = .ok name output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (identifier_trace_success_iff context).mp parsed

example (context : ParseContext) {input output : State} {name : Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (result : identifier context input = .ok name output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    IdentifierTraceParses input.declarativeRemainder name remainder trace :=
  (identifier_trace_success_iff context).mpr ⟨output, result, after, diagnostics⟩

example (context : ParseContext) {input output : State} {actual expected : Identifier}
    {remainder : Remainder} {trace : List ParseDiagnostic}
    (result : identifier context input = .ok actual output)
    (parsed : IdentifierTraceParses input.declarativeRemainder expected remainder trace) :
    actual = expected ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases identifier_success_trace_sound context result with
    ⟨actualTrace, actualParsed, actualDiagnostics⟩
  rcases actualParsed.result_unique parsed with ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, actualDiagnostics⟩

example (context : ParseContext) {input : State} {diagnostic : ParseDiagnostic}
    (absent : IdentifierAbsentAt input.declarativeRemainder)
    (reported : RejectAtReports input.file.id input.window.endByte
      { head := .identifier, tail := [] } context input.declarativeRemainder diagnostic) :
    ∃ failure, identifier context input = .reject failure input ∧
      failure.toDiagnostic = diagnostic :=
  (identifier_reject_reports_iff context).mp ⟨absent, reported⟩

end Solcore.Test.SyntaxParserIdentifierTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserInvariantFreeProperties
/-! External consumers for compositional invariant-freedom laws. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserInvariantFreeProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @Parser.InvariantFreeOnValid
example := @Parser.InvariantFreeOnValid.ne_invariant
example := @Parser.invariantFreeOnValid_of_ne_invariant
example := @Parser.invariantFreeOnValid_iff_ne_invariant
example := @Parser.Ordinary.invariantFreeOnValid
example := @Parser.pure_invariantFreeOnValid
example := @Parser.bind_invariantFreeOnValid
example := @Parser.orElse_invariantFreeOnValid
example := @Parser.getState_invariantFreeOnValid
example := @Parser.modifyState_invariantFreeOnValid
example := @Parser.emitDiagnostic_invariantFreeOnValid
example := @Parser.rejectAt_invariantFreeOnValid

example {alpha : Type} {parser : Parser alpha}
    (ordinary : Parser.Ordinary parser) :
    Parser.InvariantFreeOnValid parser :=
  ordinary.invariantFreeOnValid

example {alpha : Type} {parser : Parser alpha}
    (free : Parser.InvariantFreeOnValid parser)
    (input : State) (valid : input.ValidFor)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error :=
  free.ne_invariant input valid error

end Solcore.Test.SyntaxParserInvariantFreeProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserInvariantProperties
/-! External consumers for public frontend invariant classification. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example (file : SourceFile) (diagnostic : LexicalDiagnostic)
    (result : parse file = .error (.lexerInvariant diagnostic)) : False :=
  parse_lexerInvariant_impossible file diagnostic result

example (file : SourceFile) (error : SyntaxInvariantError)
    (result : parse file = .error error) :
    ∃ lexed parserError,
      Lexer.lex file = .ok lexed ∧
      parseLexed file lexed = .error parserError ∧
      error = .parserInvariant parserError :=
  parse_error_parserInvariant file error result

example (file : SourceFile) (error : SyntaxInvariantError)
    (result : parse file = .error error) :
    ∃ lexed parserError,
      Lexer.lex file = .ok lexed ∧
      validateLexed file lexed = .ok () ∧
      parseLexed file lexed = .error parserError ∧
      error = .parserInvariant parserError :=
  parse_error_after_preflight file error result

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserNameProperties
/-! External compile consumers for canonical name provenance contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @acceptToken_ok_state_shape
example := @symbol_ok_state_shape
example := @identifier_ok_state_shape

example (file : SourceFile) (name : QualifiedName)
    (valid : QualifiedName.ValidFor file name) :
    name.span.ValidFor file :=
  valid.1

example (file : SourceFile) (name : QualifiedName)
    (valid : QualifiedName.ValidFor file name)
    (component : Identifier)
    (member : component ∈ name.value.components.toList) :
    component.span.ValidFor file :=
  valid.2 component member

example (context : ParseContext) (phase : ParserPhase) :
    (qualifiedName context phase).ValidFor QualifiedName.ValidFor :=
  qualifiedName_validFor context phase

example := @qualifiedName_ok_state_shape
example := @qualifiedName_preservesTokensOnSuccess
example := @qualifiedName_preservesTokenWindow
example := @qualifiedName_startsAtCurrentTokenOnSuccess
example := @qualifiedName_cursor_lt_onSuccess
example := @qualifiedName_cursorMonotoneOnSuccess

example (context : ParseContext) (phase : ParserPhase) :
    (qualifiedName context phase).ValidFor QualifiedName.ValidFor ∧
      Parser.PreservesTokensOnSuccess (qualifiedName context phase) ∧
      Parser.CursorMonotoneOnSuccess (qualifiedName context phase) ∧
      Parser.StartsAtCurrentTokenOnSuccess
        (qualifiedName context phase) (·.span) :=
  ⟨qualifiedName_validFor context phase,
    qualifiedName_preservesTokensOnSuccess context phase,
    qualifiedName_cursorMonotoneOnSuccess context phase,
    qualifiedName_startsAtCurrentTokenOnSuccess context phase⟩

example (context : ParseContext) (phase : ParserPhase)
    {input next : State} {name : QualifiedName}
    (inputValid : input.ValidFor)
    (result : qualifiedName context phase input = .ok name next) :
    QualifiedName.ValidFor input.file name ∧ next.ValidFor ∧
      next.file = input.file ∧ input.cursor < next.cursor ∧
      next.tokens = input.tokens ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = name.span.startByte := by
  have valid := qualifiedName_validFor context phase input inputValid
  rw [result] at valid
  exact ⟨valid.1, valid.2.1, valid.2.2,
    qualifiedName_cursor_lt_onSuccess context phase result,
    qualifiedName_preservesTokensOnSuccess context phase
      input name next result,
    qualifiedName_startsAtCurrentTokenOnSuccess context phase
      input name next result⟩

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPrimitiveCarrierProperties
/-! External consumers for primitive parser token-carrier laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @acceptToken_preservesTokensOnSuccess
example := @acceptToken_cursor_lt_onSuccess
example := @acceptToken_cursorMonotoneOnSuccess
example := @keyword_preservesTokensOnSuccess
example := @keyword_cursorMonotoneOnSuccess
example := @symbol_preservesTokensOnSuccess
example := @symbol_cursorMonotoneOnSuccess
example := @contextual_preservesTokensOnSuccess
example := @contextual_cursorMonotoneOnSuccess
example := @contextual_startsAtCurrentTokenOnSuccess
example := @rawIdentifier_ok_state_shape
example := @rawIdentifier_preservesTokensOnSuccess
example := @rawIdentifier_cursorMonotoneOnSuccess
example := @identifier_preservesTokensOnSuccess
example := @identifier_cursorMonotoneOnSuccess
example := @yulIdentifier_ok_state_shape
example := @yulIdentifier_preservesTokensOnSuccess
example := @yulIdentifier_cursorMonotoneOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPrimitiveProperties
/-! External compile consumers for primitive parser provenance laws. -/

namespace Tests

open Solcore.Syntax.Parser

example := @rejectAt_reject_validFor
example := @acceptToken_ok_validFor
example := @acceptToken_reject_validFor
example := @rawIdentifier_ok_validFor
example := @rawIdentifier_reject_validFor
example := @identifier_ok_validFor
example := @identifier_reject_validFor
example := @yulIdentifier_ok_validFor
example := @yulIdentifier_reject_validFor
example := @coreLiteral_ok_validFor
example := @coreLiteral_reject_validFor
example := @booleanIdentifier_ok_validFor
example := @booleanIdentifier_reject_validFor

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPrimitiveRejectionDiagnosticProperties
/-! Independent observation and exact uncommitted-diagnostic consumers. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPrimitiveRejectionDiagnosticProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @currentInputAt_total
example := @CurrentInputAt.result_unique
example := @rejectAtReports_total
example := @RejectAtReports.diagnostic_unique
example := @currentInputAt_currentSpan_peekKind
example := @currentInputAt_iff_currentSpan_peekKind
example := @rejectAt_reject_reports
example := @rawIdentifier_eq_rejectAt_of_identifierAbsent
example := @identifier_eq_rejectAt_of_identifierAbsent

example (source : SourceId) (endByte : Nat) (input : Remainder)
    (atEnd : input.endIndex ≤ input.cursor) :
    CurrentInputAt source endByte input
      { source, startByte := endByte, endByte } none :=
  .windowEnd atEnd

example (source : SourceId) (endByte : Nat) (input : Remainder)
    (inside : input.cursor < input.endIndex)
    (missing : input.tokens[input.cursor]? = none) :
    CurrentInputAt source endByte input
      { source, startByte := endByte, endByte } none :=
  .missingToken inside missing

example {alpha : Type} {input : State}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    {diagnostic : ParseDiagnostic}
    (reported : RejectAtReports input.file.id input.window.endByte
      expected context input.declarativeRemainder diagnostic) :
    ∃ failure, rejectAt (α := alpha) input expected context =
      .reject failure input ∧ failure.toDiagnostic = diagnostic :=
  rejectAt_reports_iff.mp reported

example {alpha : Type} {input : State} {failure : Failure}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    {diagnostic : ParseDiagnostic}
    (result : rejectAt (α := alpha) input expected context = .reject failure input)
    (reportEq : failure.toDiagnostic = diagnostic) :
    RejectAtReports input.file.id input.window.endByte expected context
      input.declarativeRemainder diagnostic :=
  (rejectAt_reports_iff (alpha := alpha)).mpr ⟨failure, result, reportEq⟩

example (context : ParseContext) {input : State} {span : SourceSpan}
    {found : Option TokenKind}
    (absent : IdentifierAbsentAt input.declarativeRemainder)
    (observed : CurrentInputAt input.file.id input.window.endByte
      input.declarativeRemainder span found) :
    rawIdentifier context input = .reject {
      span, found, expected := { head := .identifier, tail := [] }, context
    } input := by
  rcases (rawIdentifier_reject_reports_iff context).mp
      ⟨absent, .reported observed⟩ with ⟨failure, result, reportEq⟩
  have payload : failure = {
      span, found, expected := { head := .identifier, tail := [] }, context
    } := Failure.toDiagnostic_injective reportEq
  simpa only [payload] using result

example (context : ParseContext) {input : State} {failure : Failure}
    {diagnostic : ParseDiagnostic}
    (result : rawIdentifier context input = .reject failure input)
    (reportEq : failure.toDiagnostic = diagnostic) :
    IdentifierAbsentAt input.declarativeRemainder ∧
      RejectAtReports input.file.id input.window.endByte
        { head := .identifier, tail := [] } context
        input.declarativeRemainder diagnostic :=
  (rawIdentifier_reject_reports_iff context).mpr ⟨failure, result, reportEq⟩

example (context : ParseContext) {input : State} {diagnostic : ParseDiagnostic}
    (absent : IdentifierAbsentAt input.declarativeRemainder)
    (reported : RejectAtReports input.file.id input.window.endByte
      { head := .identifier, tail := [] } context input.declarativeRemainder diagnostic) :
    ∃ failure, identifier context input = .reject failure input ∧
      failure.toDiagnostic = diagnostic :=
  (identifier_reject_reports_iff context).mp ⟨absent, reported⟩

example (context : ParseContext) {input : State} {failure : Failure}
    {diagnostic : ParseDiagnostic}
    (result : identifier context input = .reject failure input)
    (reportEq : failure.toDiagnostic = diagnostic) :
    IdentifierAbsentAt input.declarativeRemainder ∧
      RejectAtReports input.file.id input.window.endByte
        { head := .identifier, tail := [] } context
        input.declarativeRemainder diagnostic :=
  (identifier_reject_reports_iff context).mpr ⟨failure, result, reportEq⟩

example (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : rawIdentifier context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics :=
  rawIdentifier_reject_diagnostics_eq context result

example (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
    rejected.diagnostics = input.diagnostics :=
  identifier_reject_diagnostics_eq context result

end Solcore.Test.SyntaxParserPrimitiveRejectionDiagnosticProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPrimitiveTotalityProperties
/-! External consumers for primitive parser totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @Parser.Ordinary
example := @Parser.Ordinary.ne_invariant
example := @acceptToken_ordinary
example := @acceptToken_ne_invariant
example := @keyword_ordinary
example := @keyword_ne_invariant
example := @symbol_ordinary
example := @symbol_ne_invariant
example := @contextual_ordinary
example := @contextual_ne_invariant
example := @rawIdentifier_ordinary
example := @rawIdentifier_ne_invariant
example := @identifier_ordinary
example := @identifier_ne_invariant
example := @acceptToken_elementTotalityContract
example := @keyword_elementTotalityContract
example := @symbol_elementTotalityContract
example := @contextual_elementTotalityContract
example := @identifier_elementTotalityContract

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserReservedWords
/-! Reserved-word conformance tests mirrored from the pinned Rust parser. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def reservedSource (name : String) : SourceId := {
  origin := .main
  path := name ++ ".sol"
}

private def parse (name source : String) : IO ParseOutput := do
  let file : SourceFile := { id := reservedSource name, content := source }
  match Parser.parse file with
  | .ok output => pure output
  | .error error => throw (IO.userError
      s!"{name}: parser invariant failed: {reprStr error}")

private def assertAccepted (name source : String) : IO Unit := do
  let output ← parse name source
  unless output.lexicalDiagnostics.isEmpty do
    throw (IO.userError (
      s!"{name}: unexpected lexical diagnostics: " ++
        reprStr output.lexicalDiagnostics))
  unless output.parseDiagnostics.isEmpty do
    throw (IO.userError (
      s!"{name}: unexpected parse diagnostics: " ++
        reprStr output.parseDiagnostics))

private def assertRejectedIdentifier (name source : String) : IO Unit := do
  let output ← parse name source
  unless output.lexicalDiagnostics.isEmpty do
    throw (IO.userError (
      s!"{name}: reserved word should lex without lexical errors: " ++
        reprStr output.lexicalDiagnostics))
  if output.parseDiagnostics.isEmpty then
    throw (IO.userError
      s!"{name}: reserved identifier parsed without diagnostics")

private def testValuesPatternsAndFallbackEntry : IO Unit :=
  assertAccepted "reserved-positive" "
function flip(value: bool) returns (bool) {
  match (value) {
    case true { return false; }
    case false { return true; }
  }
}

contract C {
  fallback() payable {}
}
"

private def testReservedIdentifiers : IO Unit := do
  for (name, source) in [
      ("function-true", "function true() {}"),
      ("function-false", "function false() {}"),
      ("ordinary-function-fallback",
        "contract C { function fallback() {} }"),
      ("let-true", "function f() { let true = false; }"),
      ("field-false", "contract C { false: word; }"),
      ("parameter-fallback", "function f(fallback: word) {}"),
      ("type-true", "function f(value: true) {}"),
      ("import-false", "import {false} from std;"),
      ("enum-fallback", "enum fallback { Value }")
    ] do
    assertRejectedIdentifier name source

/-- Run canonical reserved-word parser regressions. -/
def testSyntaxParserReservedWords : IO Unit := do
  testValuesPatternsAndFallbackEntry
  testReservedIdentifiers

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStateCursorProperties
/-! External consumers for cursor-relative parser span guarantees. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example (state : State) (valid : state.ValidFor)
    (offset : Nat) (token : Token)
    (found : state.peekOffset? offset = some token) :
    token.span.ValidFor state.file :=
  valid.peekOffset?_span_validFor found

example (state : State) (valid : state.ValidFor)
    (consumedIndex offset : Nat) (consumed remaining : Token)
    (consumedFound : state.tokens[consumedIndex]? = some consumed)
    (consumedBeforeCursor : consumedIndex < state.cursor)
    (remainingFound : state.peekOffset? offset = some remaining) :
    consumed.span.endByte ≤ remaining.span.startByte :=
  valid.consumed_end_le_peekOffset_start consumedFound
    consumedBeforeCursor remainingFound

example (state next : State) (valid : state.ValidFor)
    (consumed following : Token)
    (advanced : state.advance? = some (consumed, next))
    (followingFound : next.peek? = some following) :
    consumed.span.endByte ≤ next.currentSpan.startByte :=
  valid.consumed_end_le_currentSpan_start_after_advance
    advanced followingFound

example (state next : State) (token : Token)
    (advanced : state.advance? = some (token, next)) :
    next.peek? = state.peekOffset? 1 :=
  State.peek?_eq_peekOffset?_one_of_advance? advanced

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStateProperties
/-! External compile consumers for canonical parser-state invariants. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example (file : SourceFile) (lexed : LexedFile)
    (valid : lexed.ValidFor file) :
    (State.initial file lexed).ValidFor :=
  State.initial_validFor valid

example (state : State) (valid : state.ValidFor)
    (token : Token) (found : state.peek? = some token) :
    token.span.ValidFor state.file :=
  valid.peek?_span_validFor found

example (state : State) (valid : state.ValidFor) :
    state.currentSpan.ValidFor state.file :=
  valid.currentSpan_validFor

example (state next : State) (valid : state.ValidFor)
    (token : Token) (advanced : state.advance? = some (token, next)) :
    next.ValidFor :=
  valid.advance?_validFor advanced

example (state : State) (valid : state.ValidFor)
    (diagnostic : ParseDiagnostic)
    (diagnosticValid : diagnostic.span.ValidFor state.file) :
    (state.emit diagnostic).ValidFor :=
  valid.emit_validFor diagnostic diagnosticValid

example (state : State) (valid : state.ValidFor)
    (diagnostic : ParseDiagnostic) (member : diagnostic ∈ state.diagnostics) :
    diagnostic.span.ValidFor state.file :=
  valid.diagnostics_span_validFor member

example (file : SourceFile) (failure : Failure)
    (valid : failure.span.ValidFor file) :
    failure.toDiagnostic.span.ValidFor file :=
  failure.toDiagnostic_span_validFor valid

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTrivia
/-! Leading-comment fidelity regressions for canonical syntax parsing. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def triviaSource_variant : SourceId := {
  origin := .main
  path := "parser-trivia.sol"
}

private def checkedParse_variant (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := triviaSource_variant, content }
  match Parser.parse file with
  | .ok output => pure output
  | .error error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")

private def leadingTexts (item : TopItem) : List String :=
  item.leadingComments.map (·.text)

private def itemAt (label : String) (output : ParseOutput)
    (index : Nat) : IO TopItem :=
  match output.parsed.items[index]? with
  | some item => pure item
  | none => throw (IO.userError
      s!"{label}: missing item {index}, only {output.parsed.items.length} present")

private def testAdjacentComments : IO Unit := do
  let output ← checkedParse_variant "CRLF comments"
    "// one\r\n/* two */\r\ntype A = word;"
  let item ← itemAt "CRLF comments" output 0
  assertEqual_variant (leadingTexts item) [" one\r", " two "]
    "CRLF attached comments"

  let adjacent ← checkedParse_variant "adjacent comments"
    "/*a*//*b*/\ntype A = word;"
  let adjacentItem ← itemAt "adjacent comments" adjacent 0
  assertEqual_variant (leadingTexts adjacentItem) ["a", "b"]
    "adjacent attached comments"

private def testBlankLineBoundary : IO Unit := do
  let blank ← checkedParse_variant "blank line"
    "/* doc */\r\n\r\ntype A = word;"
  let blankItem ← itemAt "blank line" blank 0
  assertEqual_variant blankItem.leadingComments [] "blank-line attachment"

  let suffix ← checkedParse_variant "newest comment suffix"
    "// old\n\n// new\ntype A = word;"
  let suffixItem ← itemAt "newest comment suffix" suffix 0
  assertEqual_variant (leadingTexts suffixItem) [" new"]
    "newest direct comment suffix"

private def testCodeBeforeComment : IO Unit := do
  let trailing ← checkedParse_variant "trailing comment"
    "type A = word; // trailing\r\ntype B = word;"
  let first ← itemAt "trailing comment" trailing 0
  let second ← itemAt "trailing comment" trailing 1
  assertEqual_variant first.leadingComments [] "first leading comments"
  assertEqual_variant second.leadingComments [] "trailing comment leakage"

  let code ← checkedParse_variant "code before comments"
    "junk /*a*/ /*b*/\ntype A = word;"
  let declaration ← itemAt "code before comments" code 1
  assertEqual_variant declaration.leadingComments [] "code-before attachment"

  let multiline ← checkedParse_variant "multiline closing tail"
    "/* multi\n*/ /* b */\ntype A = word;"
  let multilineItem ← itemAt "multiline closing tail" multiline 0
  assertEqual_variant multilineItem.leadingComments []
    "multiline closing-tail attachment"

private def testRustUnicodeWhitespace : IO Unit := do
  let nbsp ← checkedParse_variant "nonbreaking space"
    "/*doc*/\u00a0type A = word;"
  let nbspItem ← itemAt "nonbreaking space" nbsp 0
  assertEqual_variant (leadingTexts nbspItem) ["doc"] "NBSP attachment"
  assertEqual_variant nbsp.lexicalDiagnostics.length 1 "NBSP lexical diagnostic"

  let separators ← checkedParse_variant "Unicode separators"
    "/*doc*/\u2028\u2028type A = word;"
  let separatorItem ← itemAt "Unicode separators" separators 0
  assertEqual_variant (leadingTexts separatorItem) ["doc"]
    "Unicode separator attachment"
  assertEqual_variant separators.lexicalDiagnostics.length 2
    "Unicode separator lexical diagnostics"

  let zeroWidth ← checkedParse_variant "zero-width space"
    "/*doc*/\u200btype A = word;"
  let zeroWidthItem ← itemAt "zero-width space" zeroWidth 0
  assertEqual_variant zeroWidthItem.leadingComments []
    "zero-width non-whitespace attachment"

private def testRecoveryOwnership : IO Unit := do
  let output ← checkedParse_variant "recovery comments"
    "// recovery\n+ -; type B = word;"
  let recovered ← itemAt "recovery comments" output 0
  let declaration ← itemAt "recovery comments" output 1
  assertEqual_variant (leadingTexts recovered) [" recovery"]
    "recovery item leading comment"
  assertEqual_variant declaration.leadingComments []
    "recovery comment did not leak"

private def forgedLexed (file : SourceFile)
    (comments : List Comment) : LexedFile := {
  source := file.id
  tokens := []
  comments
  diagnostics := []
}

private def forgedComment (file : SourceFile)
    (startByte endByte : Nat) : Comment := {
  kind := .block
  text := ""
  span := { source := file.id, startByte, endByte }
}

private def expectInvalidSecondComment (label : String)
    (file : SourceFile) (comments : List Comment) : IO Unit :=
  match Parser.parseLexed file (forgedLexed file comments) with
  | .error (.invalidCommentSpan 1 _) => pure ()
  | result => throw (IO.userError
      s!"{label}: expected second-comment invariant, got {reprStr result}")

private def testForgedCommentOrder : IO Unit := do
  let file : SourceFile := {
    id := triviaSource_variant
    content := "abcdefghijklmnop"
  }
  expectInvalidSecondComment "out-of-order comments" file [
    forgedComment file 5 7,
    forgedComment file 2 4
  ]
  expectInvalidSecondComment "overlapping comments" file [
    forgedComment file 2 6,
    forgedComment file 5 8
  ]

/-- Run canonical parser leading-comment regressions. -/
def testSyntaxParserTrivia : IO Unit := do
  testAdjacentComments
  testBlankLineBoundary
  testCodeBeforeComment
  testRustUnicodeWhitespace
  testRecoveryOwnership
  testForgedCommentOrder

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTriviaSelectionProperties
/-! External consumer for comment-selection provenance. -/

namespace Tests

open Solcore.Syntax.Parser

example := @commentsDirectlyBefore_mem

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTriviaValidityProperties
/-! External consumers for canonical comment-attachment validity. -/

namespace Tests

open Solcore.Syntax.Parser

example := @commentsDirectlyBefore_validFor
example := @TriviaInternals.attachEnumConstructorComments_mem
example := @TriviaInternals.attachEnumConstructorComments_validFor
example := @TriviaInternals.attachEnumConstructors_validFor
example := @TriviaInternals.attachEnumComments_validFor
example := @TriviaInternals.attachTraitMethodComments_validFor
example := @TriviaInternals.attachTraitComments_validFor
example := @TriviaInternals.attachImplMethodComments_validFor
example := @TriviaInternals.attachImplComments_validFor
example := @TriviaInternals.attachContractMemberComments_validFor
example := @TriviaInternals.attachContractComments_validFor
example := @attachTopItemComments_leading_validFor
example := @attachTopItemComments_trait_validFor
example := @attachTopItemComments_impl_validFor
example := @attachTopItemComments_validFor
example := @attachTopItemComments_span
example := @attachTopItemComments_list_validFor
example := @parsedFile_withAttachedComments_validFor

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxSourceSpanProperties
/-! External compile consumers for canonical source-span composition laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example (file : SourceFile) (first last : SourceSpan)
    (firstValid : first.ValidFor file) (lastValid : last.ValidFor file)
    (ordered : first.startByte ≤ last.endByte) :
    (SourceSpan.cover first last).ValidFor file :=
  SourceSpan.cover_validFor firstValid lastValid ordered

example (file : SourceFile) (first last : SourceSpan)
    (firstValid : first.ValidFor file)
    (endOrdered : first.endByte ≤ last.endByte) :
    (SourceSpan.cover first last).Contains first :=
  SourceSpan.cover_contains_first firstValid endOrdered

example (file : SourceFile) (first last : SourceSpan)
    (firstValid : first.ValidFor file) (lastValid : last.ValidFor file)
    (startOrdered : first.startByte ≤ last.startByte) :
    (SourceSpan.cover first last).Contains last :=
  SourceSpan.cover_contains_last firstValid lastValid startOrdered

end Tests
end
