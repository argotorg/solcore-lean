import Solcore.Test.SyntaxLexerCatalog

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

private def assertEqual {α : Type} [BEq α] [Repr α]
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
      assertEqual output.source file.id s!"{label} source owner"
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
  assertEqual (tokenKinds output) [
      .symbol .colonEqual, .symbol .equal,
      .symbol .logicalAnd, .symbol .amp,
      .symbol .tildeEqual, .symbol .tilde,
      .decimalLiteral "0", .identifier "x",
      .decimalLiteral "0", .identifier "xz",
      .hexadecimalLiteral "0x1", .identifier "g"
    ] "maximal-munch tokens"
  assertEqual (tokenRanges output) [
      (0, 2), (2, 3), (4, 6), (6, 7), (8, 10), (10, 11),
      (12, 13), (13, 14), (15, 16), (16, 18), (19, 22), (22, 23)
    ] "maximal-munch Rust spans"
  assertEqual output.diagnostics [] "maximal-munch diagnostics"

private def testUnicode : IO Unit := do
  let output ← checkedLex "Unicode identifiers" "λ2 四٤_ 𐐀9 § z"
  assertEqual (tokenKinds output) [
      .identifier "λ2", .identifier "四٤_", .identifier "𐐀9",
      .identifier "z"
    ] "Unicode identifier tokens"
  assertEqual (tokenRanges output)
    [(0, 3), (4, 10), (11, 16), (20, 21)]
    "Unicode identifier Rust spans"
  assertEqual (diagnosticViews output)
    [(.invalidToken, (17, 19))]
    "Unicode invalid-scalar span"

private def testYulAndMeta : IO Unit := do
  let output ← checkedLex "Yul names and meta"
    "λ2 := 0xF += _x $y value$tail `z` ${q}"
  assertEqual (tokenKinds output) [
      .identifier "λ2", .symbol .colonEqual, .hexadecimalLiteral "0xF",
      .symbol .plusEqual, .yulIdentifier "_x", .yulIdentifier "$y",
      .yulIdentifier "value$tail", .yulMetaBacktick "`z`",
      .yulMetaInterpolation "${q}"
    ] "Yul and meta tokens"
  assertEqual (tokenRanges output) [
      (0, 3), (4, 6), (7, 10), (11, 13), (14, 16), (17, 19),
      (20, 30), (31, 34), (35, 39)
    ] "Yul and meta Rust spans"
  assertEqual output.diagnostics [] "Yul and meta diagnostics"

  let interpolation ← checkedLex "unterminated interpolation" "${unterminated"
  assertEqual (tokenKinds interpolation) [
      .yulIdentifier "$", .symbol .leftBrace, .identifier "unterminated"
    ] "unterminated interpolation fallback"
  assertEqual (tokenRanges interpolation) [(0, 1), (1, 2), (2, 14)]
    "unterminated interpolation Rust spans"

  let backtick ← checkedLex "unterminated backtick" "`unterminated"
  assertEqual backtick.tokens [] "unterminated backtick tokens"
  assertEqual (diagnosticViews backtick)
    [(.invalidToken, (0, 13))]
    "unterminated backtick Rust span"

private def testStringsAndRecovery : IO Unit := do
  let strings ← checkedLex "strings" "\"ok\\n\" \"bad\\q\" after"
  assertEqual (tokenKinds strings)
    [.stringLiteral "\"ok\\n\"", .identifier "after"]
    "string recovery tokens"
  assertEqual (tokenRanges strings) [(0, 6), (15, 20)]
    "string recovery token spans"
  assertEqual (diagnosticViews strings)
    [(.invalidStringEscape, (7, 14))]
    "invalid string escape Rust span"

  let unterminated ← checkedLex "unterminated string" "\"unterminated after"
  assertEqual unterminated.tokens [] "unterminated string tokens"
  assertEqual (diagnosticViews unterminated)
    [(.invalidToken, (0, 19))]
    "unterminated string Rust span"

  let accumulated ← checkedLex "diagnostic accumulation" "§ \"bad\\q\" ¤ ok"
  assertEqual (tokenKinds accumulated) [.identifier "ok"]
    "diagnostic accumulation tokens"
  assertEqual (tokenRanges accumulated) [(14, 16)]
    "diagnostic accumulation token span"
  assertEqual (diagnosticViews accumulated) [
      (.invalidToken, (0, 2)),
      (.invalidStringEscape, (3, 10)),
      (.invalidToken, (11, 13))
    ] "diagnostic accumulation order and Rust spans"

private def testComments : IO Unit := do
  let comments ← checkedLex "comments"
    "x // cr\r\ny /* outer /* inner */ end */ z"
  assertEqual (tokenKinds comments)
    [.identifier "x", .identifier "y", .identifier "z"]
    "comment-separated tokens"
  assertEqual (tokenRanges comments) [(0, 1), (9, 10), (39, 40)]
    "comment-separated Rust token spans"
  assertEqual (commentViews comments) [
      (.line, " cr\r", (2, 8)),
      (.block, " outer /* inner */ end ", (11, 38))
    ] "comment text and Rust spans"
  assertEqual comments.diagnostics [] "closed comment diagnostics"

  let unterminated ← checkedLex "unterminated block comment" "x /* no"
  assertEqual (tokenKinds unterminated) [.identifier "x"]
    "unterminated block prefix token"
  assertEqual unterminated.comments [] "unterminated block comments"
  assertEqual (diagnosticViews unterminated)
    [(.unterminatedBlockComment, (2, 7))]
    "unterminated block Rust span"

private def testIdentifierBoundaries : IO Unit := do
  let words ← checkedLex "identifier boundaries"
    "if ifx xif if-x true$x foo-2 foo--bar"
  assertEqual (tokenKinds words) [
      .keyword .ifKw, .identifier "ifx", .identifier "xif",
      .identifier "if-x", .yulIdentifier "true$x",
      .identifier "foo", .symbol .minus, .decimalLiteral "2",
      .identifier "foo", .symbol .minus, .symbol .minus, .identifier "bar"
    ] "keyword, hyphen, and Yul identifier boundaries"
  assertEqual (tokenRanges words) [
      (0, 2), (3, 6), (7, 10), (11, 15), (16, 22),
      (23, 26), (26, 27), (27, 28),
      (29, 32), (32, 33), (33, 34), (34, 37)
    ] "identifier-boundary Rust spans"

  let marked ← checkedLex "marked identifiers" "_ $ _$value"
  assertEqual (tokenKinds marked)
    [.symbol .underscore, .yulIdentifier "$", .yulIdentifier "_$value"]
    "lone underscore and marked identifiers"
  assertEqual (tokenRanges marked) [(0, 1), (2, 3), (4, 11)]
    "marked-identifier Rust spans"

private def testWhitespaceAndStringNewlines : IO Unit := do
  let whitespace ← checkedLex "ASCII whitespace" "a \t\n\r\u000c b"
  assertEqual (tokenKinds whitespace) [.identifier "a", .identifier "b"]
    "ASCII whitespace tokens"
  assertEqual (tokenRanges whitespace) [(0, 1), (7, 8)]
    "ASCII whitespace spans"

  let rawNewline ← checkedLex "raw string newline" "\"line\nbreak\" after"
  assertEqual (tokenKinds rawNewline)
    [.stringLiteral "\"line\nbreak\"", .identifier "after"]
    "raw-newline string tokens"
  assertEqual (tokenRanges rawNewline) [(0, 12), (13, 18)]
    "raw-newline string Rust spans"
  assertEqual rawNewline.diagnostics [] "raw-newline string diagnostics"

  let escapedLf ← checkedLex "escaped LF string prefix" "\"bad\\\nafter"
  assertEqual (tokenKinds escapedLf) [.identifier "after"]
    "escaped-LF recovery token"
  assertEqual (tokenRanges escapedLf) [(6, 11)]
    "escaped-LF recovery token span"
  assertEqual (diagnosticViews escapedLf)
    [(.invalidToken, (0, 5))]
    "escaped-LF invalid-prefix span"

private def testEmptyComments : IO Unit := do
  let output ← checkedLex "empty comments" "//\n/**///"
  assertEqual output.tokens [] "empty-comment tokens"
  assertEqual (commentViews output) [
      (.line, "", (0, 2)),
      (.block, "", (3, 7)),
      (.line, "", (7, 9))
    ] "empty and EOF comment spans"
  assertEqual output.diagnostics [] "empty-comment diagnostics"

private def hyphenNameChars : Nat → List Char → List Char
  | 0, reversed => reversed.reverse
  | count + 1, reversed =>
      hyphenNameChars count ('a' :: '-' :: reversed)

private def testLongScans : IO Unit := do
  let longName := String.ofList (List.replicate 100000 'a')
  let nameOutput ← checkedLex "long identifier" longName
  match nameOutput.tokens with
  | [{ value := .identifier text, .. }] =>
      assertEqual text.length 100000 "long identifier length"
  | tokens =>
      throw (IO.userError
        s!"long identifier produced {tokens.length} tokens")

  let commentOutput ← checkedLex "long line comment" ("//" ++ longName)
  match commentOutput.comments with
  | [{ kind := .line, text, .. }] =>
      assertEqual text.length 100000 "long line-comment length"
  | comments =>
      throw (IO.userError
        s!"long line comment produced {comments.length} comments")

  let hyphenName := String.ofList (hyphenNameChars 10000 ['a'])
  let hyphenOutput ← checkedLex "long hyphen identifier" hyphenName
  assertEqual hyphenOutput.tokens.length 1
    "long hyphen identifier token count"
  assertEqual hyphenOutput.diagnostics []
    "long hyphen identifier diagnostics"

private def testInternalFuelBranch : IO Unit := do
  let file : SourceFile := { id := lexerSource, content := "x" }
  match Lexer.lexLoop file 0 (Lexer.State.initial file) with
  | .ok output =>
      throw (IO.userError
        s!"zero-fuel lexer unexpectedly succeeded: {reprStr output}")
  | .error diagnostic =>
      assertEqual diagnostic.kind .internalFuelExhausted
        "zero-fuel internal diagnostic"
      assertEqual (byteRange diagnostic.span) (0, 0)
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
