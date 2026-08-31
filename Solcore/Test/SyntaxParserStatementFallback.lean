import Solcore.Syntax.Parser
import Solcore.Syntax.Parser.Term

/-! Regression coverage for canonical Core statement-choice fallback. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def fallbackSource : SourceId := {
  origin := .main
  path := "parser-statement-fallback.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private structure BlockRun where
  value : Block
  state : Parser.State

private def runBlock (label content : String) : IO BlockRun := do
  let file : SourceFile := { id := fallbackSource, content }
  let lexed ← match Lexer.lex file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"{label}: lexer invariant failed: {reprStr error}")
  assertEqual lexed.diagnostics [] s!"{label} lexical diagnostics"
  match Parser.block .allow (Parser.State.initial file lexed) with
  | .ok value state =>
      unless state.atEnd do
        throw (IO.userError
          s!"{label}: left {state.remainingCount} token(s)")
      pure { value, state }
  | .reject failure _ => throw (IO.userError
      s!"{label}: block rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")

private def assertRecoveredPair
    (label : String) (block : Block) : IO Unit :=
  match block.value with
  | [
      { value := .expression { value := .error, .. } true, .. },
      { value := .letDecl name none none, .. }
    ] => assertEqual name.value "kept" s!"{label} following statement"
  | statements => throw (IO.userError
      s!"{label}: fallback statements changed: {reprStr statements}")

private structure FallbackCase where
  label : String
  source : String
  failureRange : ByteRange
  failureKind : ParseDiagnosticKind

private def expressionFailure (found : TokenKind) : ParseDiagnosticKind :=
  .unexpected (some found) { head := .expression, tail := [] } .expression

private def statementFailure (found : TokenKind)
    (expected : ParseExpectation) : ParseDiagnosticKind :=
  .unexpected (some found) { head := expected, tail := [] } .statement

private def fallbackCases : List FallbackCase := [
  {
    label := "let initializer"
    source := "{ let value = ; let kept; }"
    failureRange := (14, 15)
    failureKind := expressionFailure (.symbol .semicolon)
  },
  {
    label := "return expression"
    source := "{ return value + ; let kept; }"
    failureRange := (17, 18)
    failureKind := expressionFailure (.symbol .semicolon)
  },
  {
    label := "break terminator"
    source := "{ break value; let kept; }"
    failureRange := (8, 13)
    failureKind := statementFailure (.identifier "value")
      (.symbol .semicolon)
  },
  {
    label := "continue terminator"
    source := "{ continue value; let kept; }"
    failureRange := (11, 16)
    failureKind := statementFailure (.identifier "value")
      (.symbol .semicolon)
  },
  {
    label := "if opening"
    source := "{ if value; let kept; }"
    failureRange := (5, 10)
    failureKind := statementFailure (.identifier "value")
      (.symbol .leftParen)
  },
  {
    label := "match opening"
    source := "{ match value; let kept; }"
    failureRange := (8, 13)
    failureKind := .unexpected (some (.identifier "value"))
      { head := .symbol .leftParen, tail := [] } .expression
  },
  {
    label := "for opening"
    source := "{ for value; let kept; }"
    failureRange := (6, 11)
    failureKind := statementFailure (.identifier "value")
      (.symbol .leftParen)
  },
  {
    label := "assembly opening"
    source := "{ assembly value; let kept; }"
    failureRange := (11, 16)
    failureKind := .unexpected (some (.identifier "value"))
      { head := .symbol .leftBrace, tail := [] } .yulStatement
  },
  {
    label := "nested block"
    source := "{ { ; let kept; }"
    failureRange := (4, 5)
    failureKind := expressionFailure (.symbol .semicolon)
  }
]

private def testRecognizedBranchesUseFallbackShape : IO Unit := do
  for test in fallbackCases do
    let run ← runBlock test.label test.source
    assertRecoveredPair test.label run.value
    assertEqual (run.state.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
        (test.failureRange, test.failureKind)
      ] s!"{test.label} sole primary diagnostic"

private def semicolonRanges (tokens : List Token) : List ByteRange :=
  tokens.filterMap fun token =>
    if token.value == .symbol .semicolon then
      some (byteRange token.span)
    else
      none

private def testIndependentSameLineFailuresAndBodyIsolation : IO Unit := do
  let source := String.intercalate "\n" [
    "function broken() { let first = ; let second = ; }",
    "type Kept = word;"
  ]
  let file : SourceFile := { id := fallbackSource, content := source }
  let output ← match Parser.parse file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"same-line fallback parser invariant: {reprStr error}")
  assertEqual output.lexicalDiagnostics []
    "same-line fallback lexical diagnostics"
  let invalidSemicolons := (semicolonRanges output.tokens).take 2
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind))
    (invalidSemicolons.map fun span =>
      (span, expressionFailure (.symbol .semicolon)))
    "independent same-line primary diagnostics"
  match output.parsed.items with
  | [
      { value := .function function, .. },
      { value := .typeAlias alias, .. }
    ] =>
      assertEqual function.value.signature.name.value "broken"
        "malformed function name"
      assertEqual alias.value.name.value "Kept" "following top-level item"
      match function.value.body.value with
      | [
          { value := .expression { value := .error, .. } true, .. },
          { value := .expression { value := .error, .. } true, .. }
        ] => pure ()
      | body => throw (IO.userError
          s!"body isolation replaced recovered statements: {reprStr body}")
  | items => throw (IO.userError
      s!"same-line fallback top-level shape changed: {reprStr items}")

/-- Run statement-choice fallback and body-isolation regressions. -/
def testSyntaxParserStatementFallback : IO Unit := do
  testRecognizedBranchesUseFallbackShape
  testIndependentSameLineFailuresAndBodyIsolation

end Tests
