import Solcore.Syntax.Parser
import Solcore.Syntax.Parser.Term

/-! Regressions for transactional ordered choice in inline-Yul statements. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def choiceSource : SourceId := {
  origin := .main
  path := "parser-yul-choice-recovery.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private structure BodyRun where
  value : Parser.YulParsedBlock
  state : Parser.State
  tokens : List Token

private def runBody (label content : String) : IO BodyRun := do
  let file : SourceFile := { id := choiceSource, content }
  let lexed ← match Lexer.lex file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"{label}: lexer invariant failed: {reprStr error}")
  assertEqual lexed.diagnostics [] s!"{label} lexical diagnostics"
  match Parser.yulBody (Parser.State.initial file lexed) with
  | .ok value state =>
      unless state.atEnd do
        throw (IO.userError
          s!"{label}: left {state.remainingCount} token(s)")
      pure { value, state, tokens := lexed.tokens }
  | .reject failure _ => throw (IO.userError
      s!"{label}: body rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")

private def yulExpressionFailure (found : TokenKind) : ParseDiagnosticKind :=
  .unexpected (some found) {
    head := .yulIdentifier
    tail := [.yulLiteral]
  } .yulExpression

private def yulNameFailure (found : TokenKind) : ParseDiagnosticKind :=
  .unexpected (some found) {
    head := .yulIdentifier
    tail := []
  } .yulExpression

private def yulStatementFailure (found : TokenKind)
    (expected : ParseExpectation) : ParseDiagnosticKind :=
  .unexpected (some found) {
    head := expected
    tail := []
  } .yulStatement

private def rightBraceRanges (tokens : List Token) : List ByteRange :=
  tokens.filterMap fun token =>
    if token.value == .symbol .rightBrace then
      some (byteRange token.span)
    else
      none

private def assertExpressionError
    (label : String) (body : List YulStmt) : IO Unit :=
  match body with
  | [{ value := .expression { value := .error, .. }, .. }] => pure ()
  | statements => throw (IO.userError
      s!"{label}: fallback shape changed: {reprStr statements}")

private structure RecognizedCase where
  label : String
  source : String
  failureKind : ParseDiagnosticKind

private def rightBrace : TokenKind := .symbol .rightBrace

private def recognizedCases : List RecognizedCase := [
  {
    label := "let"
    source := "{ let }"
    failureKind := yulNameFailure rightBrace
  },
  {
    label := "if"
    source := "{ if }"
    failureKind := yulExpressionFailure rightBrace
  },
  {
    label := "for"
    source := "{ for }"
    failureKind := yulStatementFailure rightBrace (.symbol .leftBrace)
  },
  {
    label := "switch"
    source := "{ switch }"
    failureKind := yulExpressionFailure rightBrace
  },
  {
    label := "function"
    source := "{ function }"
    failureKind := yulNameFailure rightBrace
  },
  {
    label := "return"
    source := "{ return }"
    failureKind := .unexpected (some rightBrace) {
      head := .symbol .leftParen
      tail := []
    } .yulExpression
  }
]

private def testRecognizedBranchesUseExpressionFallback : IO Unit := do
  for test in recognizedCases do
    let run ← runBody s!"recognized Yul {test.label}" test.source
    assertExpressionError test.label run.value.body
    let closing := (rightBraceRanges run.tokens).getD 0 (0, 0)
    assertEqual (run.state.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
        (closing, test.failureKind)
      ] s!"{test.label} sole farthest primary diagnostic"

private def testIndependentFailuresKeepFollowingStatement : IO Unit := do
  let source := "{ { let } { if } { for } leave }"
  let run ← runBody "independent recognized failures" source
  match run.value.body with
  | [
      { value := .block [
          { value := .expression { value := .error, .. }, .. }
        ], .. },
      { value := .block [
          { value := .expression { value := .error, .. }, .. }
        ], .. },
      { value := .block [
          { value := .expression { value := .error, .. }, .. }
        ], .. },
      { value := .leave, .. }
    ] => pure ()
  | body => throw (IO.userError
      s!"independent fallback body changed: {reprStr body}")
  let failureRanges := (rightBraceRanges run.tokens).take 3
  assertEqual (run.state.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
        (failureRanges.getD 0 (0, 0), yulNameFailure rightBrace),
        (failureRanges.getD 1 (0, 0), yulExpressionFailure rightBrace),
        (failureRanges.getD 2 (0, 0),
          yulStatementFailure rightBrace (.symbol .leftBrace))
      ] "independent primary diagnostics"

private def testGenericJunkUsesStatementRecovery : IO Unit := do
  let source := "{ , junk }"
  let run ← runBody "generic Yul junk" source
  match run.value.body with
  | [{ value := .error, span }] =>
      assertEqual (byteRange span) (2, 8) "generic recovery span"
  | body => throw (IO.userError
      s!"generic junk recovery changed: {reprStr body}")
  assertEqual (run.state.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
        ((2, 3), yulExpressionFailure (.symbol .comma)),
        ((2, 8), .recovered .yulStatement)
      ] "generic statement recovery diagnostics"

private def testAssemblyKeepsCoreAndTopLevelFollowers : IO Unit := do
  let source := String.intercalate "\n" [
    "function broken() {",
    "  assembly { let }",
    "  let kept;",
    "}",
    "type Kept = word;"
  ]
  let file : SourceFile := { id := choiceSource, content := source }
  let output ← match Parser.parse file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"assembly choice parser invariant: {reprStr error}")
  assertEqual output.lexicalDiagnostics [] "assembly choice lexical diagnostics"
  let assemblyClosing := (rightBraceRanges output.tokens).getD 0 (0, 0)
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
        (assemblyClosing, yulNameFailure rightBrace)
      ] "assembly sole primary diagnostic"
  match output.parsed.items with
  | [
      { value := .function function, .. },
      { value := .typeAlias alias, .. }
    ] =>
      assertEqual alias.value.name.value "Kept" "following top-level item"
      match function.value.body.value with
      | [
          { value := .assembly [
              { value := .expression { value := .error, .. }, .. }
            ], .. },
          { value := .letDecl name none none, .. }
        ] => assertEqual name.value "kept" "following Core statement"
      | body => throw (IO.userError
          s!"assembly body isolation changed: {reprStr body}")
  | items => throw (IO.userError
      s!"assembly following items changed: {reprStr items}")

/-- Run inline-Yul ordered-choice and recovery-boundary regressions. -/
def testSyntaxParserYulChoiceRecovery : IO Unit := do
  testRecognizedBranchesUseExpressionFallback
  testIndependentFailuresKeepFollowingStatement
  testGenericJunkUsesStatementRecovery
  testAssemblyKeepsCoreAndTopLevelFollowers

end Tests
