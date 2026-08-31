import Solcore.Syntax.Parser

/-! Regression coverage for lexical-to-parse diagnostic cascade suppression. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def diagnosticSource : SourceId := {
  origin := .main
  path := "parser-diagnostic-suppression.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := diagnosticSource, content }
  let output ← match Parser.parse file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"{label}: parser invariant failed: {reprStr error}")
  unless output.lexicalDiagnostics.all
      (fun diagnostic => diagnostic.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid lexical diagnostic span")
  unless output.parseDiagnostics.all
      (fun diagnostic => diagnostic.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid parse diagnostic span")
  pure output

private def assertOneInvalidToken
    (output : ParseOutput) (label : String) : IO Unit := do
  match output.lexicalDiagnostics with
  | [{ kind := .invalidToken, .. }] => pure ()
  | diagnostics => throw (IO.userError
      s!"{label}: expected one invalid-token diagnostic, got \
        {reprStr diagnostics}")

private def aliasName? (item : TopItem) : Option String :=
  match item.value with
  | .typeAlias declaration => some declaration.value.name.value
  | _ => none

private def assertSingleErrorExpression
    (body : Block) (label : String) : IO Unit :=
  match body.value with
  | [{ value := .expression { value := .error, .. } true, .. }] => pure ()
  | statements => throw (IO.userError
      s!"{label}: expected one recovered expression, got {reprStr statements}")

private def testSameLineSuppression : IO Unit := do
  let output ← checkedParse "same-line cascade" "§ type Broken = ;"
  assertOneInvalidToken output "same-line cascade"
  assertEqual output.parseDiagnostics []
    "same-line parse cascade suppression"
  assertEqual output.parsed.items.length 0
    "same-line failed declaration"

private def testOverlappingSuppression : IO Unit := do
  let content := "type Broken = ;"
  let file : SourceFile := { id := diagnosticSource, content }
  let lexed ← match Lexer.lex file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"overlap setup lexer invariant failed: {reprStr error}")
  let semicolon ← match lexed.tokens.getLast? with
    | some token => pure token
    | none => throw (IO.userError "overlap setup has no semicolon token")
  let overlapping : LexedFile := {
    lexed with
    diagnostics := [{
      span := semicolon.span
      kind := .invalidToken
    }]
  }
  let output ← match Parser.parseLexed file overlapping with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"overlap parse invariant failed: {reprStr error}")
  assertOneInvalidToken output "overlap"
  assertEqual output.parseDiagnostics []
    "overlapping parse cascade suppression"
  assertEqual output.parsed.items.length 0
    "overlap failed declaration"

private def testSpaceOnlyAdjacencySuppression : IO Unit := do
  let output ← checkedParse "space-only adjacency"
    "type Broken = §   ;"
  assertOneInvalidToken output "space-only adjacency"
  assertEqual (output.lexicalDiagnostics.map fun diagnostic =>
      byteRange diagnostic.span) [(14, 16)]
    "space-only lexical span"
  assertEqual output.parseDiagnostics []
    "space-only adjacent parse cascade suppression"

private def testNextLineDiagnosticSurvives : IO Unit := do
  let output ← checkedParse "next-line top-level error"
    "§\n;\ntype Kept = word;"
  assertOneInvalidToken output "next-line top-level error"
  match output.parseDiagnostics with
  | [{ span, kind := .recovered .topItem }] =>
      assertEqual (byteRange span) (3, 4)
        "independent next-line diagnostic span"
  | diagnostics => throw (IO.userError
      s!"independent next-line diagnostic changed: {reprStr diagnostics}")
  match output.parsed.items with
  | [{ value := .error, .. }, kept] =>
      assertEqual (aliasName? kept) (some "Kept")
        "item after independent next-line error"
  | items => throw (IO.userError
      s!"next-line recovery items changed: {reprStr items}")

private def testBodyIsolationSuppressesLexCascade : IO Unit := do
  let source := String.intercalate "\n" [
    "function bad() { let x = §; }",
    "type Kept = word;"
  ]
  let output ← checkedParse "body lexical cascade" source
  assertOneInvalidToken output "body lexical cascade"
  assertEqual output.parseDiagnostics []
    "body parse cascade suppression"
  match output.parsed.items with
  | [
      { value := .function bad, .. },
      kept
    ] =>
      assertEqual bad.value.signature.name.value "bad"
        "isolated function name"
      assertSingleErrorExpression bad.value.body
        "lexically broken fallback body"
      assertEqual (aliasName? kept) (some "Kept")
        "item after lexically broken body"
  | items => throw (IO.userError
      s!"body lexical isolation items changed: {reprStr items}")

private def testBodyNextLineDiagnosticSurvives : IO Unit := do
  let source := String.intercalate "\n" [
    "function bad() {",
    "  §",
    "  let x = ;",
    "}",
    "type Kept = word;"
  ]
  let output ← checkedParse "body next-line error" source
  assertOneInvalidToken output "body next-line error"
  match output.parseDiagnostics with
  | [{ span, kind := .unexpected (some (.symbol .semicolon)) _ .expression }] =>
      assertEqual (byteRange span) (32, 33)
        "independent body diagnostic span"
  | diagnostics => throw (IO.userError
      s!"independent body diagnostic changed: {reprStr diagnostics}")
  match output.parsed.items with
  | [{ value := .function bad, .. }, kept] =>
      assertSingleErrorExpression bad.value.body
        "independently bad fallback body"
      assertEqual (aliasName? kept) (some "Kept")
        "item after independently bad body"
  | items => throw (IO.userError
      s!"body next-line items changed: {reprStr items}")

private def testTopRecoveryDoesNotDuplicateLexError : IO Unit := do
  let output ← checkedParse "top recovery duplication"
    "§ ;\ntype Kept = word;"
  assertOneInvalidToken output "top recovery duplication"
  assertEqual output.parseDiagnostics []
    "top recovery duplicate diagnostic"
  match output.parsed.items with
  | [{ value := .error, .. }, kept] =>
      assertEqual (aliasName? kept) (some "Kept")
        "item after suppressed top recovery"
  | items => throw (IO.userError
      s!"suppressed top recovery items changed: {reprStr items}")

private def testContractRecoveryDoesNotDuplicateLexError : IO Unit := do
  let source := String.intercalate "\n" [
    "contract C { § ; function good() {} }",
    "type Kept = word;"
  ]
  let output ← checkedParse "contract recovery duplication" source
  assertOneInvalidToken output "contract recovery duplication"
  assertEqual output.parseDiagnostics []
    "contract recovery duplicate diagnostic"
  match output.parsed.items with
  | [
      { value := .contract contract, .. },
      kept
    ] =>
      assertEqual (aliasName? kept) (some "Kept")
        "item after suppressed contract recovery"
      match contract.value.members with
      | [
          { value := .error, .. },
          { value := .function good, .. }
        ] =>
          assertEqual good.value.signature.name.value "good"
            "member after suppressed contract recovery"
      | members => throw (IO.userError
          s!"contract recovery members changed: {reprStr members}")
  | items => throw (IO.userError
      s!"contract recovery items changed: {reprStr items}")

private def testLexFreeRecoveryPairsRemain : IO Unit := do
  let core ← checkedParse "lex-free Core recovery"
    "function core() { return pair(+ -, 0); }"
  assertEqual core.lexicalDiagnostics [] "lex-free Core lexical diagnostics"
  assertEqual (core.parseDiagnostics.map (fun diagnostic => diagnostic.kind)) [
    .unexpected (some (.symbol .plus))
      { head := .expression, tail := [] } .expression,
    .recovered .expressionAtom
  ] "lex-free Core recovery pair"

  let yul ← checkedParse "lex-free Yul recovery"
    "function yul() { assembly { let x := pair(+ -, 0) } }"
  assertEqual yul.lexicalDiagnostics [] "lex-free Yul lexical diagnostics"
  assertEqual (yul.parseDiagnostics.map (fun diagnostic => diagnostic.kind)) [
    .unexpected (some (.symbol .plus))
      { head := .yulIdentifier, tail := [.yulLiteral] } .yulExpression,
    .recovered .yulExpression
  ] "lex-free Yul recovery pair"

/-- Run lexical-to-parse diagnostic cascade suppression regressions. -/
def testSyntaxParserDiagnosticSuppression : IO Unit := do
  testSameLineSuppression
  testOverlappingSuppression
  testSpaceOnlyAdjacencySuppression
  testNextLineDiagnosticSurvives
  testBodyIsolationSuppressesLexCascade
  testBodyNextLineDiagnosticSurvives
  testTopRecoveryDoesNotDuplicateLexError
  testContractRecoveryDoesNotDuplicateLexError
  testLexFreeRecoveryPairsRemain

end Tests
