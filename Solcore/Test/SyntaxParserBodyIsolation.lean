import Solcore.Syntax.Parser

/-! Regression coverage for balanced Core-body parsing and local fallback. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def isolationSource : SourceId := {
  origin := .main
  path := "parser-body-isolation.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := isolationSource, content }
  let output ← match Parser.parse file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"{label}: parser invariant failed: {reprStr error}")
  assertEqual output.lexicalDiagnostics [] s!"{label} lexical diagnostics"
  unless output.parsed.items.all (fun item => item.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid item span")
  unless output.parseDiagnostics.all
      (fun diagnostic => diagnostic.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid diagnostic span")
  pure output

private def missingExpression : ParseDiagnosticKind :=
  .unexpected (some (.symbol .semicolon))
    { head := .expression, tail := [] } .expression

private def assertSingleErrorExpression
    (body : Block) (label : String) : IO Unit :=
  match body.value with
  | [{ value := .expression { value := .error, .. } true, .. }] => pure ()
  | statements => throw (IO.userError
      s!"{label}: expected one recovered expression, got {reprStr statements}")

private def testTopLevelIsolationAndDiagnosticOrder : IO Unit := do
  let source := String.intercalate "\n" [
    "function bad() public { x = y let broken = ; }",
    "type Kept = word;",
    "function good() { return; }"
  ]
  let output ← checkedParse "top-level body isolation" source
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((15, 21), .constraintViolation
      (.modifierOutsideContract .publicKw)),
    ((24, 29), .constraintViolation .assignmentRequiresSemicolon),
    ((43, 44), missingExpression)
  ] "top-level diagnostic order"
  match output.parsed.items with
  | [
      { span := badSpan, value := .function bad, .. },
      { value := .typeAlias kept, .. },
      { value := .function good, .. }
    ] =>
      assertEqual (byteRange badSpan) (0, 46) "bad function item span"
      assertEqual bad.value.signature.name.value "bad" "bad function name"
      assertEqual (byteRange bad.value.body.span) (22, 46)
        "bad function body span"
      match bad.value.body.value with
      | [
          { value := .assignValue left _ right, .. },
          { value := .expression { value := .error, .. } true, .. }
        ] =>
          match left.value, right.value with
          | .identifier leftName, .identifier rightName =>
              assertEqual leftName.value "x" "statement before fallback"
              assertEqual rightName.value "y" "assignment before fallback"
          | left, right => throw (IO.userError
              s!"assignment around fallback changed: {reprStr left}; {reprStr right}")
      | body => throw (IO.userError
          s!"bad function fallback body changed: {reprStr body}")
      assertEqual kept.value.name.value "Kept" "following alias"
      assertEqual good.value.signature.name.value "good" "following function"
      assertEqual good.value.body.value.length 1 "following function body"
  | items => throw (IO.userError
      s!"top-level body isolation changed: {reprStr items}")

private def testContractEntryIsolation : IO Unit := do
  let source := String.intercalate "\n" [
    "contract C {",
    "  function bad() { let x = ; }",
    "  first: word;",
    "  constructor() { let y = ; }",
    "  second: bool;",
    "  fallback() { let z = ; }",
    "  function good() {}",
    "}",
    "type After = word;"
  ]
  let output ← checkedParse "contract entry isolation" source
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((40, 41), missingExpression),
    ((85, 86), missingExpression),
    ((128, 129), missingExpression)
  ] "contract entry diagnostics"
  match output.parsed.items with
  | [
      { value := .contract contract, .. },
      { value := .typeAlias after, .. }
    ] =>
      assertEqual contract.value.name.value "C" "contract name"
      assertEqual (byteRange contract.value.bodySpan) (11, 154)
        "contract body span"
      assertEqual after.value.name.value "After" "post-contract alias"
      match contract.value.members with
      | [
          { value := .function bad, .. },
          { value := .field first, .. },
          { value := .constructor constructor, .. },
          { value := .field second, .. },
          { value := .fallback fallback, .. },
          { value := .function good, .. }
        ] =>
          assertSingleErrorExpression bad.value.body
            "contract function fallback body"
          assertEqual (byteRange bad.value.body.span) (30, 43)
            "contract function body span"
          assertEqual first.value.name.value "first" "member after function"
          assertSingleErrorExpression constructor.value.body
            "constructor fallback body"
          assertEqual (byteRange constructor.value.body.span) (75, 88)
            "constructor body span"
          assertEqual second.value.name.value "second"
            "member after constructor"
          assertSingleErrorExpression fallback.value.body
            "fallback entry body"
          assertEqual (byteRange fallback.value.body.span) (118, 131)
            "fallback body span"
          assertEqual good.value.signature.name.value "good"
            "member after fallback"
      | members => throw (IO.userError
          s!"contract entry members changed: {reprStr members}")
  | items => throw (IO.userError
      s!"contract entry isolation changed: {reprStr items}")

private def testNestedBlockIsolation : IO Unit := do
  let source := String.intercalate "\n" [
    "function outer() { { let broken = ; } return; }",
    "function after() {}"
  ]
  let output ← checkedParse "nested block isolation" source
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((34, 35), missingExpression)
  ] "nested block diagnostic"
  match output.parsed.items with
  | [
      { value := .function outer, .. },
      { value := .function after, .. }
    ] =>
      assertEqual outer.value.signature.name.value "outer" "outer function"
      assertEqual (byteRange outer.value.body.span) (17, 47)
        "outer isolated body span"
      match outer.value.body.value with
      | [
          { value := .block [
              { value := .expression { value := .error, .. } true, .. }
            ], .. },
          { value := .returnStmt none, .. }
        ] => pure ()
      | body => throw (IO.userError
          s!"nested fallback body changed: {reprStr body}")
      assertEqual after.value.signature.name.value "after"
        "function after nested error"
  | items => throw (IO.userError
      s!"nested block isolation changed: {reprStr items}")

private def testLambdaBodyIsolation : IO Unit := do
  let source := String.intercalate "\n" [
    "function outer() { let f = lam() { let broken = ; }; return; }",
    "type After = word;"
  ]
  let output ← checkedParse "lambda body isolation" source
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((48, 49), missingExpression)
  ] "lambda body diagnostic"
  match output.parsed.items with
  | [
      { value := .function outer, .. },
      { value := .typeAlias after, .. }
    ] =>
      assertEqual (byteRange outer.value.body.span) (17, 62)
        "lambda owner body span"
      assertEqual after.value.name.value "After" "item after lambda owner"
      match outer.value.body.value with
      | [
          { value := .letDecl _ none (some initializer), .. },
          { value := .returnStmt none, .. }
        ] => match initializer.value with
          | .lambda _ _ none body =>
              assertEqual (byteRange initializer.span) (27, 51)
                "isolated lambda span"
              assertEqual (byteRange body.span) (33, 51)
                "isolated lambda body span"
              assertSingleErrorExpression body "lambda fallback body"
          | value => throw (IO.userError
              s!"lambda initializer changed: {reprStr value}")
      | statements => throw (IO.userError
          s!"lambda owner body changed: {reprStr statements}")
  | items => throw (IO.userError
      s!"lambda body isolation changed: {reprStr items}")

private def testUnclosedBodyIsNotRecovered : IO Unit := do
  let source := String.intercalate "\n" [
    "function open() { return;",
    "type Ambiguous = word;"
  ]
  let output ← checkedParse "unclosed body" source
  assertEqual output.parsed.items.length 0 "unclosed body item count"
  match output.parseDiagnostics.getLast? with
  | some {
      span,
      kind := .unexpected none
        { head := .symbol .rightBrace, tail := [] } .statement
    } =>
      assertEqual (byteRange span)
        (source.utf8ByteSize, source.utf8ByteSize)
        "unclosed body terminal span"
  | diagnostic => throw (IO.userError
      s!"unclosed body diagnostic changed: {reprStr diagnostic}")

/-- Run balanced-body fallback, isolation, and unclosed-body regressions. -/
def testSyntaxParserBodyIsolation : IO Unit := do
  testTopLevelIsolationAndDiagnosticOrder
  testContractEntryIsolation
  testNestedBlockIsolation
  testLambdaBodyIsolation
  testUnclosedBodyIsNotRecovered

end Tests
