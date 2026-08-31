import Solcore.Syntax.Parser

/-!
Compatibility regressions for the four pinned upstream malformed fixtures for
which Solcore Lean deliberately retains an additional recovery diagnostic.
-/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def policySource (name : String) : SourceId := {
  origin := .main
  path := s!"upstream/parse/{name}/main.sol"
}

private def assemblyUnclosedCall : String := String.intercalate "\n" [
  "function f() returns (word) {",
  "    let r : word;",
  "    assembly {",
  "        r := add(1,",
  "    }",
  "    return r;",
  "}",
  ""
]

private def twoErrorsRecovery : String := String.intercalate "\n" [
  "function f() returns (word) {",
  "    let x = ;",
  "    return 0;",
  "}",
  "",
  "function g(y: word) returns (word) {",
  "    if ( y ) { return 1; }",
  "    return 0;",
  "}",
  "",
  "function h() returns (word) {",
  "    return (1;",
  "}",
  ""
]

private def parameterRecovery : String := String.intercalate "\n" [
  "function bad(x:, y: U) {}",
  "function ok() {}",
  ""
]

private def signatureMissingType : String := String.intercalate "\n" [
  "function bad(x: ) {}",
  ""
]

private def assertEqual {α : Type} [BEq α] [Repr α]
    (actual expected : α) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def diagnosticShape (diagnostic : ParseDiagnostic) :
    ByteRange × ParseDiagnosticKind :=
  ((diagnostic.span.startByte, diagnostic.span.endByte), diagnostic.kind)

private def checkedParse (name source : String) : IO ParseOutput := do
  let file : SourceFile := { id := policySource name, content := source }
  match Parser.parse file with
  | .error error => throw (IO.userError
      s!"{name}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual output.lexicalDiagnostics [] s!"{name} lexical diagnostics"
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{name}: invalid parse diagnostic span")
      pure output

private def unexpected (found : TokenKind)
    (head : ParseExpectation) (tail : List ParseExpectation)
    (context : ParseContext) : ParseDiagnosticKind :=
  .unexpected (some found) { head, tail } context

private def functionName? (item : TopItem) : Option String :=
  match item.value with
  | .function declaration => some declaration.value.signature.name.value
  | _ => none

private def testAssemblyUnclosedCall : IO Unit := do
  let output ← checkedParse "ergo_assembly_unclosed_call" assemblyUnclosedCall
  assertEqual (output.parseDiagnostics.map diagnosticShape) [
    ((79, 80), unexpected (.symbol .leftParen)
      .yulIdentifier [.yulLiteral] .yulExpression),
    ((79, 81), .recovered .yulExpression),
    ((81, 82), unexpected (.symbol .comma)
      .yulIdentifier [.yulLiteral] .yulExpression),
    ((81, 82), .recovered .yulStatement)
  ] "assembly diagnostic policy"
  match output.parsed.items with
  | [{ value := .function declaration, .. }] =>
      assertEqual declaration.value.signature.name.value "f"
        "assembly function name"
      match declaration.value.body.value with
      | [
          { value := .letDecl .., .. },
          { value := .assembly [
              { value := .assign .., .. },
              { value := .expression { value := .error, .. }, .. },
              { value := .error, .. }
            ], .. },
          { value := .returnStmt .., .. }
        ] => pure ()
      | body => throw (IO.userError
          s!"assembly recovery AST changed: {reprStr body}")
  | items => throw (IO.userError
      s!"assembly items changed: {reprStr items}")

private def testTwoErrorsRecovery : IO Unit := do
  let output ← checkedParse "ergo_two_errors_recovery" twoErrorsRecovery
  assertEqual (output.parseDiagnostics.map diagnosticShape) [
    ((42, 43), unexpected (.symbol .semicolon)
      .expression [] .expression),
    ((185, 186), unexpected (.symbol .semicolon)
      (.symbol .rightParen) [] .expression),
    ((183, 185), .recovered .expressionAtom)
  ] "two-error diagnostic policy"
  assertEqual (output.parsed.items.map functionName?)
    [some "f", some "g", some "h"] "two-error declaration retention"
  match output.parsed.items with
  | [
      { value := .function first, .. },
      { value := .function middle, .. },
      { value := .function last, .. }
    ] =>
      match first.value.body.value, middle.value.body.value,
          last.value.body.value with
      | [
          { value := .expression { value := .error, .. } true, .. },
          { value := .returnStmt .., .. }
        ], [
          { value := .ifThen .., .. },
          { value := .returnStmt .., .. }
        ], [
          { value := .returnStmt (some { value := .error, .. }), .. }
        ] => pure ()
      | firstBody, middleBody, lastBody => throw (IO.userError
          s!"two-error recovery AST changed: {reprStr firstBody}; \
            {reprStr middleBody}; {reprStr lastBody}")
  | items => throw (IO.userError
      s!"two-error items changed: {reprStr items}")

private def testParameterRecovery : IO Unit := do
  let output ← checkedParse "function_param_recovery" parameterRecovery
  assertEqual (output.parseDiagnostics.map diagnosticShape) [
    ((15, 16), unexpected (.symbol .comma) .typeExpr [] .typeExpr),
    ((13, 15), .recovered .functionParameter)
  ] "parameter diagnostic policy"
  assertEqual (output.parsed.items.map functionName?)
    [some "bad", some "ok"] "parameter declaration retention"
  match output.parsed.items with
  | [
      { value := .function bad, .. },
      { value := .function good, .. }
    ] =>
      match bad.value.signature.parameters.elements,
          good.value.signature.parameters.elements with
      | [
          { value := .error, .. },
          { value := .typed none { value := "y", .. } _, .. }
        ], [] => pure ()
      | badParameters, goodParameters => throw (IO.userError
          s!"parameter recovery AST changed: {reprStr badParameters}; \
            {reprStr goodParameters}")
  | items => throw (IO.userError
      s!"parameter recovery items changed: {reprStr items}")

private def testSignatureMissingType : IO Unit := do
  let output ← checkedParse "function_signature_missing_type"
    signatureMissingType
  assertEqual (output.parseDiagnostics.map diagnosticShape) [
    ((16, 17), unexpected (.symbol .rightParen) .typeExpr [] .typeExpr),
    ((13, 15), .recovered .functionParameter)
  ] "missing-type diagnostic policy"
  match output.parsed.items with
  | [{ value := .function declaration, .. }] =>
      assertEqual declaration.value.signature.name.value "bad"
        "missing-type function name"
      match declaration.value.signature.parameters.elements with
      | [{ value := .error, .. }] => pure ()
      | parameters => throw (IO.userError
          s!"missing-type recovery AST changed: {reprStr parameters}")
  | items => throw (IO.userError
      s!"missing-type items changed: {reprStr items}")

/-- Run pinned malformed-upstream diagnostic and recovery-policy regressions. -/
def testSyntaxParserUpstreamDiagnosticPolicy : IO Unit := do
  testAssemblyUnclosedCall
  testTwoErrorsRecovery
  testParameterRecovery
  testSignatureMissingType

end Tests
