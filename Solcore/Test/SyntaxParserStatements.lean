import Solcore.Syntax.Parser
import Solcore.Syntax.Parser.Term

/-! Executable Core statement, block, and top-level function regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def statementSource : SourceId := {
  origin := .main
  path := "parser-statements.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private structure DirectRun (alpha : Type) where
  value : alpha
  state : Parser.State

private def runDirect {alpha : Type} (label content : String)
    (parser : Solcore.Syntax.Parser.Parser alpha) : IO (DirectRun alpha) := do
  let file : SourceFile := { id := statementSource, content }
  let lexed ← match Lexer.lex file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"{label}: lexer invariant failed: {reprStr error}")
  assertEqual lexed.diagnostics [] s!"{label} lexical diagnostics"
  match parser (Parser.State.initial file lexed) with
  | .ok value state =>
      unless state.atEnd do
        throw (IO.userError s!"{label}: left {state.remainingCount} token(s)")
      pure { value, state }
  | .reject failure _ => throw (IO.userError
      s!"{label}: rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: invariant failed: {reprStr error}")

private def runStatement (label content : String) : IO (DirectRun Statement) :=
  runDirect label content Parser.statement

private def runBlock (label content : String)
    (policy : Parser.TailExpressionPolicy := .allow) : IO (DirectRun Block) :=
  runDirect label content (Parser.block policy)

private def expressionName? (expression : Expr) : Option String :=
  match expression.value with
  | .identifier name => some name.value
  | _ => none

private inductive StatementAssignment where
  | value (operator : ValueAssignOp)
  | bitNot
  deriving Repr, BEq

private def assignment? (statement : Statement) : Option StatementAssignment :=
  match statement.value with
  | .assignValue _ operator _ => some (.value operator.value)
  | .assignBitNot .. => some .bitNot
  | _ => none

private def testLetAndReturn : IO Unit := do
  let run ← runBlock "let and return"
    "{ let value: word = 42; return value; return; }"
  assertEqual run.state.diagnostics [] "let/return diagnostics"
  match run.value.value with
  | [
      { value := .letDecl name (some type) (some initializer), .. },
      { value := .returnStmt (some returned), .. },
      { value := .returnStmt none, .. }
    ] =>
      assertEqual name.value "value" "let name"
      assertEqual (byteRange type.span) (13, 17) "let type span"
      match initializer.value with
      | .literal { value := .decimal "42", .. } => pure ()
      | value => throw (IO.userError s!"let initializer changed: {reprStr value}")
      assertEqual (expressionName? returned) (some "value") "return value"
  | statements => throw (IO.userError
      s!"let/return statement shapes changed: {reprStr statements}")

private def testAssignments : IO Unit := do
  for (source, expected) in [
      ("x = y;", .value .equal), ("x += y;", .value .add),
      ("x -= y;", .value .subtract), ("x *= y;", .value .multiply),
      ("x /= y;", .value .divide), ("x %= y;", .value .modulo),
      ("x &= y;", .value .bitAnd), ("x ^= y;", .value .bitXor),
      ("x |= y;", .value .bitOr), ("x ~=;", .bitNot)
    ] do
    let run ← runStatement s!"assignment {source}" source
    assertEqual (assignment? run.value) (some expected)
      s!"assignment shape {source}"
    assertEqual run.state.diagnostics [] s!"assignment diagnostics {source}"

  for source in ["x = y", "x ~="] do
    let run ← runStatement s!"unterminated assignment {source}" source
    assertEqual (run.state.diagnostics.map (fun item => item.kind)) [
      .constraintViolation .assignmentRequiresSemicolon
    ] s!"missing assignment semicolon {source}"
    assertEqual (run.state.diagnostics.map (fun item => byteRange item.span))
      [(0, source.utf8ByteSize)] s!"missing assignment span {source}"

private def expressionSemicolons (block : Block) : List Bool :=
  block.value.filterMap fun statement => match statement.value with
    | .expression _ terminated => some terminated
    | _ => none

private def testTailPolicies : IO Unit := do
  let allowed ← runBlock "root tail" "{first; last}"
  assertEqual (expressionSemicolons allowed.value) [true, false]
    "root tail source shape"
  assertEqual allowed.state.diagnostics [] "root tail allowance"

  let earlier ← runBlock "earlier tail" "{first second}"
  assertEqual (earlier.state.diagnostics.map fun item =>
      (byteRange item.span, item.kind)) [
    ((1, 6), .constraintViolation .expressionRequiresSemicolon)
  ] "earlier expression diagnostic"

  let nested ← runBlock "nested tail" "{{nested} root}"
  assertEqual (nested.state.diagnostics.map fun item =>
      (byteRange item.span, item.kind)) [
    ((2, 8), .constraintViolation .expressionRequiresSemicolon)
  ] "nested expression diagnostic"

private def testForHeader : IO Unit := do
  let source :=
    "for (let i: word = 0, seed; i < n; i += 1, flag ~=) { continue; }"
  let run ← runStatement "for header" source
  assertEqual run.state.diagnostics [] "for-header diagnostics"
  match run.value.value with
  | .forLoop header initializer condition post body =>
      assertEqual initializer.length 2 "for initializer count"
      assertEqual post.length 2 "for post count"
      assertEqual (byteRange run.value.span) (0, source.utf8ByteSize) "for span"
      match initializer, post, body.value with
      | [{ value := .letDecl name .., .. },
          { value := .expression seed, .. }],
        [{ value := .assignValue _ op _, .. },
          { value := .assignBitNot .., .. }],
        [{ value := .continueStmt, .. }] =>
          assertEqual name.value "i" "for let item"
          assertEqual (expressionName? seed) (some "seed") "for expression item"
          assertEqual op.value .add "for post assignment"
          assertEqual (header.contains condition.span) true "for condition in header"
      | _, _, _ => throw (IO.userError "for header item shapes changed")
  | value => throw (IO.userError s!"for statement changed: {reprStr value}")

private def testControlStatements : IO Unit := do
  let run ← runBlock "control statements" (String.intercalate " " [
    "{", "while (ready) { break; }",
    "if (ready) { return; } else { continue; }", "{ let x; }", "}"
  ])
  assertEqual run.state.diagnostics [] "control diagnostics"
  match run.value.value with
  | [
      { value := .whileLoop condition whileBody, .. },
      { value := .ifThen _ thenBody (some elseBody), .. },
      { value := .block nestedBody, .. }
    ] =>
      assertEqual (expressionName? condition) (some "ready") "while condition"
      assertEqual whileBody.value.length 1 "while body"
      assertEqual thenBody.value.length 1 "if body"
      assertEqual elseBody.value.length 1 "else body"
      assertEqual nestedBody.length 1 "nested block"
  | statements => throw (IO.userError
      s!"control statement shapes changed: {reprStr statements}")

private def testMatchStatements : IO Unit := do
  let valid ← runStatement "valid match"
    "match (x, y,) { case (a, b) { return; } default { return; } }"
  assertEqual valid.state.diagnostics [] "valid match diagnostics"
  match valid.value.value with
  | .matchWith scrutinees arms =>
      assertEqual scrutinees.elements.toList.length 2 "match scrutinees"
      assertEqual arms.value.cases.length 1 "match cases"
      assertEqual arms.value.defaultBody.isSome true "match default"
  | value => throw (IO.userError s!"valid match changed: {reprStr value}")

  let empty ← runStatement "empty match" "match (x) {}"
  assertEqual (empty.state.diagnostics.map (fun item => item.kind)) [
    .constraintViolation .matchRequiresArm
  ] "match arm requirement"

  let mismatch ← runStatement "match arity"
    "match (x, y) { case value { return; } }"
  match mismatch.value.value, mismatch.state.diagnostics with
  | .matchWith _ { value := { cases := [case], .. }, .. },
      [{ span, kind := .constraintViolation (.matchArityMismatch 2 1) }] =>
      assertEqual span case.span "match arity diagnostic span"
  | value, diagnostics => throw (IO.userError
      s!"match arity changed: {reprStr value}; {reprStr diagnostics}")

private def testAssemblyAndLambda : IO Unit := do
  let assembly ← runStatement "assembly integration"
    "assembly { let x := 1 x := add(x, 1) if x { leave } }"
  assertEqual assembly.state.diagnostics [] "assembly diagnostics"
  match assembly.value.value with
  | .assembly [
      { value := .letDecl .., .. },
      { value := .assign .., .. },
      { value := .ifThen _ [{ value := .leave, .. }], .. }
    ] => pure ()
  | value => throw (IO.userError s!"assembly integration changed: {reprStr value}")

  let lambda ← runStatement "lambda body"
    "let f = lam(x, comptime y: word) -> word { return y; };"
  assertEqual lambda.state.diagnostics [] "lambda diagnostics"
  match lambda.value.value with
  | .letDecl _ none (some initializer) =>
      match initializer.value with
      | .lambda _ parameters (some returnType) body =>
          assertEqual parameters.elements.length 2 "lambda parameter count"
          assertEqual (byteRange returnType.span) (36, 40) "lambda return span"
          assertEqual body.value.length 1 "lambda body statement count"
      | value => throw (IO.userError s!"lambda expression changed: {reprStr value}")
  | value => throw (IO.userError s!"lambda integration changed: {reprStr value}")

private def testTopLevelFunction : IO Unit := do
  let content := String.intercalate "\n" [
    "// function", "function id(x: word) returns (word) {", "  x", "}",
    "// alias", "type Result = word;"
  ]
  let file : SourceFile := { id := statementSource, content }
  let output ← match Parser.parse file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"top-level function invariant: {reprStr error}")
  assertEqual output.parseDiagnostics [] "top-level function diagnostics"
  assertEqual output.lexicalDiagnostics [] "top-level function lexing"
  assertEqual output.parsed.comments.length 2 "top-level comments"
  match output.parsed.items with
  | [functionItem, aliasItem] =>
      assertEqual (functionItem.leadingComments.map (fun item => item.text))
        [" function"] "function leading comment"
      assertEqual (aliasItem.leadingComments.map (fun item => item.text))
        [" alias"] "following-item leading comment"
      assertEqual (byteRange functionItem.span) (12, 55) "function item span"
      assertEqual (byteRange aliasItem.span) (65, 84) "following item span"
      match functionItem.value with
      | .function declaration =>
          assertEqual declaration.value.signature.name.value "id" "function name"
          assertEqual (byteRange declaration.value.signature.span) (12, 47)
            "function signature span"
          assertEqual (byteRange declaration.value.body.span) (48, 55)
            "function body span"
          match declaration.value.body.value with
          | [{ value := .expression expression false, .. }] =>
              assertEqual (expressionName? expression) (some "x")
                "root tail expression"
          | body => throw (IO.userError s!"function body changed: {reprStr body}")
      | value => throw (IO.userError s!"function item changed: {reprStr value}")
  | items => throw (IO.userError s!"top-level items changed: {reprStr items}")

/-- Run Core statement and top-level function parser regressions. -/
def testSyntaxParserStatements : IO Unit := do
  testLetAndReturn
  testAssignments
  testTailPolicies
  testForHeader
  testControlStatements
  testMatchStatements
  testAssemblyAndLambda
  testTopLevelFunction

end Tests
