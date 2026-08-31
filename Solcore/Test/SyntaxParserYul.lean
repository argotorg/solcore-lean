import Solcore.Syntax.Parser.Yul.Statement

/-! Direct executable regressions for the canonical inline-Yul parser. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def yulSource : SourceId := {
  origin := .main
  path := "parser-yul.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def initialState (label content : String) : IO Parser.State := do
  let file : SourceFile := { id := yulSource, content }
  match Lexer.lex file with
  | .error error => throw (IO.userError
      s!"{label}: lexer invariant failed: {reprStr error}")
  | .ok lexed =>
      assertEqual lexed.diagnostics [] s!"{label} lexical diagnostics"
      pure (Parser.State.initial file lexed)

private structure ExpressionRun where
  value : YulExpr
  state : Parser.State

private structure StatementRun where
  value : YulStmt
  state : Parser.State

private structure BodyRun where
  value : Parser.YulParsedBlock
  state : Parser.State

private def runExpression (label content : String)
    (complete : Bool := true) : IO ExpressionRun := do
  let state ← initialState label content
  match Parser.yulExpression state with
  | .ok value next =>
      if complete && !next.atEnd then
        throw (IO.userError s!"{label}: expression left tokens")
      pure { value, state := next }
  | .reject failure _ => throw (IO.userError
      s!"{label}: expression rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: expression invariant: {reprStr error}")

private def runStatement (label content : String)
    (complete : Bool := true) : IO StatementRun := do
  let state ← initialState label content
  match Parser.yulStatement state with
  | .ok value next =>
      if complete && !next.atEnd then
        throw (IO.userError s!"{label}: statement left tokens")
      pure { value, state := next }
  | .reject failure _ => throw (IO.userError
      s!"{label}: statement rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: statement invariant: {reprStr error}")

private def runBody (label content : String) : IO BodyRun := do
  let state ← initialState label content
  match Parser.yulBody state with
  | .ok value next =>
      unless next.atEnd do throw (IO.userError s!"{label}: body left tokens")
      pure { value, state := next }
  | .reject failure _ => throw (IO.userError
      s!"{label}: body rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: body invariant: {reprStr error}")

private inductive YulExpressionShape where
  | literal (value : YulLiteralValue)
  | identifier (name : String)
  | call (name : String) (arguments : List YulExpressionShape)
  | error
  deriving Repr, BEq, Inhabited

private partial def expressionShape (expression : YulExpr) : YulExpressionShape :=
  match expression.value with
  | .literal literal => .literal literal.value
  | .identifier name => .identifier name.value
  | .call name arguments =>
      .call name.value (arguments.elements.map expressionShape)
  | .error => .error

private inductive YulStatementShape where
  | block (body : List YulStatementShape)
  | letDecl (names : List String) (initializer : Option YulExpressionShape)
  | assign (names : List String) (value : YulExpressionShape)
  | expression (value : YulExpressionShape)
  | ifThen (condition : YulExpressionShape) (body : List YulStatementShape)
  | forLoop (initializer : List YulStatementShape) (condition : YulExpressionShape)
      (post body : List YulStatementShape)
  | switch (scrutinee : YulExpressionShape)
      (cases : List (YulLiteralValue × List YulStatementShape))
      (defaultBody : Option (List YulStatementShape))
  | functionDef (name : String) (parameters : List String)
      (returns : Option (List String)) (body : List YulStatementShape)
  | leave | break | continue | error
  deriving Repr, BEq, Inhabited

private def names (values : NonemptyList YulIdentifier) : List String :=
  values.toList.map (fun value => value.value)

private partial def statementShape (statement : YulStmt) : YulStatementShape :=
  match statement.value with
  | .block body => .block (body.map statementShape)
  | .letDecl bound initializer =>
      .letDecl (names bound) (initializer.map expressionShape)
  | .assign assigned value => .assign (names assigned) (expressionShape value)
  | .expression value => .expression (expressionShape value)
  | .ifThen condition body =>
      .ifThen (expressionShape condition) (body.map statementShape)
  | .forLoop initializer condition post body =>
      .forLoop (initializer.map statementShape) (expressionShape condition)
        (post.map statementShape) (body.map statementShape)
  | .switch scrutinee cases defaultBody =>
      .switch (expressionShape scrutinee) (cases.toList.map fun item =>
        match item.value with
        | .arm literal body => (literal.value, body.map statementShape))
        (defaultBody.map fun body => body.map statementShape)
  | .functionDef name parameters returns body =>
      .functionDef name.value (parameters.elements.map (fun item => item.value))
        (returns.map fun clause => names clause.value.names)
        (body.map statementShape)
  | .leave => .leave
  | .break => .break
  | .continue => .continue
  | .error => .error

private def id (name : String) : YulExpressionShape := .identifier name
private def call (name : String) (args : List YulExpressionShape) : YulExpressionShape :=
  .call name args

private def testExpressions : IO Unit := do
  let cases : List (String × YulExpressionShape) := [
    ("42", .literal (.decimal "42")),
    ("0xF", .literal (.hexadecimal "0xF")),
    ("\"text\"", .literal (.string "\"text\"")),
    ("true", .literal (.boolean true)),
    ("false", .literal (.boolean false)),
    ("ordinary", id "ordinary"), ("_", id "_"),
    ("$slot", id "$slot"), ("value$tail", id "value$tail"),
    ("fallback", id "fallback"),
    ("outer(inner(1,), false,)",
      call "outer" [call "inner" [.literal (.decimal "1")],
        .literal (.boolean false)])
  ]
  for (source, expected) in cases do
    let run ← runExpression s!"Yul expression {source}" source
    assertEqual (expressionShape run.value) expected s!"Yul expression shape {source}"
    assertEqual (byteRange run.value.span) (0, source.utf8ByteSize)
      s!"Yul expression span {source}"
    assertEqual run.state.diagnostics [] s!"Yul expression diagnostics {source}"
  let nested ← runExpression "Yul call delimiters" "outer(inner(1,), false,)"
  match nested.value.value with
  | .call callee arguments =>
      assertEqual (byteRange callee.span) (0, 5) "Yul call callee span"
      assertEqual (byteRange arguments.span) (5, 24) "Yul call arguments span"
  | _ => throw (IO.userError "Yul call shape changed")

private def testMetaAndRecovery : IO Unit := do
  for source in ["`value`", "${value}", "``", "${}"] do
    let run ← runExpression s!"Yul meta {source}" source
    assertEqual (expressionShape run.value) .error s!"Yul meta node {source}"
    assertEqual (byteRange run.value.span) (0, source.utf8ByteSize)
      s!"Yul meta span {source}"
    assertEqual (run.state.diagnostics.map fun item => item.kind)
      [.constraintViolation .yulMetaInSource] s!"Yul meta diagnostic {source}"

  let expression ← runExpression "Yul expression recovery" "+ -," false
  assertEqual (expressionShape expression.value) .error "Yul recovered expression"
  assertEqual (byteRange expression.value.span) (0, 3) "Yul recovery span"
  assertEqual expression.state.peekKind? (some (.symbol .comma))
    "Yul expression recovery boundary"
  assertEqual (expression.state.diagnostics.map fun item => item.kind) [
    .unexpected (some (.symbol .plus))
      { head := .yulIdentifier, tail := [.yulLiteral] } .yulExpression,
    .recovered .yulExpression
  ] "Yul expression recovery diagnostics"

  let statement ← runStatement "Yul statement recovery" "let , }" false
  assertEqual (statementShape statement.value) (.expression .error)
    "Yul recognized-statement fallback"
  assertEqual (byteRange statement.value.span) (0, 3)
    "Yul recognized-statement fallback span"
  assertEqual statement.state.peekKind? (some (.symbol .comma))
    "Yul statement recovery boundary"
  assertEqual (statement.state.diagnostics.map fun item => item.kind) [
    .unexpected (some (.symbol .comma))
      { head := .yulIdentifier, tail := [] } .yulExpression
  ] "Yul recognized-statement primary diagnostic"

private def testAllStatements : IO Unit := do
  let source := "{ {} let a, b := pair(1, 2,) a, b := pair() ping(a) " ++
    "return(0, 0,) if cond { leave } " ++
    "for { let i := 0 } lt(i, 2) { i := add(i, 1) } { continue break } " ++
    "switch flag case 0 { leave } case true {} default { break } " ++
    "function pair(x,) -> a, b { a := x b := 2 } leave break continue }"
  let run ← runBody "all Yul statements" source
  assertEqual (byteRange run.value.span) (0, source.utf8ByteSize) "Yul body span"
  assertEqual run.state.diagnostics [] "all Yul statement diagnostics"
  assertEqual (run.value.body.map statementShape) [
    .block [],
    .letDecl ["a", "b"] (some (call "pair"
      [.literal (.decimal "1"), .literal (.decimal "2")])),
    .assign ["a", "b"] (call "pair" []),
    .expression (call "ping" [id "a"]),
    .expression (call "return" [.literal (.decimal "0"), .literal (.decimal "0")]),
    .ifThen (id "cond") [.leave],
    .forLoop [.letDecl ["i"] (some (.literal (.decimal "0")))]
      (call "lt" [id "i", .literal (.decimal "2")])
      [.assign ["i"] (call "add" [id "i", .literal (.decimal "1")])]
      [.continue, .break],
    .switch (id "flag") [
      (.decimal "0", [.leave]), (.boolean true, [])] (some [.break]),
    .functionDef "pair" ["x"] (some ["a", "b"])
      [.assign ["a"] (id "x"), .assign ["b"] (.literal (.decimal "2"))],
    .leave, .break, .continue
  ] "all Yul statement shapes"

private def testPoliciesAndSpans : IO Unit := do
  for (source, found, boundary) in [
      ("let a, := x", TokenKind.symbol .colonEqual, Symbol.comma),
      ("function f() -> r, {}", TokenKind.symbol .leftBrace, Symbol.rightParen)
    ] do
    let run ← runStatement s!"rejected Yul trailing comma {source}" source false
    assertEqual (statementShape run.value) (.expression .error)
      s!"Yul trailing comma fallback {source}"
    assertEqual run.state.peekKind? (some (.symbol boundary))
      s!"Yul trailing comma boundary {source}"
    assertEqual (run.state.diagnostics.map fun item => item.kind) [
      .unexpected (some found)
        { head := .yulIdentifier, tail := [] } .yulExpression
    ] s!"Yul trailing comma primary diagnostic {source}"

  let assignment ← runStatement "rejected Yul assignment trailing comma"
    "a, := x" false
  assertEqual (statementShape assignment.value) (.expression (id "a"))
    "Yul assignment trailing comma prefix"
  assertEqual assignment.state.peekKind? (some (.symbol .comma))
    "Yul assignment trailing comma remains unconsumed"

  for (source, expected) in [
      ("leave;", YulStatementShape.leave),
      ("{};", .block []),
      ("function f() {};", .functionDef "f" [] none [])
    ] do
    let run ← runStatement s!"optional Yul semicolon {source}" source
    assertEqual (statementShape run.value) expected s!"Yul semicolon shape {source}"
    assertEqual (byteRange run.value.span) (0, source.utf8ByteSize - 1)
      s!"Yul semicolon excluded from span {source}"
    assertEqual run.state.diagnostics [] s!"Yul semicolon diagnostics {source}"

  let functionSource :=
    "function $copy(_src, value$len,) -> $result, _end { $result := _src }"
  let functionRun ← runStatement "Yul function returns" functionSource
  assertEqual (statementShape functionRun.value)
    (.functionDef "$copy" ["_src", "value$len"] (some ["$result", "_end"])
      [.assign ["$result"] (id "_src")]) "Yul function shape"
  match functionRun.value.value with
  | .functionDef _ parameters (some returns) _ =>
      assertEqual (byteRange parameters.span) (14, 32) "Yul parameter span"
      assertEqual (byteRange returns.value.arrow) (33, 35) "Yul return arrow span"
      assertEqual (byteRange returns.span) (33, 49) "Yul return clause span"
  | _ => throw (IO.userError "Yul return clause changed")

  for source in ["switch x", "switch x default {}"] do
    let run ← runStatement s!"Yul switch case requirement {source}" source
    assertEqual (statementShape run.value) .error s!"Yul switch error node {source}"
    assertEqual (run.state.diagnostics.map fun item => item.kind)
      [.constraintViolation .yulSwitchRequiresCase]
      s!"Yul switch case diagnostic {source}"

/-- Run direct inline-Yul expression, statement, and recovery regressions. -/
def testSyntaxParserYul : IO Unit := do
  testExpressions
  testMetaAndRecovery
  testAllStatements
  testPoliciesAndSpans

end Tests
