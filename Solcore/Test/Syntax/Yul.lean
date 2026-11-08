import Solcore.Syntax.Parser.Internal.YulStatementSoundness
import Solcore.Syntax.Parser.Internal.YulTotality
import Solcore.Syntax.Parser
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Parser.Internal.YulAssignmentSoundness
import Solcore.Syntax.Parser.Internal.Completeness
import Solcore.Syntax.Parser.Internal.YulPublicSoundness
import Solcore.Syntax
import Solcore.Syntax.Yul

/-!
# Yul syntax tests

Inline Yul: expressions, statements, control forms and function signatures, with choice recovery,
fuel totality, exactness and public completeness.
-/

section
-- leanmerge: from Solcore.Test.SyntaxParserYul
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
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulBlockFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulBlockFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulBlockItems_ordinary_of_statementFuel
example := @yulBlockItems_ne_invariant_of_statementFuel
example := @yulBlock_ordinary_of_statementFuel
example := @yulBlock_ne_invariant_of_statementFuel
example := @yulBlock_fuelElementTotalityContract

example (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulBlock statement) (statementFuel + 1) :=
  yulBlock_fuelElementTotalityContract statement statementFuel contract

end Solcore.Test.SyntaxParserYulBlockFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulBodyTotalityProperties
/-! Compile-time consumers for public inline-Yul body totality. -/

namespace Solcore.Test.SyntaxParserYulBodyTotalityProperties

open Solcore.Syntax.Parser

example := @yulStatement_elementTotalityContract
example := @yulBody_ordinary
example := @yulBody_invariantFreeOnValid
example := @yulBody_ne_invariant
example := @yulBody_cursor_lt_onSuccess
example := @yulBody_elementTotalityContract

end Solcore.Test.SyntaxParserYulBodyTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulChoiceRecovery
/-! Regressions for transactional ordered choice in inline-Yul statements. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def choiceSource : SourceId := {
  origin := .main
  path := "parser-yul-choice-recovery.sol"
}

private structure BodyRun_variant where
  value : Parser.YulParsedBlock
  state : Parser.State
  tokens : List Token

private def runBody_variant (label content : String) : IO BodyRun_variant := do
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
    let run ← runBody_variant s!"recognized Yul {test.label}" test.source
    assertExpressionError test.label run.value.body
    let closing := (rightBraceRanges run.tokens).getD 0 (0, 0)
    assertEqual (run.state.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
        (closing, test.failureKind)
      ] s!"{test.label} sole farthest primary diagnostic"

private def testIndependentFailuresKeepFollowingStatement : IO Unit := do
  let source := "{ { let } { if } { for } leave }"
  let run ← runBody_variant "independent recognized failures" source
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
  let run ← runBody_variant "generic Yul junk" source
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
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulCommonProperties
/-! External consumers for common inline-Yul parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @YulNameSequence.ValidFor
example := @yulNames_validFor
example := @yulNames_ok_state_shape
example := @yulNames_preservesTokensOnSuccess
example := @yulNames_preservesTokenWindow
example := @yulNames_cursorMonotoneOnSuccess
example := @yulNames_startsAtCurrentTokenOnSuccess
example := @YulParsedBlock.ValidFor
example := @yulBlock_validFor
example := @yulBlock_ok_state_shape
example := @yulBlock_preservesTokensOnSuccess
example := @yulBlock_cursor_lt_onSuccess
example := @yulBlock_cursorMonotoneOnSuccess
example := @yulBlock_startsAtCurrentTokenOnSuccess
example := @yulParameters_validFor
example := @yulParameters_preservesTokensOnSuccess
example := @yulParameters_cursor_lt_onSuccess
example := @yulParameters_cursorMonotoneOnSuccess
example := @yulParameters_startsAtCurrentTokenOnSuccess

example (file : SourceFile) (values : YulNameSequence)
    (valid : YulNameSequence.ValidFor file values)
    (name : YulIdentifier) (member : name ∈ values.names.toList) :
    values.span.ValidFor file ∧ name.span.ValidFor file :=
  ⟨valid.1, valid.2 name member⟩

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulControlForFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulControlForFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulForStatement_ordinary_of_statementFuel
example := @yulForStatement_ne_invariant_of_statementFuel
example := @yulForStatement_cursor_lt_onSuccess
example := @yulForStatement_fuelElementTotalityContract
example := @yulForStatement_fuelTotalityContract

example (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulForStatement statement)
      (statementFuel + 2) :=
  yulForStatement_fuelElementTotalityContract statement statementFuel
    contract

end Solcore.Test.SyntaxParserYulControlForFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulControlFunctionFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulControlFunctionFuelTotalityProperties

open Solcore.Syntax.Parser

example := @FuelYulStatementTotalityContract.fuelElementTotalityContract
example := @yulBlockStatement_ordinary_of_statementFuel
example := @yulBlockStatement_ne_invariant_of_statementFuel
example := @yulBlockStatement_cursor_lt_onSuccess
example := @yulBlockStatement_fuelTotalityContract
example := @yulFunctionStatement_ordinary_of_statementFuel
example := @yulFunctionStatement_ne_invariant_of_statementFuel
example := @yulFunctionStatement_cursor_lt_onSuccess
example := @yulFunctionStatement_fuelTotalityContract

end Solcore.Test.SyntaxParserYulControlFunctionFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulControlIfFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulControlIfFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulIfStatement_ordinary_of_statementFuel
example := @yulIfStatement_ne_invariant_of_statementFuel
example := @yulIfStatement_cursor_lt_onSuccess
example := @yulIfStatement_fuelElementTotalityContract
example := @yulIfStatement_fuelTotalityContract

example (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulIfStatement statement)
      (statementFuel + 3) :=
  yulIfStatement_fuelElementTotalityContract statement statementFuel contract

end Solcore.Test.SyntaxParserYulControlIfFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulControlProperties
/-! External compile consumers for inline-Yul `if` parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulIfStatement_validFor
example := @yulIfStatement_preservesTokensOnSuccess
example := @yulIfStatement_cursorMonotoneOnSuccess
example := @yulIfStatement_startsAtCurrentTokenOnSuccess
example := @yulForStatement_validFor
example := @yulForStatement_preservesTokensOnSuccess
example := @yulForStatement_cursorMonotoneOnSuccess
example := @yulForStatement_startsAtCurrentTokenOnSuccess
example := @yulFunctionStatement_validFor
example := @yulFunctionStatement_preservesTokensOnSuccess
example := @yulFunctionStatement_cursorMonotoneOnSuccess
example := @yulFunctionStatement_startsAtCurrentTokenOnSuccess
example := @yulCase_validFor
example := @yulCase_preservesTokensOnSuccess
example := @yulCase_cursorMonotoneOnSuccess
example := @yulCases_preservesTokensOnSuccess
example := @yulCases_cursorMonotoneOnSuccess
example := @yulCases_validFor
example := @yulCase_startsAtCurrentTokenOnSuccess
example := @yulCase_cursor_lt_onSuccess
example := @optionalYulDefault_validFor
example := @optionalYulDefault_preservesTokensOnSuccess
example := @optionalYulDefault_cursorMonotoneOnSuccess
example := @yulSwitchStatement_validFor
example := @yulSwitchStatement_preservesTokensOnSuccess
example := @yulSwitchStatement_cursorMonotoneOnSuccess
example := @yulSwitchStatement_startsAtCurrentTokenOnSuccess
example := @yulBlock_preservesTokenWindow
example := @yulParameters_preservesTokenWindow
example := @yulIfStatement_preservesTokenWindow
example := @yulForStatement_preservesTokenWindow
example := @yulReturns_preservesTokenWindow
example := @yulFunctionStatement_preservesTokenWindow
example := @yulCase_preservesTokenWindow
example := @yulCases_preservesTokenWindow
example := @optionalYulDefault_preservesTokenWindow
example := @yulSwitchStatement_preservesTokenWindow

example (nested : Parser YulStmt)
    (expressionValid : yulExpression.ValidFor YulExpr.ValidFor)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess yulExpression (·.span))
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (yulIfStatement nested).ValidFor YulStmt.ValidFor :=
  yulIfStatement_validFor nested expressionValid expressionStarts
    expressionPreserves expressionMonotone nestedValid nestedPreserves

example (nested : Parser YulStmt)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulIfStatement nested) :=
  yulIfStatement_preservesTokensOnSuccess nested expressionPreserves
    nestedPreserves

example (nested : Parser YulStmt)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (yulIfStatement nested) :=
  yulIfStatement_cursorMonotoneOnSuccess nested expressionMonotone
    nestedPreserves

example (nested : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulIfStatement nested) (·.span) :=
  yulIfStatement_startsAtCurrentTokenOnSuccess nested

example (nested : Parser YulStmt)
    (expressionValid : yulExpression.ValidFor YulExpr.ValidFor)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (yulForStatement nested).ValidFor YulStmt.ValidFor :=
  yulForStatement_validFor nested expressionValid expressionPreserves
    expressionMonotone nestedValid nestedPreserves

example (nested : Parser YulStmt)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulForStatement nested) :=
  yulForStatement_preservesTokensOnSuccess nested expressionPreserves
    nestedPreserves

example (nested : Parser YulStmt)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (yulForStatement nested) :=
  yulForStatement_cursorMonotoneOnSuccess nested expressionMonotone
    nestedPreserves

example (nested : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulForStatement nested) (·.span) :=
  yulForStatement_startsAtCurrentTokenOnSuccess nested

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulControlSwitchDefaultFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulControlSwitchDefaultFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @optionalYulDefault_ordinary_of_statementFuel
example := @optionalYulDefault_ne_invariant_of_statementFuel
example := @optionalYulDefault_fuelTotalityContract

end Solcore.Test.SyntaxParserYulControlSwitchDefaultFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulControlSwitchFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulControlSwitchFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @YulControl.FuelParserTotalityContract.ne_invariant
example := @yulCase_ordinary_of_statementFuel
example := @yulCase_ne_invariant_of_statementFuel
example := @yulCase_fuelElementTotalityContract
example := @yulCases_ordinary_of_fuels
example := @yulCases_ne_invariant_of_fuels
example := @yulCases_fuelTotalityContract

end Solcore.Test.SyntaxParserYulControlSwitchFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulControlSwitchStatementFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulControlSwitchStatementFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulSwitchStatement_ordinary_of_statementFuel
example := @yulSwitchStatement_ne_invariant_of_statementFuel
example := @yulSwitchStatement_cursor_lt_onSuccess
example := @yulSwitchStatement_fuelElementTotalityContract
example := @yulSwitchStatement_fuelTotalityContract

end Solcore.Test.SyntaxParserYulControlSwitchStatementFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulExpressionExactnessProperties
/-! External compile consumers of exact fixed-fuel and public Yul expressions. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulExpressionExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeclarativeGrammar.yulNameExactOutcomeSpec
example := @DeclarativeGrammar.YulNameOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulNameRejects.output_unique
example := @DeclarativeGrammar.YulLiteralParses.result_unique
example := @DeclarativeGrammar.OptionalYulCallArgumentsOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulNamedExpressionOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulExpressionCoreOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulExpressionRecoveryScanParses.result_unique
example := @DeclarativeGrammar.YulExpressionLayerOrdinaryParses.result_unique
example := @DeclarativeGrammar.yulExpressionLayerExactOutcomeSpec
example := @DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel.value_unique
example := @DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel.result_unique
example := @DeclarativeGrammar.YulExpressionRejectsWithFuel.output_unique
example := @DeclarativeGrammar.YulExpressionOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulExpressionOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulExpressionPublicRejects.output_unique

example (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.YulExpressionOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.YulExpressionRejectsWithFuel fuel) :=
  YulExpressionInternals.withFuel_exactOutcomeSpec fuel

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.YulExpressionOrdinaryParses
    DeclarativeGrammar.YulExpressionPublicRejects :=
  yulExpression_publicExactOutcomeSpec

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.YulExpressionOrdinaryParses
    DeclarativeGrammar.YulExpressionRejects :=
  yulExpression_exactOutcomeSpec

example (fuel : Nat) {input leftOutput rightOutput : State}
    {left right : YulExpr}
    (leftResult : YulExpressionInternals.withFuel fuel input =
      .ok left leftOutput)
    (rightResult : YulExpressionInternals.withFuel fuel input =
      .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  YulExpressionInternals.withFuel_success_result_unique fuel leftResult rightResult

example (fuel : Nat) {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : YulExpressionInternals.withFuel fuel input =
      .reject leftFailure leftOutput)
    (rightResult : YulExpressionInternals.withFuel fuel input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  YulExpressionInternals.withFuel_reject_output_unique fuel leftResult rightResult

example {input leftOutput rightOutput : State} {left right : YulExpr}
    (leftResult : yulExpression input = .ok left leftOutput)
    (rightResult : yulExpression input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulExpression_success_result_unique leftResult rightResult

example {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulExpression input = .reject leftFailure leftOutput)
    (rightResult : yulExpression input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulExpression_reject_output_unique leftResult rightResult

end Solcore.Test.SyntaxParserYulExpressionExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulExpressionFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulExpressionFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @optionalYulCallArguments_ordinary_of_elementFuel
example := @optionalYulCallArguments_ne_invariant_of_elementFuel
example := @yulExpressionCore_ordinary_of_elementFuel
example := @yulExpressionCore_ne_invariant_of_elementFuel
example := @YulExpressionInternals.recoverAux_exists_ok_of_remainingCount_lt
example := @YulExpressionInternals.recoverAux_production_exists_ok
example := @YulExpressionInternals.recoverAux_ne_invariant_of_remainingCount_lt
example := @YulExpressionInternals.layer_ordinary_of_elementFuel
example := @YulExpressionInternals.layer_ne_invariant_of_elementFuel

example (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next,
      YulExpressionInternals.layer nested input = .ok expression next) ∨
    (∃ failure next,
      YulExpressionInternals.layer nested input = .reject failure next) :=
  YulExpressionInternals.layer_ordinary_of_elementFuel nested nestedFuel
    contract input inputValid adequate

end Solcore.Test.SyntaxParserYulExpressionFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulExpressionProperties
/-! External compile consumers for inline-Yul expression-layer contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @YulExpr.ValidFor
example := @optionalYulCallArguments_validFor
example := @rejectedMeta_validFor
example := @rejectedMeta_yulExpr_validFor

example : Parser.StartsAtCurrentTokenOnSuccess yulName (·.span) :=
  yulName_startsAtCurrentTokenOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess yulLiteral (·.span) :=
  yulLiteral_startsAtCurrentTokenOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess rejectedMeta (·.span) :=
  rejectedMeta_startsAtCurrentTokenOnSuccess

example (nested : Parser YulExpr)
    (valid : nested.ValidFor YulExpr.ValidFor)
    (preserves : Parser.PreservesTokensOnSuccess nested) :
    (yulExpressionCore nested).ValidFor YulExpr.ValidFor :=
  yulExpressionCore_validFor nested valid preserves

example (nested : Parser YulExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulExpressionCore nested) (·.span) :=
  yulExpressionCore_startsAtCurrentTokenOnSuccess nested

example (nested : Parser YulExpr)
    (preserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulExpressionCore nested) :=
  yulExpressionCore_preservesTokensOnSuccess nested preserves

example (nested : Parser YulExpr)
    (shape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (yulExpressionCore nested) :=
  yulExpressionCore_preservesTokenWindow nested shape

example (nested : Parser YulExpr)
    (shape : Parser.PreservesTokenWindow nested)
    {input failedState : State} {failure : Failure}
    (rejected : yulExpressionCore nested input =
      .reject failure failedState) :
    failedState.tokens = input.tokens ∧
      failedState.window = input.window :=
  yulExpressionCore_reject_preservesTokenWindow nested shape rejected

example (nested : Parser YulExpr) :
    Parser.CursorMonotoneOnSuccess (yulExpressionCore nested) :=
  yulExpressionCore_cursorMonotoneOnSuccess nested

example (nested : Parser YulExpr) {input next : State} {expression : YulExpr}
    (parsed : yulExpressionCore nested input = .ok expression next) :
    input.cursor < next.cursor :=
  yulExpressionCore_cursor_lt_onSuccess nested parsed

example := @YulExpressionInternals.finishRecovered_validFor
example := @YulExpressionInternals.recoverAux_validFor
example := @YulExpressionInternals.recoverAux_ok_state_shape

example (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokensOnSuccess
      (YulExpressionInternals.recoverAux first last fuel) :=
  YulExpressionInternals.recoverAux_preservesTokensOnSuccess first last fuel

example (first last : SourceSpan) (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess
      (YulExpressionInternals.recoverAux first last fuel) :=
  YulExpressionInternals.recoverAux_cursorMonotoneOnSuccess first last fuel

example (nested : Parser YulExpr)
    (valid : nested.ValidFor YulExpr.ValidFor)
    (preserves : Parser.PreservesTokensOnSuccess nested)
    (rejectShape : ∀ input failure failedState,
      yulExpressionCore nested input = .reject failure failedState →
      failedState.tokens = input.tokens ∧ failedState.window = input.window) :
    (YulExpressionInternals.layer nested).ValidFor YulExpr.ValidFor :=
  YulExpressionInternals.layer_validFor nested valid preserves rejectShape

example : yulExpression.ValidFor YulExpr.ValidFor :=
  yulExpression_validFor

example : Parser.PreservesTokenWindow yulExpression :=
  yulExpression_preservesTokenWindow

example : Parser.PreservesTokensOnSuccess yulExpression :=
  yulExpression_preservesTokensOnSuccess

example : Parser.CursorMonotoneOnSuccess yulExpression :=
  yulExpression_cursorMonotoneOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess yulExpression (·.span) :=
  yulExpression_startsAtCurrentTokenOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulExpressionRecursiveTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulExpressionRecursiveTotalityProperties

open Solcore.Syntax.Parser

example := @YulExpressionInternals.layer_cursor_lt_onSuccess
example := @YulExpressionInternals.withFuel_cursor_lt_onSuccess
example := @YulExpressionInternals.withFuel_fuelElementTotalityContract
example := @YulExpressionInternals.withFuel_ordinary_of_remainingCount_lt
example := @YulExpressionInternals.withFuel_ne_invariant_of_remainingCount_lt
example := @yulExpression_invariantFreeOnValid
example := @yulExpression_ne_invariant
example := @yulExpression_cursor_lt_onSuccess
example := @yulExpression_elementTotalityContract

example (input : State) (inputValid : input.ValidFor) :
    (∃ expression next, yulExpression input = .ok expression next) ∨
    (∃ failure next, yulExpression input = .reject failure next) :=
  yulExpression_invariantFreeOnValid input inputValid

end Solcore.Test.SyntaxParserYulExpressionRecursiveTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulLeafProperties
set_option autoImplicit false

namespace Tests
open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulName_validFor
example := @yulLiteral_validFor
example := @yulName_preservesTokensOnSuccess
example := @yulLiteral_preservesTokensOnSuccess
example := @yulName_cursorMonotoneOnSuccess
example := @yulLiteral_cursorMonotoneOnSuccess
example := @yulName_ok_state_shape
example := @yulLiteral_ok_state_shape
end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulLeafTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulLeafTotalityProperties

open Solcore.Syntax.Parser

example := @yulName_ordinary
example := @yulLiteral_ordinary
example := @rejectedMeta_ordinary
example := @yulName_elementTotalityContract
example := @yulLiteral_elementTotalityContract
example := @rejectedMeta_elementTotalityContract

end Solcore.Test.SyntaxParserYulLeafTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulNamesTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulNamesTotalityProperties

open Solcore.Syntax.Parser

example := @yulNamesTail_ordinary_of_remainingCount_lt
example := @yulNames_invariantFreeOnValid
example := @yulNames_cursor_lt_onSuccess
example := @yulNames_elementTotalityContract

end Solcore.Test.SyntaxParserYulNamesTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulPublicCompletenessProperties
/-! Independent forward and reverse consumers for public Yul completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulPublicCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulExpression_ordinary_success_iff
example := @yulExpression_ordinary_reject_iff

example {input : State} (inputValid : input.ValidFor)
    {value : YulExpr} {remainder : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulExpressionOrdinaryParses input.declarativeRemainder value remainder) :
    ∃ output, yulExpression input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (yulExpression_ordinary_success_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {value : YulExpr} {remainder : DeclarativeGrammar.Remainder}
    (result : yulExpression input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.YulExpressionOrdinaryParses input.declarativeRemainder value remainder :=
  (yulExpression_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulExpressionPublicRejects input.declarativeRemainder rejected) :
    ∃ failure output, yulExpression input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (yulExpression_ordinary_reject_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {failure : Failure} {rejected : DeclarativeGrammar.Remainder}
    (result : yulExpression input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.YulExpressionPublicRejects input.declarativeRemainder rejected :=
  (yulExpression_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example := @yulStatement_ordinary_success_iff
example := @yulStatement_ordinary_reject_iff

example {input : State} (inputValid : input.ValidFor)
    {value : YulStmt} {remainder : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulStatementOrdinaryParses input.declarativeRemainder value remainder) :
    ∃ output, yulStatement input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (yulStatement_ordinary_success_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {value : YulStmt} {remainder : DeclarativeGrammar.Remainder}
    (result : yulStatement input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.YulStatementOrdinaryParses input.declarativeRemainder value remainder :=
  (yulStatement_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulStatementPublicRejects input.declarativeRemainder rejected) :
    ∃ failure output, yulStatement input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (yulStatement_ordinary_reject_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {failure : Failure} {rejected : DeclarativeGrammar.Remainder}
    (result : yulStatement input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.YulStatementPublicRejects input.declarativeRemainder rejected :=
  (yulStatement_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example := @yulBody_ordinary_success_iff
example := @yulBody_ordinary_reject_iff

example {input : State} (inputValid : input.ValidFor)
    {value : YulParsedBlock} {remainder : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulBodyOrdinaryParses input.declarativeRemainder value.span value.body remainder) :
    ∃ output, yulBody input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (yulBody_ordinary_success_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {value : YulParsedBlock} {remainder : DeclarativeGrammar.Remainder}
    (result : yulBody input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.YulBodyOrdinaryParses input.declarativeRemainder value.span value.body remainder :=
  (yulBody_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulBodyRejects input.declarativeRemainder rejected) :
    ∃ failure output, yulBody input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (yulBody_ordinary_reject_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {failure : Failure} {rejected : DeclarativeGrammar.Remainder}
    (result : yulBody input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.YulBodyRejects input.declarativeRemainder rejected :=
  (yulBody_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example := @yulExpression_boundary_reject_iff
example := @yulStatement_boundary_reject_iff

end Solcore.Test.SyntaxParserYulPublicCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulSignatureTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulSignatureTotalityProperties

open Solcore.Syntax.Parser

example := @yulParameters_ordinary
example := @yulParameters_invariantFreeOnValid
example := @yulParameters_ne_invariant
example := @yulParameters_elementTotalityContract
example := @yulReturnClause_ordinary
example := @yulReturnClause_invariantFreeOnValid
example := @yulReturnClause_ne_invariant
example := @yulReturnClause_cursor_lt_onSuccess
example := @yulReturnClause_elementTotalityContract
example := @yulReturns_ordinary
example := @yulReturns_invariantFreeOnValid
example := @yulReturns_ne_invariant

end Solcore.Test.SyntaxParserYulSignatureTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulStatementChoiceFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementChoiceFuelTotalityProperties

open Solcore.Syntax.Parser

example := @recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
example := @stateChoice_fuelTotalityContract
example := @stateChoice_cursor_lt_onSuccess_of_strict
example := @orElse_fuelTotalityContract
example := @orElse_cursor_lt_onSuccess_of_strict

end Solcore.Test.SyntaxParserYulStatementChoiceFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulStatementCoreFuelTotalityProperties
/-! Compile-time consumers for complete Yul statement-core totality. -/

namespace Solcore.Test.SyntaxParserYulStatementCoreFuelTotalityProperties

open Solcore.Syntax.Parser

example := @yulStatementCore_fuelTotalityContract
example := @yulStatementCore_cursor_lt_onSuccess

end Solcore.Test.SyntaxParserYulStatementCoreFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulStatementExactnessProperties
/-! External consumers of exact recursive Yul statement and body outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeclarativeGrammar.YulBlockItemsParses.result_unique
example := @DeclarativeGrammar.YulBlockItemsRejects.output_unique
example := @DeclarativeGrammar.yulBlockExactOutcomeSpec
example := @DeclarativeGrammar.YulNamesOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulExpressionStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.yulExpressionStatementExactOutcomeSpec
example := @DeclarativeGrammar.YulReturnBuiltinOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulControlTokenOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulLetStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulAssignmentOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulIfStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulForStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulFunctionStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.YulSwitchStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.OptionalYulDefaultParses.result_unique
example := @DeclarativeGrammar.YulNameStatementOrdinaryParses.value_unique
example := @DeclarativeGrammar.yulStatementCoreExactOutcomeSpec
example := @DeclarativeGrammar.yulStatementTerminatedExactOutcomeSpec
example := @DeclarativeGrammar.YulStatementRecoveryScanParses.value_unique
example := @DeclarativeGrammar.yulStatementLayerExactOutcomeSpec
example := @DeclarativeGrammar.YulBodyOrdinaryParses.result_unique
example := @DeclarativeGrammar.YulBodyRejects.output_unique

example (fuel : Nat) : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.YulStatementRejectsWithFuel fuel) :=
  yulStatementWithFuel_exactOutcomeSpec fuel

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.YulStatementOrdinaryParses
    DeclarativeGrammar.YulStatementPublicRejects :=
  yulStatement_publicExactOutcomeSpec

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.YulStatementOrdinaryParses
    DeclarativeGrammar.YulStatementRejects :=
  yulStatement_exactOutcomeSpec

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.YulBodyOutcomeParses DeclarativeGrammar.YulBodyRejects :=
  yulBody_exactOutcomeSpec

example (fuel : Nat) {input leftOutput rightOutput : State}
    {left right : YulStmt}
    (leftResult : yulStatementWithFuel fuel input = .ok left leftOutput)
    (rightResult : yulStatementWithFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulStatementWithFuel_success_result_unique fuel leftResult rightResult

example (fuel : Nat) {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : yulStatementWithFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : yulStatementWithFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulStatementWithFuel_reject_output_unique fuel leftResult rightResult

example {input leftOutput rightOutput : State} {left right : YulStmt}
    (leftResult : yulStatement input = .ok left leftOutput)
    (rightResult : yulStatement input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulStatement_success_result_unique leftResult rightResult

example {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulStatement input = .reject leftFailure leftOutput)
    (rightResult : yulStatement input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulStatement_reject_output_unique leftResult rightResult

example {input leftOutput rightOutput : State} {left right : YulParsedBlock}
    (leftResult : yulBody input = .ok left leftOutput)
    (rightResult : yulBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulBody_success_result_unique leftResult rightResult

example {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulBody input = .reject leftFailure leftOutput)
    (rightResult : yulBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  yulBody_reject_output_unique leftResult rightResult

end Solcore.Test.SyntaxParserYulStatementExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulDeclarativeSoundnessProperties
/-! External consumers for public Yul statement and body soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulDeclarativeSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TransactionalFallbackOrdinaryParses.value_unique
example := @TransactionalFallbackOrdinaryParses.result_unique
example := @TransactionalFallbackRejects.output_unique
example := @transactionalFallbackExactOutcomeSpec
example := @TransactionalFallbackOrdinaryParses.value_unique_of_success
example := @TransactionalFallbackOrdinaryParses.result_unique_of_success

example {alpha : Type}
    (primaryParses fallbackParses : Remainder → alpha → Remainder → Prop)
    (primaryRejects fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses fallbackRejects)
    (primaryValues : ∀ {input left right afterLeft afterRight},
      primaryParses input left afterLeft →
      primaryParses input right afterRight → left = right)
    (fallbackValues : ∀ {input left right afterLeft afterRight},
      fallbackParses input left afterLeft →
      fallbackParses input right afterRight → left = right) :
    ExactDeterministicOutcomeSpec
      (TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (TransactionalFallbackRejects primaryRejects fallbackRejects) :=
  transactionalFallbackExactOutcomeSpecOfSuccess primaryParses fallbackParses
    primaryRejects fallbackRejects primaryOutcomes fallbackOutcomes
    primaryValues fallbackValues

example := @YulStatementParses
example := @YulStatementOrdinaryParses
example := @YulStatementPublicRejects
example := @yulStatementPublicOutcomeSpec

example := @yulStatement_success_clean_sound
example := @yulStatement_success_ordinary_sound
example := @yulStatement_reject_ordinary_sound
example := @yulStatement_reject_boundary_sound

example {input output : State} {statement : YulStmt}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulStatement input = .ok statement output) :
    YulStatementParses input.declarativeRemainder statement
      output.declarativeRemainder :=
  yulStatement_success_clean_sound diagnosticFree result

example {input output : State} {statement : YulStmt}
    (result : yulStatement input = .ok statement output) :
    YulStatementOrdinaryParses input.declarativeRemainder statement
      output.declarativeRemainder :=
  yulStatement_success_ordinary_sound result

example {input rejected : State} {failure : Failure}
    (result : yulStatement input = .reject failure rejected) :
    YulStatementPublicRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  yulStatement_reject_ordinary_sound result

example :
    DeterministicOutcomeSpec YulStatementOrdinaryParses
      YulStatementPublicRejects :=
  yulStatementPublicOutcomeSpec

example := @YulBodyParses
example := @YulBodyOrdinaryParses
example := @YulBodyRejects
example := @YulBodyOutcomeParses

example := @yulBody_success_clean_sound
example := @yulBody_success_ordinary_sound
example := @yulBody_reject_ordinary_sound
example := @yulBody_success_outcome_sound
example := @yulBody_publicOutcomeSpec

example {input output : State} {body : YulParsedBlock}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulBody input = .ok body output) :
    YulBodyParses input.declarativeRemainder body.span body.body
      output.declarativeRemainder :=
  yulBody_success_clean_sound diagnosticFree result

example {input output : State} {body : YulParsedBlock}
    (result : yulBody input = .ok body output) :
    YulBodyOrdinaryParses input.declarativeRemainder body.span body.body
      output.declarativeRemainder :=
  yulBody_success_ordinary_sound result

example {input rejected : State} {failure : Failure}
    (result : yulBody input = .reject failure rejected) :
    YulBodyRejects input.declarativeRemainder rejected.declarativeRemainder :=
  yulBody_reject_ordinary_sound result

example {input output : State} {body : YulParsedBlock}
    (result : yulBody input = .ok body output) :
    YulBodyOutcomeParses input.declarativeRemainder {
      span := body.span
      body := body.body
    } output.declarativeRemainder :=
  yulBody_success_outcome_sound result

example :
    DeterministicOutcomeSpec YulBodyOutcomeParses YulBodyRejects :=
  yulBody_publicOutcomeSpec

end Solcore.Test.SyntaxParserYulDeclarativeSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulStatementFallbackFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementFallbackFuelTotalityProperties

open Solcore.Syntax.Parser

example := @FuelYulStatementTotalityContract.weaken
example := @FuelYulStatementTotalityContract.ne_invariant
example := @FuelYulStatementTotalityContract.ofTotality
example := @recognizedYulStatementOrFallback_ordinary_of_fuels
example := @recognizedYulStatementOrFallback_fuelTotalityContract
example := @optionalYulSemicolon_ordinary
example := @yulStatementTerminated_cursor_lt_onSuccess_of_core
example := @yulStatementTerminated_ordinary_of_coreFuel
example := @yulStatementTerminated_fuelTotalityContract

end Solcore.Test.SyntaxParserYulStatementFallbackFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulStatementLeafStrictTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementLeafStrictTotalityProperties

open Solcore.Syntax.Parser

example := @yulLetStatement_cursor_lt_onSuccess
example := @yulAssignment_cursor_lt_onSuccess
example := @yulExpressionStatement_cursor_lt_onSuccess
example := @yulReturnBuiltin_cursor_lt_onSuccess
example := @yulControlToken_cursor_lt_onSuccess
example := @YulStatementTotalityContract.elementTotalityContract
example := @yulLetStatement_elementTotalityContract
example := @yulAssignment_elementTotalityContract
example := @yulExpressionStatement_elementTotalityContract
example := @yulReturnBuiltin_elementTotalityContract
example := @yulControlToken_elementTotalityContract
example := @yulLeaveControl_elementTotalityContract
example := @yulBreakControl_elementTotalityContract
example := @yulContinueControl_elementTotalityContract

end Solcore.Test.SyntaxParserYulStatementLeafStrictTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulStatementLeafTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementLeafTotalityProperties

open Solcore.Syntax.Parser

example := @yulLetInitializer_ordinary
example := @yulLetInitializer_ne_invariant
example := @yulLetStatement_ordinary
example := @yulLetStatement_ne_invariant
example := @yulAssignment_ordinary
example := @yulAssignment_ne_invariant
example := @yulExpressionStatement_ordinary
example := @yulExpressionStatement_ne_invariant
example := @yulReturnBuiltin_ordinary
example := @yulReturnBuiltin_ne_invariant
example := @yulControlToken_ordinary
example := @yulControlToken_ne_invariant
example := @YulStatementTotalityContract.ne_invariant
example := @yulLetStatement_totalityContract
example := @yulAssignment_totalityContract
example := @yulExpressionStatement_totalityContract
example := @yulReturnBuiltin_totalityContract
example := @yulControlToken_totalityContract

end Solcore.Test.SyntaxParserYulStatementLeafTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulStatementProperties
/-! External consumers for inline-Yul leaf-statement contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulBlockStatement_validFor
example := @yulBlockStatement_preservesTokensOnSuccess
example := @yulBlockStatement_cursorMonotoneOnSuccess
example := @yulBlockStatement_startsAtCurrentTokenOnSuccess
example := @yulStatementCore_contracts
example := @yulStatementCore_validFor
example := @yulStatementCore_preservesTokensOnSuccess
example := @yulStatementCore_cursorMonotoneOnSuccess
example := @yulStatementCore_startsAtCurrentTokenOnSuccess
example := yulLetInitializer_validFor
example := yulLetInitializer_preservesTokenWindow
example := yulLetInitializer_cursorMonotoneOnSuccess
example := yulLetStatement_validFor
example := yulLetStatement_preservesTokenWindow
example := yulLetStatement_preservesTokensOnSuccess
example := yulLetStatement_cursorMonotoneOnSuccess
example := yulLetStatement_startsAtCurrentTokenOnSuccess
example := yulAssignment_validFor
example := yulAssignment_preservesTokensOnSuccess
example := yulAssignment_cursorMonotoneOnSuccess
example := yulAssignment_startsAtCurrentTokenOnSuccess

example := yulExpressionStatement_validFor
example := yulExpressionStatement_preservesTokenWindow
example := yulExpressionStatement_preservesTokensOnSuccess
example := yulExpressionStatement_cursorMonotoneOnSuccess
example := yulExpressionStatement_startsAtCurrentTokenOnSuccess

example := yulReturnBuiltin_validFor
example := yulReturnBuiltin_preservesTokenWindow
example := yulReturnBuiltin_preservesTokensOnSuccess
example := yulReturnBuiltin_cursorMonotoneOnSuccess
example := yulReturnBuiltin_startsAtCurrentTokenOnSuccess

example := yulLeaveControl_validFor
example := yulBreakControl_validFor
example := yulContinueControl_validFor
example := @yulControlToken_preservesTokenWindow
example := @yulControlToken_preservesTokensOnSuccess
example := @yulControlToken_cursorMonotoneOnSuccess
example := @yulControlToken_startsAtCurrentTokenOnSuccess
example := @recognizedYulStatementOrFallback_validFor
example := @recognizedYulStatementOrFallback_preservesTokenWindow
example := @recognizedYulStatementOrFallback_preservesTokensOnSuccess
example := @recognizedYulStatementOrFallback_cursorMonotoneOnSuccess
example := @recognizedYulStatementOrFallback_startsAtCurrentTokenOnSuccess
example := @optionalYulSemicolon_validForAt
example := @optionalYulSemicolon_preservesTokenWindow
example := @optionalYulSemicolon_cursorMonotoneOnSuccess
example := @optionalYulSemicolon_value_eq
example := @yulStatementTerminated_validFor
example := @yulStatementTerminated_preservesTokensOnSuccess
example := @yulStatementTerminated_cursorMonotoneOnSuccess
example := @yulStatementTerminated_startsAtCurrentTokenOnSuccess
example := @finishRecoveredYulStatement_validFor
example := @recoverYulStatementAux_validFor
example := @recoverYulStatementAux_preservesTokenWindow
example := @recoverYulStatementAux_preservesTokensOnSuccess
example := @recoverYulStatementAux_cursorMonotoneOnSuccess
example := @yulStatementTerminated_preservesTokenWindow
example := @yulStatementLayer_validFor
example := @yulStatementLayer_preservesTokenWindow
example := @yulStatementLayer_preservesTokensOnSuccess
example := @yulStatementLayer_cursorMonotoneOnSuccess
example := @yulStatementLayer_startsAtCurrentTokenOnSuccess
example := @yulStatementWithFuel_preservesTokenWindow
example := @yulStatementWithFuel_preservesTokensOnSuccess
example := @yulStatementWithFuel_validFor
example := @yulStatementWithFuel_cursorMonotoneOnSuccess
example := @yulStatementWithFuel_startsAtCurrentTokenOnSuccess
example := @yulBlockStatement_preservesTokenWindow
example := @yulAssignment_preservesTokenWindow
example := @yulStatementCore_preservesTokenWindow
example := yulStatement_preservesTokenWindow
example := yulStatement_preservesTokensOnSuccess
example := yulStatement_validFor
example := yulStatement_cursorMonotoneOnSuccess
example := yulStatement_startsAtCurrentTokenOnSuccess
example := yulBody_validFor
example := yulBody_preservesTokenWindow
example := yulBody_preservesTokensOnSuccess
example := yulBody_cursorMonotoneOnSuccess
example := yulBody_startsAtCurrentTokenOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulStatementRecoveryFuelTotalityProperties
/-! Compile-time consumers for Yul statement recovery totality. -/

namespace Solcore.Test.SyntaxParserYulStatementRecoveryFuelTotalityProperties

open Solcore.Syntax.Parser

example := @recoverYulStatementAux_exists_ok_of_remainingCount_lt
example := @recoverYulStatementAux_ordinary_of_remainingCount_lt
example := @recoverYulStatementAux_production_exists_ok
example := @recoverYulStatementAux_production_ordinary
example := @recoverYulStatementAux_production_invariantFreeOnValid
example := @recoverYulStatementAux_production_ne_invariant
example := @recoverYulStatementAux_ne_invariant_of_remainingCount_lt
example := @yulStatementLayer_ordinary_of_terminatedFuel
example := @yulStatementLayer_ne_invariant_of_terminatedFuel
example := @yulStatementLayer_cursor_lt_onSuccess_of_terminated
example := @yulStatementLayer_fuelTotalityContract

end Solcore.Test.SyntaxParserYulStatementRecoveryFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserYulStatementRecursiveFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementRecursiveFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulStatementWithFuel_cursor_lt_onSuccess
example := @yulStatementWithFuel_fuelTotalityContract
example := @yulStatement_ordinary
example := @yulStatement_invariantFreeOnValid
example := @yulStatement_ne_invariant
example := @yulStatement_cursor_lt_onSuccess
example := @yulStatement_totalityContract

example (fuel : Nat) :
    FuelYulStatementTotalityContract (yulStatementWithFuel fuel) fuel :=
  yulStatementWithFuel_fuelTotalityContract fuel

end Solcore.Test.SyntaxParserYulStatementRecursiveFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxYulStatementValidity
/-! External consumers for recursive inline-Yul statement validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @List.ValidFor
example := @YulReturnClause.ValidFor
example := @YulStmt.ValidFor
example := @YulCase.ValidFor
example := @YulStmt.ValidFor.span_valid
example := @YulCase.ValidFor.span_valid

example (file : SourceFile) (span : SourceSpan)
    (body : List YulStmt)
    (spanValid : span.ValidFor file)
    (bodyValid : List.ValidFor YulStmt.ValidFor file body) :
    YulStmt.ValidFor file { span, value := .block body } :=
  .block spanValid bodyValid

example (file : SourceFile) (span : SourceSpan)
    (scrutinee : YulExpr) (cases : NonemptyList YulCase)
    (defaultBody : Option (List YulStmt))
    (spanValid : span.ValidFor file)
    (scrutineeValid : YulExpr.ValidFor file scrutinee)
    (casesValid : cases.ValidFor YulCase.ValidFor file)
    (defaultValid : ∀ statements ∈ defaultBody,
      ∀ statement ∈ statements, YulStmt.ValidFor file statement) :
    YulStmt.ValidFor file {
      span
      value := .switch scrutinee cases defaultBody
    } :=
  .switch spanValid scrutineeValid casesValid defaultValid

end Tests
end
