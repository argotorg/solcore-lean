import Solcore.Syntax.Parser.Yul.Control

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Lift a parsed Yul block into statement position. -/
def yulBlockStatement (statement : Parser YulStmt) : Parser YulStmt := do
  let block ← yulBlock statement
  pure { span := block.span, value := .block block.body }

/-- Parse an optional initializer following a Yul name sequence. -/
def yulLetInitializer : Parser (Option YulExpr) := do
  let state ← getState
  if isSymbol state .colonEqual then
    let _ ← symbol .colonEqual .yulStatement
    pure (some (← yulExpression))
  else
    pure none

/-- Parse a Yul `let` declaration. -/
def yulLetStatement : Parser YulStmt := do
  let marker ← keyword .letKw .yulStatement
  let names ← yulNames
  let initializer ← yulLetInitializer
  let endSpan := initializer.map (fun value => value.span) |>.getD names.span
  pure {
    span := SourceSpan.cover marker.span endSpan
    value := .letDecl names.names initializer
  }

/-- Parse a nonempty Yul assignment. -/
def yulAssignment : Parser YulStmt := do
  let names ← yulNames
  let _ ← symbol .colonEqual .yulStatement
  let value ← yulExpression
  pure {
    span := SourceSpan.cover names.span value.span
    value := .assign names.names value
  }

/-- Lift a Yul expression into statement position. -/
def yulExpressionStatement : Parser YulStmt := do
  let expression ← yulExpression
  pure { span := expression.span, value := .expression expression }

/-- Parse source-level `return(...)` as the corresponding Yul call statement. -/
def yulReturnBuiltin : Parser YulStmt := do
  let marker ← keyword .returnKw .yulStatement
  let arguments ← delimited .leftParen .rightParen true yulExpression
    .yulExpression .yul
  let span := SourceSpan.cover marker.span arguments.span
  let callee : YulIdentifier := { span := marker.span, value := "return" }
  let expression : YulExpr := {
    span
    value := .call callee arguments
  }
  pure { span, value := .expression expression }

/-- Parse one keyword-only Yul control statement. -/
def yulControlToken (value : HardKeyword)
    (result : YulStmtValue) : Parser YulStmt := do
  let marker ← keyword value .yulStatement
  pure { span := marker.span, value := result }

/-!
Chumsky's ordered statement choice rewinds a rejected recognized branch before
trying its final expression branch.  The expression parser may recover to a
`YulExpr.error`; retain that AST and its cursor, but replace its speculative
diagnostics with the more precise failure reached by the recognized branch.
-/
def recognizedYulStatementOrFallback
    (primary fallback : Parser YulStmt) : Parser YulStmt := fun state =>
  match primary state with
  | .ok value next => .ok value next
  | .reject failure _ =>
      match fallback state with
      | .ok value next =>
          let reset := { next with diagnosticsRev := state.diagnosticsRev }
          .ok value (reset.emit failure.toDiagnostic)
      | .reject _ _ => .reject failure state
      | .invariant error => .invariant error
  | .invariant error => .invariant error

/-- Select one non-terminating Yul statement form. -/
def yulStatementCore (nested : Parser YulStmt) : Parser YulStmt :=
    fun state =>
  let fallback := yulExpressionStatement
  if isSymbol state .leftBrace then
    recognizedYulStatementOrFallback
      (yulBlockStatement nested) fallback state
  else if isKeyword state .letKw then
    recognizedYulStatementOrFallback yulLetStatement fallback state
  else if isKeyword state .ifKw then
    recognizedYulStatementOrFallback
      (yulIfStatement nested) fallback state
  else if isKeyword state .forKw then
    recognizedYulStatementOrFallback
      (yulForStatement nested) fallback state
  else if isKeyword state .switchKw then
    recognizedYulStatementOrFallback
      (yulSwitchStatement nested) fallback state
  else if isKeyword state .functionKw then
    recognizedYulStatementOrFallback
      (yulFunctionStatement nested) fallback state
  else if isKeyword state .returnKw then
    recognizedYulStatementOrFallback yulReturnBuiltin fallback state
  else if isKeyword state .leaveKw then
    recognizedYulStatementOrFallback
      (yulControlToken .leaveKw .leave) fallback state
  else if isKeyword state .breakKw then
    recognizedYulStatementOrFallback
      (yulControlToken .breakKw .break) fallback state
  else if isKeyword state .continueKw then
    recognizedYulStatementOrFallback
      (yulControlToken .continueKw .continue) fallback state
  else if startsYulName state then
    orElse yulAssignment fallback state
  else
    fallback state

/-- Consume an optional semicolon without changing the parsed statement. -/
def optionalYulSemicolon (value : YulStmt) : Parser YulStmt := do
  let state ← getState
  if isSymbol state .semicolon then
    let _ ← symbol .semicolon .yulStatement
    pure value
  else
    pure value

/-- Parse one statement and its optional trailing semicolon. -/
def yulStatementTerminated
    (nested : Parser YulStmt) : Parser YulStmt := do
  optionalYulSemicolon (← yulStatementCore nested)

/-- Finish statement recovery with one diagnosed error node. -/
def finishRecoveredYulStatement (first last : SourceSpan)
    (state : State) : Reply YulStmt :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .yulStatement
  })

/-- Scan to a Yul statement boundary using explicit fuel. -/
def recoverYulStatementAux (first last : SourceSpan) :
    Nat → State → Reply YulStmt
  | 0, state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || isSymbol state .rightBrace then
        finishRecoveredYulStatement first last state
      else
        match state.advance? with
        | some (token, next) =>
            recoverYulStatementAux first token.span fuel next
        | none => finishRecoveredYulStatement first last state

/-- Parse one recovering statement layer around a recursive statement parser. -/
def yulStatementLayer (nested : Parser YulStmt) : Parser YulStmt :=
    fun state =>
  match yulStatementTerminated nested state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if rewound.atEnd || isSymbol rewound .rightBrace then
        .reject failure rewound
      else
        match rewound.advance? with
        | some (token, next) =>
            recoverYulStatementAux token.span token.span
              (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
        | none => .reject failure rewound
  | .invariant error => .invariant error

/-- Iterate recovering statement layers with explicit recursion fuel. -/
def yulStatementWithFuel : Nat → Parser YulStmt
  | 0 => fun state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1 => yulStatementLayer (yulStatementWithFuel fuel)

/-- Parse one complete inline-Yul statement. -/
def yulStatement : Parser YulStmt := fun state =>
  yulStatementWithFuel (state.remainingCount + 1) state

/-- Parse a complete braced inline-Yul statement sequence. -/
def yulBody : Parser YulParsedBlock := yulBlock yulStatement

end Solcore.Syntax.Parser
