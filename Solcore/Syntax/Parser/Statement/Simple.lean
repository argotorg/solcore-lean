import Solcore.Syntax.Parser.Block
import Solcore.Syntax.Parser.Expression

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace StatementSimpleInternals

def valueAssignOp? : TokenKind → Option ValueAssignOp
  | .symbol .equal => some .equal
  | .symbol .plusEqual => some .add
  | .symbol .minusEqual => some .subtract
  | .symbol .starEqual => some .multiply
  | .symbol .slashEqual => some .divide
  | .symbol .percentEqual => some .modulo
  | .symbol .ampEqual => some .bitAnd
  | .symbol .caretEqual => some .bitXor
  | .symbol .pipeEqual => some .bitOr
  | _ => none

def valueAssignOperator : Parser (Located ValueAssignOp) := fun state =>
  match state.peek? with
  | some token => match valueAssignOp? token.value with
    | some operator => .ok { span := token.span, value := operator }
        { state with cursor := state.cursor + 1 }
    | none => rejectAt state { head := .expression, tail := [] } .statement
  | none => rejectAt state { head := .expression, tail := [] } .statement

end StatementSimpleInternals

private inductive AssignmentTail where
  | value (operator : Located ValueAssignOp) (right : Expr)
  | bitNot (operator : SourceSpan)

private def assignmentTail
    (expression : Parser Expr) : Parser AssignmentTail := fun state =>
  if isSymbol state .tildeEqual then
    match symbol .tildeEqual .statement state with
    | .ok operator next => .ok (.bitNot operator.span) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else match state.peekKind?.bind StatementSimpleInternals.valueAssignOp? with
    | some _ =>
        match StatementSimpleInternals.valueAssignOperator state with
        | .ok operator afterOperator =>
            match expression afterOperator with
            | .ok right next => .ok (.value operator right) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
    | none => rejectAt state { head := .expression, tail := [] } .statement

private def optionalAssignmentTail
    (expression : Parser Expr) : Parser (Option AssignmentTail) := fun state =>
  if isSymbol state .tildeEqual ||
      (state.peekKind?.bind StatementSimpleInternals.valueAssignOp?).isSome then
    match assignmentTail expression state with
    | .ok value next => .ok (some value) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    .ok none state

private def optionalSemicolon : Parser (Option SourceSpan) := do
  let state ← getState
  if isSymbol state .semicolon then
    pure (some (← symbol .semicolon .statement).span)
  else
    pure none

private def assignmentEnd : AssignmentTail → SourceSpan
  | .value _ right => right.span
  | .bitNot operator => operator

/-- Parse an expression statement or source-preserving assignment. -/
def assignmentOrExpressionStatement
    (expression : Parser Expr) : Parser Statement := do
  let left ← expression
  let tail ← optionalAssignmentTail expression
  let semicolon ← optionalSemicolon
  let endSpan := match semicolon, tail with
    | some marker, _ => marker
    | none, some value => assignmentEnd value
    | none, none => left.span
  let span := SourceSpan.cover left.span endSpan
  match tail with
  | some (.value operator right) =>
      if semicolon.isNone then
        let _ ← emitDiagnostic {
          span
          kind := .constraintViolation .assignmentRequiresSemicolon
        }
      pure { span, value := .assignValue left operator right }
  | some (.bitNot operator) =>
      if semicolon.isNone then
        let _ ← emitDiagnostic {
          span
          kind := .constraintViolation .assignmentRequiresSemicolon
        }
      pure { span, value := .assignBitNot left operator }
  | none => pure {
      span
      value := .expression left semicolon.isSome
    }

/-- Parse a semicolon-terminated Core `let` statement. -/
def letStatement (expression : Parser Expr) : Parser Statement := do
  let marker ← keyword .letKw .statement
  let name ← identifier .statement
  let state ← getState
  let type ←
    if isSymbol state .colon then
      let _ ← symbol .colon .statement
      pure (some (← typeExpr))
    else
      pure none
  let state ← getState
  let initializer ←
    if isSymbol state .equal then
      let _ ← symbol .equal .statement
      pure (some (← expression))
    else
      pure none
  let semicolon ← symbol .semicolon .statement
  pure {
    span := SourceSpan.cover marker.span semicolon.span
    value := .letDecl name type initializer
  }

/-- Parse a semicolon-terminated Core `return` statement. -/
def returnStatement (expression : Parser Expr) : Parser Statement := do
  let marker ← keyword .returnKw .statement
  let state ← getState
  let value ←
    if isSymbol state .semicolon then pure none
    else pure (some (← expression))
  let semicolon ← symbol .semicolon .statement
  pure {
    span := SourceSpan.cover marker.span semicolon.span
    value := .returnStmt value
  }

private def forLetItem (expression : Parser Expr) : Parser ForItem := do
  let marker ← keyword .letKw .statement
  let name ← identifier .statement
  let state ← getState
  let type ←
    if isSymbol state .colon then
      let _ ← symbol .colon .statement
      pure (some (← typeExpr))
    else pure none
  let state ← getState
  let initializer ←
    if isSymbol state .equal then
      let _ ← symbol .equal .statement
      pure (some (← expression))
    else pure none
  let endSpan := initializer.map (fun value => value.span) |>.getD
    (type.map (fun value => value.span) |>.getD name.span)
  pure {
    span := SourceSpan.cover marker.span endSpan
    value := .letDecl name type initializer
  }

private def forAssignmentOrExpression
    (expression : Parser Expr) : Parser ForItem := do
  let left ← expression
  let tail ← optionalAssignmentTail expression
  match tail with
  | some (.value operator right) => pure {
      span := SourceSpan.cover left.span right.span
      value := .assignValue left operator right
    }
  | some (.bitNot operator) => pure {
      span := SourceSpan.cover left.span operator
      value := .assignBitNot left operator
    }
  | none => pure { span := left.span, value := .expression left }

/-- Restricted item accepted in one canonical `for` header list. -/
def forItem (expression : Parser Expr) : Parser ForItem := fun state =>
  if isKeyword state .letKw then forLetItem expression state
  else forAssignmentOrExpression expression state

end Solcore.Syntax.Parser
