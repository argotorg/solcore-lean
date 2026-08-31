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

namespace StatementSimpleInternals

inductive AssignmentTail where
  | value (operator : Located ValueAssignOp) (right : Expr)
  | bitNot (operator : SourceSpan)

def assignmentTail
    (expression : Parser Expr) : Parser AssignmentTail := fun state =>
  if isSymbol state .tildeEqual then
    (do
      let operator ← symbol .tildeEqual .statement
      pure (AssignmentTail.bitNot operator.span)) state
  else match state.peekKind?.bind StatementSimpleInternals.valueAssignOp? with
    | some _ =>
        (do
          let operator ← StatementSimpleInternals.valueAssignOperator
          let right ← expression
          pure (AssignmentTail.value operator right)) state
    | none => rejectAt state { head := .expression, tail := [] } .statement

def optionalAssignmentTail
    (expression : Parser Expr) : Parser (Option AssignmentTail) := fun state =>
  if isSymbol state .tildeEqual ||
      (state.peekKind?.bind StatementSimpleInternals.valueAssignOp?).isSome then
    (do
      let value ← assignmentTail expression
      pure (some value)) state
  else
    .ok none state

def optionalSemicolon : Parser (Option SourceSpan) := do
  let state ← getState
  if isSymbol state .semicolon then
    pure (some (← symbol .semicolon .statement).span)
  else
    pure none

/-- Parse the optional expression before a required return semicolon. -/
def optionalReturnValue
    (expression : Parser Expr) : Parser (Option Expr) := do
  let state ← getState
  if isSymbol state .semicolon then
    pure none
  else
    pure (some (← expression))

/-- Parse an optional `: type` annotation shared by Core `let` forms. -/
def optionalLetType : Parser (Option TypeExpr) := do
  let state ← getState
  if isSymbol state .colon then
    let _ ← symbol .colon .statement
    pure (some (← typeExpr))
  else
    pure none

/-- Parse an optional `= expression` initializer shared by Core `let` forms. -/
def optionalLetInitializer
    (expression : Parser Expr) : Parser (Option Expr) := do
  let state ← getState
  if isSymbol state .equal then
    let _ ← symbol .equal .statement
    pure (some (← expression))
  else
    pure none

def assignmentEnd : AssignmentTail → SourceSpan
  | .value _ right => right.span
  | .bitNot operator => operator

/-- Select the final source span of an assignment or expression statement. -/
def statementEnd (left : Expr) (tail : Option AssignmentTail)
    (semicolon : Option SourceSpan) : SourceSpan :=
  match semicolon, tail with
  | some marker, _ => marker
  | none, some value => assignmentEnd value
  | none, none => left.span

end StatementSimpleInternals

/-- Parse an expression statement or source-preserving assignment. -/
def assignmentOrExpressionStatement
    (expression : Parser Expr) : Parser Statement := do
  let left ← expression
  let tail ← StatementSimpleInternals.optionalAssignmentTail expression
  let semicolon ← StatementSimpleInternals.optionalSemicolon
  let endSpan := StatementSimpleInternals.statementEnd left tail semicolon
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
  let type ← StatementSimpleInternals.optionalLetType
  let initializer ←
    StatementSimpleInternals.optionalLetInitializer expression
  let semicolon ← symbol .semicolon .statement
  pure {
    span := SourceSpan.cover marker.span semicolon.span
    value := .letDecl name type initializer
  }

/-- Parse a semicolon-terminated Core `return` statement. -/
def returnStatement (expression : Parser Expr) : Parser Statement := do
  let marker ← keyword .returnKw .statement
  let value ← StatementSimpleInternals.optionalReturnValue expression
  let semicolon ← symbol .semicolon .statement
  pure {
    span := SourceSpan.cover marker.span semicolon.span
    value := .returnStmt value
  }

private def forLetItem (expression : Parser Expr) : Parser ForItem := do
  let marker ← keyword .letKw .statement
  let name ← identifier .statement
  let type ← StatementSimpleInternals.optionalLetType
  let initializer ←
    StatementSimpleInternals.optionalLetInitializer expression
  let endSpan := initializer.map (fun value => value.span) |>.getD
    (type.map (fun value => value.span) |>.getD name.span)
  pure {
    span := SourceSpan.cover marker.span endSpan
    value := .letDecl name type initializer
  }

private def forAssignmentOrExpression
    (expression : Parser Expr) : Parser ForItem := do
  let left ← expression
  let tail ← StatementSimpleInternals.optionalAssignmentTail expression
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
