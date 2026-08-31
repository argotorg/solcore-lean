import Solcore.Syntax.Parser.Statement.Match
import Solcore.Syntax.Parser.Yul.Statement

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def forItemsTail (expression : Parser Expr) (stop : Symbol) :
    Nat → List ForItem → State → Reply (List ForItem)
  | 0, _, state => .invariant (.fuelExhausted .statement state.currentSpan)
  | fuel + 1, itemsRev, state =>
      if isSymbol state .comma then
        match symbol .comma .statement state with
        | .ok _ afterComma =>
            if isSymbol afterComma stop then
              rejectAt afterComma { head := .expression, tail := [] } .statement
            else
              let before := afterComma.cursor
              match forItem expression afterComma with
              | .ok value next =>
                  if next.cursor > before then
                    forItemsTail expression stop fuel (value :: itemsRev) next
                  else
                    .invariant (.noProgress .statement next.currentSpan)
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok itemsRev.reverse state

private def forItems (expression : Parser Expr)
    (stop : Symbol) : Parser (List ForItem) := fun state =>
  if isSymbol state stop then
    .ok [] state
  else
    match forItem expression state with
    | .ok first next =>
        forItemsTail expression stop (next.remainingCount + 1) [first] next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

def forStatement (statement : Parser Statement)
    (expression : Parser Expr) : Parser Statement := do
  let marker ← keyword .forKw .statement
  let opening ← symbol .leftParen .statement
  let initializer ← forItems expression .semicolon
  let _ ← symbol .semicolon .statement
  let condition ← expression
  let _ ← symbol .semicolon .statement
  let post ← forItems expression .rightParen
  let closing ← symbol .rightParen .statement
  let body ← coreBlock statement .require
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .forLoop (SourceSpan.cover opening.span closing.span)
      initializer condition post body
  }

def whileStatement (statement : Parser Statement)
    (expression : Parser Expr) : Parser Statement := do
  let marker ← contextual .while .statement
  let _ ← symbol .leftParen .statement
  let condition ← expression
  let _ ← symbol .rightParen .statement
  let body ← coreBlock statement .require
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .whileLoop condition body
  }

namespace ControlInternals

/-- Parse the optional `else` keyword and its required braced body. -/
def optionalElseBody (statement : Parser Statement) :
    Parser (Option Block) := do
  let state ← getState
  if isKeyword state .elseKw then
    let _ ← keyword .elseKw .statement
    pure (some (← coreBlock statement .require))
  else
    pure none

end ControlInternals

def ifStatement (statement : Parser Statement)
    (expression : Parser Expr) : Parser Statement := do
  let marker ← keyword .ifKw .statement
  let _ ← symbol .leftParen .statement
  let condition ← expression
  let _ ← symbol .rightParen .statement
  let thenBody ← coreBlock statement .require
  let elseBody ← ControlInternals.optionalElseBody statement
  let endSpan := elseBody.map (fun body => body.span) |>.getD thenBody.span
  pure {
    span := SourceSpan.cover marker.span endSpan
    value := .ifThen condition thenBody elseBody
  }

def assemblyStatement : Parser Statement := do
  let marker ← keyword .assemblyKw .statement
  let body ← yulBody
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .assembly body.body
  }

def blockStatement (statement : Parser Statement) : Parser Statement := do
  let body ← coreBlock statement .require
  pure { span := body.span, value := .block body.value }

private def terminatedControl (keywordValue : HardKeyword)
    (value : StatementValue) : Parser Statement := do
  let marker ← keyword keywordValue .statement
  let semicolon ← symbol .semicolon .statement
  pure {
    span := SourceSpan.cover marker.span semicolon.span
    value
  }

def breakStatement : Parser Statement :=
  terminatedControl .breakKw .breakStmt

def continueStatement : Parser Statement :=
  terminatedControl .continueKw .continueStmt

end Solcore.Syntax.Parser
