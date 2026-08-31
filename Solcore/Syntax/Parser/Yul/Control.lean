import Solcore.Syntax.Parser.Yul.Common

set_option autoImplicit false

namespace Solcore.Syntax.Parser

def yulIfStatement (statement : Parser YulStmt) : Parser YulStmt := do
  let marker ← keyword .ifKw .yulStatement
  let condition ← yulExpression
  let body ← yulBlock statement
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .ifThen condition body.body
  }

def yulForStatement (statement : Parser YulStmt) : Parser YulStmt := do
  let marker ← keyword .forKw .yulStatement
  let initializer ← yulBlock statement
  let condition ← yulExpression
  let post ← yulBlock statement
  let body ← yulBlock statement
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .forLoop initializer.body condition post.body body.body
  }

private def yulCase (statement : Parser YulStmt) : Parser YulCase := do
  let marker ← keyword .caseKw .yulStatement
  let literal ← yulLiteral
  let body ← yulBlock statement
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .arm literal body.body
  }

private def yulCases (statement : Parser YulStmt) :
    Nat → List YulCase → State → Reply (List YulCase)
  | 0, _, state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1, casesRev, state =>
      if isKeyword state .caseKw then
        let before := state.cursor
        match yulCase statement state with
        | .ok value next =>
            if next.cursor > before then
              yulCases statement fuel (value :: casesRev) next
            else
              .invariant (.noProgress .yul next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok casesRev.reverse state

private def optionalYulDefault (statement : Parser YulStmt) :
    Parser (Option YulParsedBlock) := do
  let state ← getState
  if isKeyword state .defaultKw then
    let _ ← keyword .defaultKw .yulStatement
    pure (some (← yulBlock statement))
  else
    pure none

def yulSwitchStatement (statement : Parser YulStmt) : Parser YulStmt := do
  let marker ← keyword .switchKw .yulStatement
  let scrutinee ← yulExpression
  let cases ← fun current =>
    yulCases statement (current.remainingCount + 1) [] current
  let defaultBody ← optionalYulDefault statement
  let endSpan := match defaultBody with
    | some body => body.span
    | none => match cases.reverse with
      | last :: _ => last.span
      | [] => scrutinee.span
  let span := SourceSpan.cover marker.span endSpan
  match cases with
  | head :: tail => pure {
      span
      value := .switch scrutinee { head, tail }
        (defaultBody.map (fun body => body.body))
    }
  | [] =>
      let _ ← emitDiagnostic {
        span
        kind := .constraintViolation .yulSwitchRequiresCase
      }
      pure { span, value := .error }

private def yulReturns : Parser (Option YulReturnClause) := do
  let state ← getState
  if isSymbol state .arrow then
    let arrow ← symbol .arrow .yulStatement
    let names ← yulNames
    pure (some {
      span := SourceSpan.cover arrow.span names.span
      value := { arrow := arrow.span, names := names.names }
    })
  else
    pure none

def yulFunctionStatement (statement : Parser YulStmt) : Parser YulStmt := do
  let marker ← keyword .functionKw .yulStatement
  let name ← yulName
  let parameters ← yulParameters
  let returns ← yulReturns
  let body ← yulBlock statement
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .functionDef name parameters returns body.body
  }

end Solcore.Syntax.Parser
