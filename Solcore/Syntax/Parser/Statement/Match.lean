import Solcore.Syntax.Parser.Pattern
import Solcore.Syntax.Parser.Statement.Simple

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def requireScrutinees (values : DelimitedList Expr) :
    Parser (NonemptyDelimitedList Expr) :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .statement values.span)

namespace MatchInternals

def matchCase (statement : Parser Statement)
    (pattern : Parser Pattern) : Parser MatchCase := do
  let marker ← keyword .caseKw .statement
  let pattern ← pattern
  let body ← coreBlock statement .require
  pure {
    span := SourceSpan.cover marker.span body.span
    value := { pattern, body }
  }

def matchCases (statement : Parser Statement)
    (pattern : Parser Pattern) :
    Nat → List MatchCase → State → Reply (List MatchCase)
  | 0, _, state => .invariant (.fuelExhausted .statement state.currentSpan)
  | fuel + 1, casesRev, state =>
      if isKeyword state .caseKw then
        let before := state.cursor
        match matchCase statement pattern state with
        | .ok value next =>
            if next.cursor > before then
              matchCases statement pattern fuel (value :: casesRev) next
            else
              .invariant (.noProgress .statement next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok casesRev.reverse state

end MatchInternals

private def optionalDefaultBody (statement : Parser Statement) :
    Parser (Option Block) := do
  let state ← getState
  if isKeyword state .defaultKw then
    let _ ← keyword .defaultKw .statement
    pure (some (← coreBlock statement .require))
  else
    pure none

private def patternArity (scrutineeCount : Nat)
    (pattern : Pattern) : Nat :=
  if scrutineeCount > 1 then
    match pattern.value with
    | .tuple elements => elements.elements.length
    | _ => 1
  else
    1

private def validateMatchCaseArity (scrutineeCount : Nat)
    (case : MatchCase) : Parser Unit :=
  let count := patternArity scrutineeCount case.value.pattern
  if count == scrutineeCount then
    pure ()
  else
    emitDiagnostic {
      span := case.span
      kind := .constraintViolation
        (.matchArityMismatch scrutineeCount count)
    }

private def validateMatchArities (scrutineeCount : Nat) :
    List MatchCase → Parser Unit
  | [] => pure ()
  | case :: rest => do
      let _ ← validateMatchCaseArity scrutineeCount case
      validateMatchArities scrutineeCount rest

/-- Parse a canonical multi-scrutinee `match` statement. -/
def matchStatement (statement : Parser Statement)
    (expression : Parser Expr) (pattern : Parser Pattern) : Parser Statement := do
  let marker ← keyword .matchKw .statement
  let scrutineeValues ← delimited .leftParen .rightParen false expression
    .expression .statement
  let scrutinees ← requireScrutinees scrutineeValues
  let opening ← symbol .leftBrace .statement
  let cases ← fun state =>
    MatchInternals.matchCases statement pattern
      (state.remainingCount + 1) [] state
  let defaultBody ← optionalDefaultBody statement
  let closing ← symbol .rightBrace .statement
  let armsSpan := SourceSpan.cover opening.span closing.span
  let _ ← validateMatchArities scrutinees.elements.toList.length cases
  if cases.isEmpty && defaultBody.isNone then
    let _ ← emitDiagnostic {
      span := SourceSpan.cover marker.span closing.span
      kind := .constraintViolation .matchRequiresArm
    }
  else
    pure ()
  pure {
    span := SourceSpan.cover marker.span closing.span
    value := .matchWith scrutinees {
      span := armsSpan
      value := { cases, defaultBody }
    }
  }

end Solcore.Syntax.Parser
