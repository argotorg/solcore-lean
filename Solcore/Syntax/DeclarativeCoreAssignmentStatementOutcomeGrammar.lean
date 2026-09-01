import Solcore.Syntax.DeclarativeCoreAssignmentStatementGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes for a Core assignment-or-expression
statement.  Ordinary success includes the executable parser's diagnosed
missing-semicolon assignment cases; the existing clean grammar remains the
diagnostic-free subset.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Statement construction after all ordinary suffix stages have succeeded.
Unlike the clean builder, assignment cases also allow an absent semicolon. -/
inductive AssignmentOrExpressionOrdinaryBuilds :
    Syntax.Expr → Option CoreAssignmentTail → Option SourceSpan →
      Syntax.Statement → Prop where
  | expression (left : Syntax.Expr) (semicolon : Option SourceSpan) :
      AssignmentOrExpressionOrdinaryBuilds left none semicolon {
        span := SourceSpan.cover left.span (statementEnd left none semicolon)
        value := .expression left semicolon.isSome
      }
  | value (left right : Syntax.Expr) (operator : Located ValueAssignOp)
      (semicolon : Option SourceSpan) :
      AssignmentOrExpressionOrdinaryBuilds left
        (some (.value operator right)) semicolon {
          span := SourceSpan.cover left.span
            (statementEnd left (some (.value operator right)) semicolon)
          value := .assignValue left operator right
        }
  | bitNot (left : Syntax.Expr) (operator : SourceSpan)
      (semicolon : Option SourceSpan) :
      AssignmentOrExpressionOrdinaryBuilds left (some (.bitNot operator))
        semicolon {
          span := SourceSpan.cover left.span
            (statementEnd left (some (.bitNot operator)) semicolon)
          value := .assignBitNot left operator
        }

/-- Exact ordinary success of the Core assignment/expression fallback. -/
def AssignmentOrExpressionStatementOrdinaryParses
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (input : Remainder) (statement : Syntax.Statement)
    (output : Remainder) : Prop :=
  ∃ left afterLeft tail afterTail semicolon,
    expressionOrdinary input left afterLeft ∧
      OptionalAssignmentTailParses expressionOrdinary afterLeft tail
        afterTail ∧
      OptionalStatementSemicolonParses afterTail semicolon output ∧
      AssignmentOrExpressionOrdinaryBuilds left tail semicolon statement

/-- Exact rejection trace of the Core assignment/expression fallback.
Only the initial expression and a committed value-assignment right operand
can reject; `~=` and both optional suffixes otherwise complete immediately. -/
inductive AssignmentOrExpressionStatementRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | leftRejected {input rejected : Remainder}
      (leftRejected : expressionRejects input rejected) :
      AssignmentOrExpressionStatementRejects expressionOrdinary
        expressionRejects input rejected
  | rightRejected
      {input afterLeft afterOperator rejected : Remainder}
      {left : Syntax.Expr} {operator : Located ValueAssignOp}
      (leftParsed : expressionOrdinary input left afterLeft)
      (tildeEqualAbsent : TokenKindAbsentAt afterLeft.tokens
        afterLeft.endIndex afterLeft.cursor (.symbol .tildeEqual))
      (operatorParsed : ValueAssignOperatorParses afterLeft operator
        afterOperator)
      (rightRejected : expressionRejects afterOperator rejected) :
      AssignmentOrExpressionStatementRejects expressionOrdinary
        expressionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
