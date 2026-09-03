import Solcore.Syntax.DeclarativeYulExpressionExactnessProperties
import Solcore.Syntax.DeclarativeYulLetOrdinaryOutcomeProperties
import Solcore.Syntax.DeclarativeYulNameStatementOutcomeProperties
import Solcore.Syntax.DeclarativeYulNamesExactnessProperties

/-! Exact ASTs of basic inline-Yul statement primaries. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lifting an ordinary expression to statement position fixes its AST. -/
theorem YulExpressionStatementOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionStatementOrdinaryParses input left afterLeft)
    (rightParsed : YulExpressionStatementOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftExpression =>
      cases rightParsed with
      | parsed rightExpression =>
          cases leftExpression.value_unique rightExpression
          rfl

/-- Expression-statement rejection has one exact non-consuming endpoint. -/
theorem YulExpressionStatementRejects.output_eq {input rejected : Remainder}
    (rejectedAt : YulExpressionStatementRejects input rejected) : rejected = input := by
  cases rejectedAt with
  | expressionRejected rejection => exact rejection.output_eq

/-- Public ordinary expressions give exact expression-statement outcomes. -/
theorem yulExpressionStatementExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulExpressionStatementOrdinaryParses
      YulExpressionStatementRejects where
  toDeterministicOutcomeSpec := yulExpressionStatementDeterministicOutcomeSpec
  successValueUnique := YulExpressionStatementOrdinaryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    rw [leftRejected.output_eq, rightRejected.output_eq]

/-- The synthesized source-level return call has one complete AST. -/
theorem YulReturnBuiltinOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulReturnBuiltinOrdinaryParses input left afterLeft)
    (rightParsed : YulReturnBuiltinOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftArguments =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightArguments =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          cases leftArguments.value_unique yulExpressionExactOutcomeSpec rightArguments
          rfl

/-- Keyword-only Yul statements have the exact current token span and AST. -/
theorem YulControlTokenOrdinaryParses.value_unique
    {keyword : HardKeyword} {statementValue : Syntax.YulStmtValue}
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulControlTokenOrdinaryParses keyword statementValue input left afterLeft)
    (rightParsed : YulControlTokenOrdinaryParses keyword statementValue input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftToken =>
      cases rightParsed with
      | parsed rightSpan rightToken =>
          cases leftToken.span_unique rightToken
          rfl

/-- The optional initializer fixes its absence/presence branch and expression. -/
theorem YulLetInitializerOrdinaryParses.value_unique
    {input : Remainder} {left right : Option Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulLetInitializerOrdinaryParses input left afterLeft)
    (rightParsed : YulLetInitializerOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present _ rightToken _ => exact False.elim (leftAbsent ⟨_, rightToken.1⟩)
  | present _ leftToken leftExpression =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent ⟨_, leftToken.1⟩)
      | present _ rightToken rightExpression =>
          have outputEq := leftToken.output_unique rightToken
          subst outputEq
          exact congrArg some (leftExpression.value_unique rightExpression)

/-- Ordinary let statements fix exact names, initializer, and covering span. -/
theorem YulLetStatementOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulLetStatementOrdinaryParses input left afterLeft)
    (rightParsed : YulLetStatementOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftNames leftInitializer =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightNames rightInitializer =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases leftNames.result_unique rightNames with ⟨namesEq, namesOutputEq⟩
          subst namesEq
          subst namesOutputEq
          cases leftInitializer.value_unique rightInitializer
          rfl

/-- Ordinary assignments fix the forward target list, expression, and span. -/
theorem YulAssignmentOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulAssignmentOrdinaryParses input left afterLeft)
    (rightParsed : YulAssignmentOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftNames leftOperator leftExpression =>
      cases rightParsed with
      | parsed rightSpan rightNames rightOperator rightExpression =>
          rcases leftNames.result_unique rightNames with ⟨namesEq, namesOutputEq⟩
          subst namesEq
          subst namesOutputEq
          have outputEq := leftOperator.output_unique rightOperator
          subst outputEq
          cases leftExpression.value_unique rightExpression
          rfl

end Solcore.Syntax.DeclarativeGrammar
