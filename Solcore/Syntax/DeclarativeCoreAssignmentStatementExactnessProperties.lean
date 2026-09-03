import Solcore.Syntax.DeclarativeCoreAssignmentStatementOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementSemicolonExactnessProperties

/-!
Exact ordinary Core assignment-or-expression statements from exact expression
outcomes. The proofs preserve assignment priority, optional suffixes, source
spans, diagnosed missing-semicolon successes, and rejection endpoints.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem assignment_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A value-assignment token fixes its operator, source span, and remainder. -/
theorem ValueAssignOperatorParses.result_unique
    {input leftOutput rightOutput : Remainder}
    {leftOperator rightOperator : Located ValueAssignOp}
    (leftParsed : ValueAssignOperatorParses input leftOperator leftOutput)
    (rightParsed : ValueAssignOperatorParses input rightOperator rightOutput) :
    leftOperator = rightOperator ∧ leftOutput = rightOutput := by
  have tokenEq := leftParsed.1.token_unique rightParsed.1
  cases leftOperator with
  | mk leftSpan leftValue =>
      cases rightOperator with
      | mk rightSpan rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp_all [ValueAssignOperatorParses, ValueAssignOp.symbol]
          all_goals exact leftParsed.output_unique rightParsed

/-- Exact expression outcomes fix a prioritized assignment suffix and its
final remainder. -/
theorem AssignmentTailParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : CoreAssignmentTail}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssignmentTailParses expressionOrdinary input left
      afterLeft)
    (rightParsed : AssignmentTailParses expressionOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | bitNot leftSpan leftToken =>
      cases rightParsed with
      | bitNot rightSpan rightToken =>
          rcases leftToken.result_unique rightToken with
            ⟨spanEq, outputEq⟩
          exact ⟨congrArg CoreAssignmentTail.bitNot spanEq, outputEq⟩
      | value rightAbsent rightOperator rightExpression =>
          exact False.elim
            (assignment_absent_conflicts_exact rightAbsent leftToken)
  | value leftAbsent leftOperator leftExpression =>
      cases rightParsed with
      | bitNot rightSpan rightToken =>
          exact False.elim
            (assignment_absent_conflicts_exact leftAbsent rightToken)
      | value rightAbsent rightOperator rightExpression =>
          rcases leftOperator.result_unique rightOperator with
            ⟨operatorEq, afterOperatorEq⟩
          subst operatorEq
          subst afterOperatorEq
          rcases outcomes.successResultUnique leftExpression rightExpression
            with ⟨expressionEq, outputEq⟩
          subst expressionEq
          exact ⟨rfl, outputEq⟩

/-- Maximal optional assignment suffixes fix their value and remainder under
exact expression outcomes. -/
theorem OptionalAssignmentTailParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option CoreAssignmentTail}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalAssignmentTailParses expressionOrdinary input left
      afterLeft)
    (rightParsed : OptionalAssignmentTailParses expressionOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present rightTail =>
          cases rightTail with
          | bitNot span token =>
              exact False.elim
                (assignment_absent_conflicts_exact leftAbsent.1 token)
          | value tildeAbsent operator expression =>
              exact False.elim (leftAbsent.2 ⟨_, _, operator.1⟩)
  | present leftTail =>
      cases rightParsed with
      | absent rightAbsent =>
          cases leftTail with
          | bitNot span token =>
              exact False.elim
                (assignment_absent_conflicts_exact rightAbsent.1 token)
          | value tildeAbsent operator expression =>
              exact False.elim (rightAbsent.2 ⟨_, _, operator.1⟩)
      | present rightTail =>
          rcases leftTail.result_unique outcomes rightTail with
            ⟨tailEq, outputEq⟩
          exact ⟨congrArg some tailEq, outputEq⟩

/-- Ordinary fallback success fixes the complete statement AST, including
assignments whose missing semicolon is diagnosed. -/
theorem AssignmentOrExpressionStatementOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input right afterRight) : left = right := by
  rcases leftParsed with
    ⟨leftExpression, leftAfterExpression, leftTail, leftAfterTail,
      leftSemicolon, leftExpressionParsed, leftTailParsed,
      leftSemicolonParsed, leftBuild⟩
  rcases rightParsed with
    ⟨rightExpression, rightAfterExpression, rightTail, rightAfterTail,
      rightSemicolon, rightExpressionParsed, rightTailParsed,
      rightSemicolonParsed, rightBuild⟩
  rcases outcomes.successResultUnique leftExpressionParsed
      rightExpressionParsed with ⟨expressionEq, afterExpressionEq⟩
  subst expressionEq
  subst afterExpressionEq
  rcases leftTailParsed.result_unique outcomes rightTailParsed with
    ⟨tailEq, afterTailEq⟩
  subst tailEq
  subst afterTailEq
  rcases leftSemicolonParsed.result_unique rightSemicolonParsed with
    ⟨semicolonEq, outputEq⟩
  subst semicolonEq
  cases leftBuild <;> cases rightBuild <;> rfl

/-- Ordinary fallback success fixes both its statement AST and remainder. -/
theorem AssignmentOrExpressionStatementOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- Exact expression outcomes fix the initial-expression or committed
right-operand rejection endpoint of an ordinary fallback statement. -/
theorem AssignmentOrExpressionStatementRejects.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input left right : Remainder}
    (leftRejects : AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects input left)
    (rightRejects : AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects input right) : left = right := by
  cases leftRejects with
  | leftRejected leftExpression =>
      cases rightRejects with
      | leftRejected rightExpression =>
          exact outcomes.rejectOutputUnique leftExpression rightExpression
      | rightRejected rightLeft rightTilde rightOperator rightExpression =>
          exact False.elim
            (outcomes.successRejectDisjoint leftExpression
              ⟨_, _, rightLeft⟩)
  | rightRejected leftLeft leftTilde leftOperator leftExpression =>
      cases rightRejects with
      | leftRejected rightExpression =>
          exact False.elim
            (outcomes.successRejectDisjoint rightExpression
              ⟨_, _, leftLeft⟩)
      | rightRejected rightLeft rightTilde rightOperator rightExpression =>
          have afterLeftEq := outcomes.successOutputUnique leftLeft rightLeft
          subst afterLeftEq
          have afterOperatorEq :=
            (leftOperator.result_unique rightOperator).2
          subst afterOperatorEq
          exact outcomes.rejectOutputUnique leftExpression rightExpression

/-- Exact expression outcomes lift to exact ordinary assignment and
expression-statement fallback outcomes. -/
theorem assignmentOrExpressionStatementExactOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    ExactDeterministicOutcomeSpec
      (AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary)
      (AssignmentOrExpressionStatementRejects expressionOrdinary
        expressionRejects) where
  toDeterministicOutcomeSpec :=
    assignmentOrExpressionStatementDeterministicOutcomeSpec
      outcomes.toDeterministicOutcomeSpec
  successValueUnique :=
    AssignmentOrExpressionStatementOrdinaryParses.value_unique outcomes
  rejectOutputUnique :=
    AssignmentOrExpressionStatementRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
