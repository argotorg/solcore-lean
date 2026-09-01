import Solcore.Syntax.DeclarativeCoreAssignmentStatementOutcomeGrammar

/-!
Functionality, rejection exclusivity, and clean embedding for ordinary Core
assignment-or-expression statement outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem valueOperator_output_unique
    {input leftOutput rightOutput : Remainder}
    {leftOperator rightOperator : Located ValueAssignOp}
    (leftParsed : ValueAssignOperatorParses input leftOperator leftOutput)
    (rightParsed : ValueAssignOperatorParses input rightOperator rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- A parsed assignment suffix has a unique output remainder. -/
theorem AssignmentTailParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : CoreAssignmentTail}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssignmentTailParses expressionOrdinary input left
      afterLeft)
    (rightParsed : AssignmentTailParses expressionOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | bitNot leftSpan leftToken =>
      cases rightParsed with
      | bitNot rightSpan rightToken => rw [leftToken.2, rightToken.2]
      | value rightAbsent rightOperator rightExpression =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
  | value leftAbsent leftOperator leftExpression =>
      cases rightParsed with
      | bitNot rightSpan rightToken =>
          exact False.elim (absent_conflicts_exact leftAbsent rightToken)
      | value rightAbsent rightOperator rightExpression =>
          have operatorEq := valueOperator_output_unique leftOperator
            rightOperator
          subst operatorEq
          exact outcomes.successOutputUnique leftExpression rightExpression

/-- Maximal optional assignment suffix parsing has a unique remainder. -/
theorem OptionalAssignmentTailParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option CoreAssignmentTail}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalAssignmentTailParses expressionOrdinary input left
      afterLeft)
    (rightParsed : OptionalAssignmentTailParses expressionOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightTail =>
          cases rightTail with
          | bitNot span token =>
              exact False.elim (absent_conflicts_exact leftAbsent.1 token)
          | value tildeAbsent operatorParsed expressionParsed =>
              exact False.elim (leftAbsent.2
                ⟨_, _, operatorParsed.1⟩)
  | present leftTail =>
      cases rightParsed with
      | absent rightAbsent =>
          cases leftTail with
          | bitNot span token =>
              exact False.elim (absent_conflicts_exact rightAbsent.1 token)
          | value tildeAbsent operatorParsed expressionParsed =>
              exact False.elim (rightAbsent.2
                ⟨_, _, operatorParsed.1⟩)
      | present rightTail =>
          exact leftTail.output_unique outcomes rightTail

/-- Maximal optional statement-semicolon parsing has a unique remainder. -/
theorem OptionalStatementSemicolonParses.output_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalStatementSemicolonParses input left afterLeft)
    (rightParsed : OptionalStatementSemicolonParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightToken =>
          exact False.elim (absent_conflicts_exact leftAbsent rightToken)
  | present leftSpan leftToken =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
      | present rightSpan rightToken => rw [leftToken.2, rightToken.2]

/-- Ordinary Core fallback success has a unique output remainder. -/
theorem AssignmentOrExpressionStatementOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftExpression, leftAfterExpression, leftTail, leftAfterTail,
      leftSemicolon, leftExpressionParsed, leftTailParsed,
      leftSemicolonParsed, leftBuild⟩
  rcases rightParsed with
    ⟨rightExpression, rightAfterExpression, rightTail, rightAfterTail,
      rightSemicolon, rightExpressionParsed, rightTailParsed,
      rightSemicolonParsed, rightBuild⟩
  have expressionEq := outcomes.successOutputUnique leftExpressionParsed
    rightExpressionParsed
  subst expressionEq
  have tailEq := leftTailParsed.output_unique outcomes rightTailParsed
  subst tailEq
  exact leftSemicolonParsed.output_unique rightSemicolonParsed

/-- Exact fallback rejection excludes every ordinary fallback success. -/
theorem AssignmentOrExpressionStatementRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects input rejected) :
    ¬ ∃ statement output,
      AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary input
        statement output := by
  rintro ⟨statement, output, left, afterLeft, tail, afterTail, semicolon,
    leftParsed, tailParsed, semicolonParsed, builds⟩
  cases rejection with
  | leftRejected leftRejected =>
      exact outcomes.successRejectDisjoint leftRejected
        ⟨left, afterLeft, leftParsed⟩
  | rightRejected rejectedLeft rejectedTilde rejectedOperator
        rightRejected =>
      have afterLeftEq := outcomes.successOutputUnique rejectedLeft leftParsed
      subst afterLeftEq
      cases tailParsed with
      | absent tailAbsent =>
          exact tailAbsent.2 ⟨_, _, rejectedOperator.1⟩
      | present successfulTail =>
          cases successfulTail with
          | bitNot span token =>
              exact absent_conflicts_exact rejectedTilde token
          | value successfulTilde successfulOperator rightParsed =>
              have afterOperatorEq := valueOperator_output_unique
                rejectedOperator successfulOperator
              subst afterOperatorEq
              exact outcomes.successRejectDisjoint rightRejected
                ⟨_, _, rightParsed⟩

/-- Ordinary assignment/expression outcomes form a deterministic contract. -/
theorem assignmentOrExpressionStatementDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary)
      (AssignmentOrExpressionStatementRejects expressionOrdinary
        expressionRejects) where
  successOutputUnique :=
    AssignmentOrExpressionStatementOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    AssignmentOrExpressionStatementRejects.disjointOrdinary outcomes

/-- A clean assignment suffix embeds into its ordinary counterpart. -/
theorem OptionalAssignmentTailParses.toOrdinary
    {cleanExpression ordinaryExpression :
      Remainder → Syntax.Expr → Remainder → Prop}
    (cleanToOrdinary : ∀ {input value output},
      cleanExpression input value output →
        ordinaryExpression input value output)
    {input output : Remainder} {tail : Option CoreAssignmentTail}
    (parsed : OptionalAssignmentTailParses cleanExpression input tail output) :
    OptionalAssignmentTailParses ordinaryExpression input tail output := by
  cases parsed with
  | absent tailAbsent => exact .absent tailAbsent
  | present tailParsed =>
      apply OptionalAssignmentTailParses.present
      cases tailParsed with
      | bitNot operatorSpan operatorParsed =>
          exact .bitNot operatorSpan operatorParsed
      | value tildeAbsent operatorParsed rightParsed =>
          exact .value tildeAbsent operatorParsed
            (cleanToOrdinary rightParsed)

/-- Every clean Core fallback success is the same ordinary success. -/
theorem AssignmentOrExpressionStatementParses.toOrdinary
    {cleanExpression ordinaryExpression :
      Remainder → Syntax.Expr → Remainder → Prop}
    (cleanToOrdinary : ∀ {input value output},
      cleanExpression input value output →
        ordinaryExpression input value output)
    {input output : Remainder} {statement : Syntax.Statement}
    (parsed : AssignmentOrExpressionStatementParses cleanExpression input
      statement output) :
    AssignmentOrExpressionStatementOrdinaryParses ordinaryExpression input
      statement output := by
  rcases parsed with ⟨left, afterLeft, tail, afterTail, semicolon,
    leftParsed, tailParsed, semicolonParsed, builds⟩
  refine ⟨left, afterLeft, tail, afterTail, semicolon,
    cleanToOrdinary leftParsed, tailParsed.toOrdinary cleanToOrdinary,
    semicolonParsed, ?_⟩
  cases builds with
  | expression => exact .expression _ _
  | value => exact .value _ _ _ _
  | bitNot => exact .bitNot _ _ _

end Solcore.Syntax.DeclarativeGrammar
