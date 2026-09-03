import Solcore.Syntax.DeclarativeCoreAssignmentStatementExactnessProperties
import Solcore.Syntax.DeclarativeCoreForItemOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementSimpleValueProperties

/-! Exact success values for prioritized Core `for` header items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact expressions fix a for-header let item, including its optional type,
initializer, and source span. -/
theorem ForLetItemOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForLetItemOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ForLetItemOrdinaryParses expressionOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftName leftType leftInitializer =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightName rightType rightInitializer =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          rcases leftName.result_unique rightName with ⟨nameEq, inputEq⟩
          subst nameEq
          subst inputEq
          rcases leftType.result_unique rightType with ⟨typeEq, inputEq⟩
          subst typeEq
          subst inputEq
          have initializerEq :=
            (OptionalLetInitializerOrdinaryParses.result_unique
              expressionOutcomes leftInitializer rightInitializer).1
          subst initializerEq
          rfl

/-- Exact expressions fix a for-header assignment/expression item's AST. -/
theorem ForAssignmentOrExpressionOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForAssignmentOrExpressionOrdinaryParses expressionOrdinary
      input left afterLeft)
    (rightParsed : ForAssignmentOrExpressionOrdinaryParses expressionOrdinary
      input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftExpression, leftAfterExpression, leftTail,
    leftExpressionParsed, leftTailParsed, leftBuild⟩
  rcases rightParsed with ⟨rightExpression, rightAfterExpression, rightTail,
    rightExpressionParsed, rightTailParsed, rightBuild⟩
  rcases expressionOutcomes.successResultUnique leftExpressionParsed
      rightExpressionParsed with ⟨expressionEq, inputEq⟩
  subst expressionEq
  subst inputEq
  have tailEq := (leftTailParsed.result_unique expressionOutcomes
    rightTailParsed).1
  subst tailEq
  cases leftBuild <;> cases rightBuild <;> rfl

/-- Let-token priority and exact child values fix a complete for-header item. -/
theorem ForItemOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ForItemOrdinaryParses expressionOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | letItem leftItem =>
      cases rightParsed with
      | letItem rightItem =>
          exact ForLetItemOrdinaryParses.value_unique expressionOutcomes
            leftItem rightItem
      | assignmentOrExpression rightAbsent rightItem =>
          cases leftItem with
          | parsed span marker name type initializer =>
              exact False.elim (rightAbsent ⟨span, marker.1⟩)
  | assignmentOrExpression leftAbsent leftItem =>
      cases rightParsed with
      | letItem rightItem =>
          cases rightItem with
          | parsed span marker name type initializer =>
              exact False.elim (leftAbsent ⟨span, marker.1⟩)
      | assignmentOrExpression rightAbsent rightItem =>
          exact ForAssignmentOrExpressionOrdinaryParses.value_unique
            expressionOutcomes leftItem rightItem

/-- A successful for-header item fixes its full AST and remainder. -/
theorem ForItemOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ForItemOrdinaryParses expressionOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨ForItemOrdinaryParses.value_unique expressionOutcomes leftParsed rightParsed,
    ForItemOrdinaryParses.output_unique
      expressionOutcomes.toDeterministicOutcomeSpec
      typeExprExactOutcomeSpec.toDeterministicOutcomeSpec leftParsed
      rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
