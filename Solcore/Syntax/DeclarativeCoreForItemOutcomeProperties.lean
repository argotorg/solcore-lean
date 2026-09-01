import Solcore.Syntax.DeclarativeCoreForItemLeafOutcomeProperties

/-! Deterministic outcomes for the let-prioritized public Core `for` item. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Public ordinary `for` item success has one final remainder. -/
theorem ForItemOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ForItemOrdinaryParses expressionOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | letItem leftLet =>
      cases rightParsed with
      | letItem rightLet =>
          exact ForLetItemOrdinaryParses.output_unique expressionOutcomes
            typeOutcomes leftLet rightLet
      | assignmentOrExpression letAbsent rightFallback =>
          cases leftLet with
          | parsed markerSpan marker name type initializer =>
              exact False.elim (absent_conflicts_exact letAbsent marker)
  | assignmentOrExpression leftAbsent leftFallback =>
      cases rightParsed with
      | letItem rightLet =>
          cases rightLet with
          | parsed markerSpan marker name type initializer =>
              exact False.elim (absent_conflicts_exact leftAbsent marker)
      | assignmentOrExpression rightAbsent rightFallback =>
          exact ForAssignmentOrExpressionOrdinaryParses.output_unique
            expressionOutcomes leftFallback rightFallback

/-- Exact public `for` item rejection excludes every ordinary success. -/
theorem ForItemRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input rejected : Remainder}
    (rejection : ForItemRejects expressionOrdinary expressionRejects
      typeRejects input rejected) :
    ¬ ∃ item output,
      ForItemOrdinaryParses expressionOrdinary input item output := by
  rintro ⟨item, output, successful⟩
  cases rejection with
  | letItem markerCurrent itemRejected =>
      cases successful with
      | letItem itemParsed =>
          exact itemRejected.disjointOrdinary expressionOutcomes typeOutcomes
            ⟨_, _, itemParsed⟩
      | assignmentOrExpression letAbsent itemParsed =>
          exact letAbsent ⟨_, markerCurrent⟩
  | assignmentOrExpression letAbsent itemRejected =>
      cases successful with
      | letItem itemParsed =>
          cases itemParsed with
          | parsed markerSpan marker name type initializer =>
              exact absent_conflicts_exact letAbsent marker
      | assignmentOrExpression otherAbsent itemParsed =>
          exact itemRejected.disjointOrdinary expressionOutcomes
            ⟨_, _, itemParsed⟩

/-- Lift expression and type outcomes through the prioritized public item. -/
theorem forItemDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects) :
    DeterministicOutcomeSpec
      (ForItemOrdinaryParses expressionOrdinary)
      (ForItemRejects expressionOrdinary expressionRejects typeRejects) where
  successOutputUnique := ForItemOrdinaryParses.output_unique
    expressionOutcomes typeOutcomes
  successRejectDisjoint := ForItemRejects.disjointOrdinary
    expressionOutcomes typeOutcomes

end Solcore.Syntax.DeclarativeGrammar
