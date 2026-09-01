import Solcore.Syntax.DeclarativeCoreAssignmentStatementOutcomeProperties
import Solcore.Syntax.DeclarativeCoreForItemOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreStatementSimpleOutcomeProperties

/-! Deterministic ordinary outcomes for the two Core `for` item branches. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

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

/-- Ordinary `for let` success has one final remainder. -/
theorem ForLetItemOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForLetItemOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ForLetItemOrdinaryParses expressionOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftType leftInitializer =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightType
            rightInitializer =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          have afterTypeEq := leftType.output_unique typeOutcomes rightType
          subst afterTypeEq
          exact OptionalLetInitializerOrdinaryParses.output_unique
            expressionOutcomes leftInitializer rightInitializer

/-- Exact `for let` rejection excludes ordinary success. -/
theorem ForLetItemRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input rejected : Remainder}
    (rejection : ForLetItemRejects expressionOrdinary expressionRejects
      typeRejects input rejected) :
    ¬ ∃ item output,
      ForLetItemOrdinaryParses expressionOrdinary input item output := by
  rintro ⟨item, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulName
        successfulType successfulInitializer =>
      cases rejection with
      | markerRejected markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | nameRejected rejectedMarkerSpan rejectedMarker rejectedName =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact rejectedName.disjoint ⟨_, _, successfulName⟩
      | typeRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedType =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          exact (OptionalLetTypeRejects.disjointOrdinary typeOutcomes
            rejectedType) ⟨_, _, successfulType⟩
      | initializerRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedType rejectedInitializer =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterTypeEq := rejectedType.output_unique typeOutcomes
            successfulType
          subst afterTypeEq
          exact (OptionalLetInitializerRejects.disjointOrdinary
            expressionOutcomes rejectedInitializer)
              ⟨_, _, successfulInitializer⟩

/-- Lift expression and type outcomes through one `for let` item. -/
theorem forLetItemDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects typeRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects) :
    DeterministicOutcomeSpec
      (ForLetItemOrdinaryParses expressionOrdinary)
      (ForLetItemRejects expressionOrdinary expressionRejects typeRejects)
    where
  successOutputUnique := ForLetItemOrdinaryParses.output_unique
    expressionOutcomes typeOutcomes
  successRejectDisjoint := ForLetItemRejects.disjointOrdinary
    expressionOutcomes typeOutcomes

/-- Ordinary non-let `for` item success has one final remainder. -/
theorem ForAssignmentOrExpressionOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForAssignmentOrExpressionOrdinaryParses expressionOrdinary
      input left afterLeft)
    (rightParsed : ForAssignmentOrExpressionOrdinaryParses expressionOrdinary
      input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftExpression, leftAfterExpression, leftTail, leftExpressionParsed,
      leftTailParsed, leftBuild⟩
  rcases rightParsed with
    ⟨rightExpression, rightAfterExpression, rightTail,
      rightExpressionParsed, rightTailParsed, rightBuild⟩
  have afterExpressionEq := expressionOutcomes.successOutputUnique
    leftExpressionParsed rightExpressionParsed
  subst afterExpressionEq
  exact leftTailParsed.output_unique expressionOutcomes rightTailParsed

/-- Exact non-let item rejection excludes ordinary success. -/
theorem ForAssignmentOrExpressionRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : ForAssignmentOrExpressionRejects expressionOrdinary
      expressionRejects input rejected) :
    ¬ ∃ item output,
      ForAssignmentOrExpressionOrdinaryParses expressionOrdinary input item
        output := by
  rintro ⟨item, output, left, afterLeft, tail, leftParsed, tailParsed,
    builds⟩
  cases rejection with
  | leftRejected leftRejected =>
      exact expressionOutcomes.successRejectDisjoint leftRejected
        ⟨left, afterLeft, leftParsed⟩
  | rightRejected rejectedLeft rejectedTilde rejectedOperator
        rightRejected =>
      have afterLeftEq := expressionOutcomes.successOutputUnique rejectedLeft
        leftParsed
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
              exact expressionOutcomes.successRejectDisjoint rightRejected
                ⟨_, _, rightParsed⟩

/-- Lift expression outcomes through the non-let `for` item branch. -/
theorem forAssignmentOrExpressionDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (ForAssignmentOrExpressionOrdinaryParses expressionOrdinary)
      (ForAssignmentOrExpressionRejects expressionOrdinary
        expressionRejects) where
  successOutputUnique :=
    ForAssignmentOrExpressionOrdinaryParses.output_unique expressionOutcomes
  successRejectDisjoint :=
    ForAssignmentOrExpressionRejects.disjointOrdinary expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
