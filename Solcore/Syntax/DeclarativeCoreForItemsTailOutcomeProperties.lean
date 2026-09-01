import Solcore.Syntax.DeclarativeCoreForItemOutcomeProperties
import Solcore.Syntax.DeclarativeCoreForItemsOutcomeGrammar

/-! Deterministic ordinary outcomes for Core `for` item-list tails. -/

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

/-- An ordinary Core `for` item-list tail has one final remainder. -/
theorem ForItemsTailOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      left afterLeft)
    (rightParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      right afterRight) : afterLeft = afterRight := by
  have itemOutcomes := forItemDeterministicOutcomeSpec expressionOutcomes
    typeExprDeterministicOutcomeSpec
  induction leftParsed generalizing right afterRight with
  | done leftCommaAbsent =>
      cases rightParsed with
      | done => rfl
      | next rightCommaSpan rightComma rightStopAbsent rightItem
            rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_exact leftCommaAbsent rightComma)
  | next leftCommaSpan leftComma leftStopAbsent leftItem leftProgress leftTail
        inductionHypothesis =>
      cases rightParsed with
      | done rightCommaAbsent =>
          exact False.elim
            (absent_conflicts_exact rightCommaAbsent leftComma)
      | next rightCommaSpan rightComma rightStopAbsent rightItem
            rightProgress rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          cases afterCommaEq
          have afterItemEq := itemOutcomes.successOutputUnique leftItem
            rightItem
          cases afterItemEq
          exact inductionHypothesis rightTail

/-- Exact tail rejection excludes ordinary tail success. -/
theorem ForItemsTailRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) {stop : Symbol} {input rejected : Remainder}
    (rejection : ForItemsTailRejects expressionOrdinary expressionRejects stop
      input rejected) :
    ¬ ∃ items output,
      ForItemsTailOrdinaryParses expressionOrdinary stop input items output := by
  have itemOutcomes := forItemDeterministicOutcomeSpec expressionOutcomes
    typeExprDeterministicOutcomeSpec
  induction rejection with
  | stopAfterComma commaSpan stopSpan commaParsed stopCurrent =>
      rintro ⟨items, output, successful⟩
      cases successful with
      | done commaAbsent =>
          exact absent_conflicts_exact commaAbsent commaParsed
      | next successfulCommaSpan successfulComma stopAbsent itemParsed
            progress tail =>
          have afterCommaEq := exactToken_output_unique commaParsed
            successfulComma
          cases afterCommaEq
          exact stopAbsent ⟨stopSpan, stopCurrent⟩
  | itemRejected commaSpan commaParsed stopAbsent itemRejected =>
      rintro ⟨items, output, successful⟩
      cases successful with
      | done commaAbsent =>
          exact absent_conflicts_exact commaAbsent commaParsed
      | next successfulCommaSpan successfulComma successfulStopAbsent
            itemParsed progress tail =>
          have afterCommaEq := exactToken_output_unique commaParsed
            successfulComma
          cases afterCommaEq
          exact itemOutcomes.successRejectDisjoint itemRejected
            ⟨_, _, itemParsed⟩
  | laterRejected commaSpan commaParsed stopAbsent itemParsed progress
        tailRejected inductionHypothesis =>
      rintro ⟨items, output, successful⟩
      cases successful with
      | done commaAbsent =>
          exact absent_conflicts_exact commaAbsent commaParsed
      | next successfulCommaSpan successfulComma successfulStopAbsent
            successfulItem successfulProgress successfulTail =>
          have afterCommaEq := exactToken_output_unique commaParsed
            successfulComma
          cases afterCommaEq
          have afterItemEq := itemOutcomes.successOutputUnique itemParsed
            successfulItem
          cases afterItemEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- Lift expression outcomes through a Core `for` item-list tail. -/
theorem forItemsTailDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol) :
    DeterministicOutcomeSpec
      (ForItemsTailOrdinaryParses expressionOrdinary stop)
      (ForItemsTailRejects expressionOrdinary expressionRejects stop) where
  successOutputUnique := ForItemsTailOrdinaryParses.output_unique
    expressionOutcomes stop
  successRejectDisjoint := ForItemsTailRejects.disjointOrdinary
    expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
