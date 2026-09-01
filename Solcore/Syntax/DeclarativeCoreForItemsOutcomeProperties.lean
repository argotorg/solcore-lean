import Solcore.Syntax.DeclarativeCoreForItemsTailOutcomeProperties

/-! Deterministic ordinary outcomes for public Core `for` item lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- An ordinary public Core `for` item list has one final remainder. -/
theorem ForItemsOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsOrdinaryParses expressionOrdinary stop input left
      afterLeft)
    (rightParsed : ForItemsOrdinaryParses expressionOrdinary stop input right
      afterRight) : afterLeft = afterRight := by
  have itemOutcomes := forItemDeterministicOutcomeSpec expressionOutcomes
    typeExprDeterministicOutcomeSpec
  have tailOutcomes := forItemsTailDeterministicOutcomeSpec
    expressionOutcomes stop
  cases leftParsed with
  | empty leftStopSpan leftStopCurrent =>
      cases rightParsed with
      | empty => rfl
      | nonempty rightStopAbsent rightFirst rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_token rightStopAbsent leftStopCurrent)
  | nonempty leftStopAbsent leftFirst leftProgress leftTail =>
      cases rightParsed with
      | empty rightStopSpan rightStopCurrent =>
          exact False.elim
            (absent_conflicts_token leftStopAbsent rightStopCurrent)
      | nonempty rightStopAbsent rightFirst rightProgress rightTail =>
          have afterFirstEq := itemOutcomes.successOutputUnique leftFirst
            rightFirst
          cases afterFirstEq
          exact tailOutcomes.successOutputUnique leftTail rightTail

/-- Exact public item-list rejection excludes ordinary success. -/
theorem ForItemsRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) {stop : Symbol} {input rejected : Remainder}
    (rejection : ForItemsRejects expressionOrdinary expressionRejects stop
      input rejected) :
    ¬ ∃ items output,
      ForItemsOrdinaryParses expressionOrdinary stop input items output := by
  have itemOutcomes := forItemDeterministicOutcomeSpec expressionOutcomes
    typeExprDeterministicOutcomeSpec
  have tailOutcomes := forItemsTailDeterministicOutcomeSpec
    expressionOutcomes stop
  rintro ⟨items, output, successful⟩
  cases rejection with
  | firstRejected stopAbsent firstRejected =>
      cases successful with
      | empty stopSpan stopCurrent =>
          exact absent_conflicts_token stopAbsent stopCurrent
      | nonempty successfulStopAbsent firstParsed progress tail =>
          exact itemOutcomes.successRejectDisjoint firstRejected
            ⟨_, _, firstParsed⟩
  | tailRejected stopAbsent firstParsed progress tailRejected =>
      cases successful with
      | empty stopSpan stopCurrent =>
          exact absent_conflicts_token stopAbsent stopCurrent
      | nonempty successfulStopAbsent successfulFirst successfulProgress
            successfulTail =>
          have afterFirstEq := itemOutcomes.successOutputUnique firstParsed
            successfulFirst
          cases afterFirstEq
          exact tailOutcomes.successRejectDisjoint tailRejected
            ⟨_, _, successfulTail⟩

/-- Lift expression outcomes through the public Core `for` item list. -/
theorem forItemsDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol) :
    DeterministicOutcomeSpec
      (ForItemsOrdinaryParses expressionOrdinary stop)
      (ForItemsRejects expressionOrdinary expressionRejects stop) where
  successOutputUnique := ForItemsOrdinaryParses.output_unique
    expressionOutcomes stop
  successRejectDisjoint := ForItemsRejects.disjointOrdinary
    expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
