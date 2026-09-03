import Solcore.Syntax.DeclarativeCoreForItemValueProperties
import Solcore.Syntax.DeclarativeCoreForItemsOutcomeProperties

/-! Exact forward-list values for Core `for` header item sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Comma priority and exact items fix the forward tail list and remainder. -/
theorem ForItemsTailOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      left afterLeft)
    (rightParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      right afterRight) : left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next rightSpan rightComma rightStop rightItem rightProgress rightTail =>
          exact False.elim (leftAbsent ⟨rightSpan, rightComma.1⟩)
  | next leftSpan leftComma leftStop leftItem leftProgress leftTail ih =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent ⟨leftSpan, leftComma.1⟩)
      | next rightSpan rightComma rightStop rightItem rightProgress rightTail =>
          have inputEq := leftComma.output_unique rightComma
          subst inputEq
          rcases ForItemOrdinaryParses.result_unique expressionOutcomes
              leftItem rightItem with ⟨itemEq, inputEq⟩
          subst itemEq
          subst inputEq
          rcases ih rightTail with ⟨tailEq, outputEq⟩
          subst tailEq
          exact ⟨rfl, outputEq⟩

/-- An ordinary for-item tail has one exact forward list of items. -/
theorem ForItemsTailOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      left afterLeft)
    (rightParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      right afterRight) : left = right :=
  (ForItemsTailOrdinaryParses.result_unique expressionOutcomes stop
    leftParsed rightParsed).1

/-- Stop priority and exact items fix a complete forward item list and
remainder without accepting a trailing comma. -/
theorem ForItemsOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsOrdinaryParses expressionOrdinary stop input left
      afterLeft)
    (rightParsed : ForItemsOrdinaryParses expressionOrdinary stop input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | empty leftSpan leftToken =>
      cases rightParsed with
      | empty => exact ⟨rfl, rfl⟩
      | nonempty rightAbsent rightFirst rightProgress rightTail =>
          exact False.elim (rightAbsent ⟨leftSpan, leftToken⟩)
  | nonempty leftAbsent leftFirst leftProgress leftTail =>
      cases rightParsed with
      | empty rightSpan rightToken =>
          exact False.elim (leftAbsent ⟨rightSpan, rightToken⟩)
      | nonempty rightAbsent rightFirst rightProgress rightTail =>
          rcases ForItemOrdinaryParses.result_unique expressionOutcomes
              leftFirst rightFirst with ⟨firstEq, inputEq⟩
          subst firstEq
          subst inputEq
          rcases ForItemsTailOrdinaryParses.result_unique expressionOutcomes
              stop leftTail rightTail with ⟨tailEq, outputEq⟩
          subst tailEq
          exact ⟨rfl, outputEq⟩

/-- An ordinary public for-item list fixes the ASTs in source order. -/
theorem ForItemsOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsOrdinaryParses expressionOrdinary stop input left
      afterLeft)
    (rightParsed : ForItemsOrdinaryParses expressionOrdinary stop input right
      afterRight) : left = right :=
  (ForItemsOrdinaryParses.result_unique expressionOutcomes stop leftParsed
    rightParsed).1

end Solcore.Syntax.DeclarativeGrammar
