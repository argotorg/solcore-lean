import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingExactnessProperties

/-! Exact success values for maximal postfix tails at one fixed base AST. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- At one fixed base, exact nested expressions fix the complete postfix AST
and remainder, including index delimiters, call arguments, and field spans. -/
theorem PostfixTailParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {base left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : PostfixTailParses nestedOrdinary input base left afterLeft)
    (rightParsed : PostfixTailParses nestedOrdinary input base right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | index openingSpan closingSpan openingToken indexParsed closingToken
            tail =>
          exact False.elim (leftAbsent.1 ⟨openingSpan, openingToken.1⟩)
      | call indexAbsent argumentsParsed tail =>
          exact False.elim (leftAbsent.2.1 argumentsParsed.opening_present)
      | field dotSpan indexAbsent callAbsent dotToken nameParsed tail =>
          exact False.elim (leftAbsent.2.2 ⟨dotSpan, dotToken.1⟩)
  | index leftOpeningSpan leftClosingSpan leftOpening leftIndex leftClosing
        leftTail ih =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent.1 ⟨leftOpeningSpan, leftOpening.1⟩)
      | index rightOpeningSpan rightClosingSpan rightOpening rightIndex
            rightClosing rightTail =>
          rcases leftOpening.result_unique rightOpening with
            ⟨openingEq, inputEq⟩
          subst openingEq
          subst inputEq
          rcases nestedOutcomes.successResultUnique leftIndex rightIndex with
            ⟨indexEq, inputEq⟩
          subst indexEq
          subst inputEq
          rcases leftClosing.result_unique rightClosing with
            ⟨closingEq, inputEq⟩
          subst closingEq
          subst inputEq
          exact ih rightTail
      | call rightIndexAbsent argumentsParsed tail =>
          exact False.elim (rightIndexAbsent ⟨leftOpeningSpan, leftOpening.1⟩)
      | field dotSpan rightIndexAbsent callAbsent dotToken nameParsed tail =>
          exact False.elim (rightIndexAbsent ⟨leftOpeningSpan, leftOpening.1⟩)
  | call leftIndexAbsent leftArguments leftTail ih =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent.2.1 leftArguments.opening_present)
      | index openingSpan closingSpan rightOpening indexParsed closingToken
            tail =>
          exact False.elim (leftIndexAbsent ⟨openingSpan, rightOpening.1⟩)
      | call rightIndexAbsent rightArguments rightTail =>
          rcases (noTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
              nestedOutcomes).successResultUnique leftArguments rightArguments
            with ⟨argumentsEq, inputEq⟩
          subst argumentsEq
          subst inputEq
          exact ih rightTail
      | field dotSpan rightIndexAbsent rightCallAbsent dotToken nameParsed
            tail =>
          exact False.elim (rightCallAbsent leftArguments.opening_present)
  | field leftDotSpan leftIndexAbsent leftCallAbsent leftDot leftName leftTail
        ih =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent.2.2 ⟨leftDotSpan, leftDot.1⟩)
      | index openingSpan closingSpan rightOpening indexParsed closingToken
            tail =>
          exact False.elim (leftIndexAbsent ⟨openingSpan, rightOpening.1⟩)
      | call rightIndexAbsent rightArguments tail =>
          exact False.elim (leftCallAbsent rightArguments.opening_present)
      | field rightDotSpan rightIndexAbsent rightCallAbsent rightDot rightName
            rightTail =>
          rcases leftDot.result_unique rightDot with ⟨dotEq, inputEq⟩
          subst dotEq
          subst inputEq
          rcases leftName.result_unique rightName with ⟨nameEq, inputEq⟩
          subst nameEq
          subst inputEq
          exact ih rightTail

/-- A maximal postfix tail at a fixed base has one complete expression AST. -/
theorem PostfixTailParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {base left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : PostfixTailParses nestedOrdinary input base left afterLeft)
    (rightParsed : PostfixTailParses nestedOrdinary input base right afterRight) :
    left = right :=
  (leftParsed.result_unique nestedOutcomes rightParsed).1

/-- Exact atoms and nested expressions fix a complete postfix expression and
its final remainder. -/
theorem ExpressionPostfixOrdinaryParses.result_unique
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : ExactDeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input left afterLeft)
    (rightParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input right afterRight) : left = right ∧ afterLeft = afterRight := by
  rcases leftParsed with ⟨leftBase, leftAfterAtom, leftAtom, leftTail⟩
  rcases rightParsed with ⟨rightBase, rightAfterAtom, rightAtom, rightTail⟩
  rcases atomOutcomes.successResultUnique leftAtom rightAtom with
    ⟨baseEq, inputEq⟩
  subst baseEq
  subst inputEq
  exact leftTail.result_unique nestedOutcomes rightTail

/-- A complete ordinary postfix success fixes its full AST value. -/
theorem ExpressionPostfixOrdinaryParses.value_unique
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : ExactDeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input left afterLeft)
    (rightParsed : ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary
      input right afterRight) : left = right :=
  (ExpressionPostfixOrdinaryParses.result_unique atomOutcomes nestedOutcomes
    leftParsed rightParsed).1

end Solcore.Syntax.DeclarativeGrammar
