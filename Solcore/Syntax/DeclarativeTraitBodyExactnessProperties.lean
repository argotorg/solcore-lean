import Solcore.Syntax.DeclarativeTraitBodyOutcomeProperties
import Solcore.Syntax.DeclarativeTraitMethodExactnessProperties

/-! Exact values and rejection endpoints for prioritized trait bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem traitBody_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem traitBody_absent_conflicts_method_start
    {input : Remainder}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .functionKw))
    (present : TraitMethodStartAt input) : False := by
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

/-- A successful trait-method tail fixes its methods, closing span, and final
remainder. -/
theorem TraitMethodTailOrdinaryParses.result_unique
    {input : Remainder}
    {leftMethods rightMethods : List Syntax.TraitMethod}
    {leftClosingSpan rightClosingSpan : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodTailOrdinaryParses input leftMethods
      leftClosingSpan afterLeft)
    (rightParsed : TraitMethodTailOrdinaryParses input rightMethods
      rightClosingSpan afterRight) :
    leftMethods = rightMethods ∧ leftClosingSpan = rightClosingSpan ∧
      afterLeft = afterRight := by
  induction leftParsed generalizing rightMethods rightClosingSpan afterRight with
  | close leftClosingSpan leftClosing =>
      cases rightParsed with
      | close rightClosingSpan rightClosing =>
          rcases leftClosing.result_unique rightClosing with
            ⟨closingSpanEq, outputEq⟩
          exact ⟨rfl, closingSpanEq, outputEq⟩
      | next rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (traitBody_absent_conflicts_exact rightClosingAbsent leftClosing)
  | next leftClosingAbsent leftFunctionPresent leftMethod leftProgress
      leftTail inductionHypothesis =>
      cases rightParsed with
      | close rightClosingSpan rightClosing =>
          exact False.elim
            (traitBody_absent_conflicts_exact leftClosingAbsent rightClosing)
      | next rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          rcases traitMethodExactOutcomeSpec.successResultUnique leftMethod
              rightMethod with ⟨methodEq, afterMethodEq⟩
          subst methodEq
          subst afterMethodEq
          rcases inductionHypothesis rightTail with
            ⟨methodsEq, closingSpanEq, outputEq⟩
          subst methodsEq
          exact ⟨rfl, closingSpanEq, outputEq⟩

/-- Rejection of the prioritized method loop fixes its failing endpoint. -/
theorem TraitMethodTailRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TraitMethodTailRejects input left)
    (rightRejected : TraitMethodTailRejects input right) : left = right := by
  induction leftRejected generalizing right with
  | unexpected leftClosingAbsent leftFunctionAbsent =>
      cases rightRejected with
      | unexpected => rfl
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod =>
          exact False.elim
            (traitBody_absent_conflicts_method_start leftFunctionAbsent
              rightFunctionPresent)
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (traitBody_absent_conflicts_method_start leftFunctionAbsent
              rightFunctionPresent)
  | methodRejected leftClosingAbsent leftFunctionPresent leftMethod =>
      cases rightRejected with
      | unexpected rightClosingAbsent rightFunctionAbsent =>
          exact False.elim
            (traitBody_absent_conflicts_method_start rightFunctionAbsent
              leftFunctionPresent)
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod =>
          exact traitMethodExactOutcomeSpec.rejectOutputUnique leftMethod
            rightMethod
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          exact False.elim
            (traitMethodExactOutcomeSpec.successRejectDisjoint leftMethod
              ⟨_, _, rightMethod⟩)
  | laterRejected leftClosingAbsent leftFunctionPresent leftMethod
      leftProgress leftTail inductionHypothesis =>
      cases rightRejected with
      | unexpected rightClosingAbsent rightFunctionAbsent =>
          exact False.elim
            (traitBody_absent_conflicts_method_start rightFunctionAbsent
              leftFunctionPresent)
      | methodRejected rightClosingAbsent rightFunctionPresent rightMethod =>
          exact False.elim
            (traitMethodExactOutcomeSpec.successRejectDisjoint rightMethod
              ⟨_, _, leftMethod⟩)
      | laterRejected rightClosingAbsent rightFunctionPresent rightMethod
          rightProgress rightTail =>
          have afterMethodEq :=
            traitMethodExactOutcomeSpec.successOutputUnique leftMethod
              rightMethod
          subst afterMethodEq
          exact inductionHypothesis rightTail

/-- The single-value tail adapter fixes its closing span and method list. -/
theorem TraitMethodTailOrdinaryOutcomeParses.value_unique
    {input : Remainder}
    {left right : SourceSpan × List Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodTailOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : TraitMethodTailOrdinaryOutcomeParses input right
      afterRight) : left = right := by
  rcases TraitMethodTailOrdinaryParses.result_unique leftParsed rightParsed with
    ⟨methodsEq, closingSpanEq, outputEq⟩
  exact Prod.ext closingSpanEq methodsEq

/-- Prioritized trait-method tails have fully exact ordinary outcomes. -/
theorem traitMethodTailExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TraitMethodTailOrdinaryOutcomeParses
      TraitMethodTailRejects where
  toDeterministicOutcomeSpec := traitMethodTailDeterministicOutcomeSpec
  successValueUnique := TraitMethodTailOrdinaryOutcomeParses.value_unique
  rejectOutputUnique := TraitMethodTailRejects.output_unique

/-- A successful complete trait body fixes its span, methods, and remainder. -/
theorem TraitBodyOrdinaryParses.result_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftMethods rightMethods : List Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitBodyOrdinaryParses input leftSpan leftMethods afterLeft)
    (rightParsed : TraitBodyOrdinaryParses input rightSpan rightMethods
      afterRight) :
    leftSpan = rightSpan ∧ leftMethods = rightMethods ∧
      afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpeningSpan leftClosingSpan leftOpening leftMethodsParsed =>
      cases rightParsed with
      | parsed rightOpeningSpan rightClosingSpan rightOpening
          rightMethodsParsed =>
          rcases leftOpening.result_unique rightOpening with
            ⟨openingSpanEq, afterOpeningEq⟩
          subst openingSpanEq
          subst afterOpeningEq
          rcases leftMethodsParsed.result_unique rightMethodsParsed with
            ⟨methodsEq, closingSpanEq, outputEq⟩
          subst methodsEq
          subst closingSpanEq
          exact ⟨rfl, rfl, outputEq⟩

/-- The single-value body adapter fixes its body span and method list. -/
theorem TraitBodyOrdinaryOutcomeParses.value_unique
    {input : Remainder}
    {left right : SourceSpan × List Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitBodyOrdinaryOutcomeParses input left afterLeft)
    (rightParsed : TraitBodyOrdinaryOutcomeParses input right afterRight) :
    left = right := by
  rcases TraitBodyOrdinaryParses.result_unique leftParsed rightParsed with
    ⟨spanEq, methodsEq, outputEq⟩
  exact Prod.ext spanEq methodsEq

/-- Complete trait-body rejection fixes its first failing endpoint. -/
theorem TraitBodyRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TraitBodyRejects input left)
    (rightRejected : TraitBodyRejects input right) : left = right := by
  cases leftRejected with
  | openingMissing leftOpeningAbsent =>
      cases rightRejected with
      | openingMissing => rfl
      | tailRejected rightOpeningSpan rightOpening rightTail =>
          exact False.elim
            (traitBody_absent_conflicts_exact leftOpeningAbsent rightOpening)
  | tailRejected leftOpeningSpan leftOpening leftTail =>
      cases rightRejected with
      | openingMissing rightOpeningAbsent =>
          exact False.elim
            (traitBody_absent_conflicts_exact rightOpeningAbsent leftOpening)
      | tailRejected rightOpeningSpan rightOpening rightTail =>
          have afterOpeningEq := leftOpening.output_unique rightOpening
          subst afterOpeningEq
          exact leftTail.output_unique rightTail

/-- Complete prioritized trait bodies have fully exact ordinary outcomes. -/
theorem traitBodyExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TraitBodyOrdinaryOutcomeParses
      TraitBodyRejects where
  toDeterministicOutcomeSpec := traitBodyDeterministicOutcomeSpec
  successValueUnique := TraitBodyOrdinaryOutcomeParses.value_unique
  rejectOutputUnique := TraitBodyRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
