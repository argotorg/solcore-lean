import Solcore.Syntax.DeclarativeExactOutcomeSpec
import Solcore.Syntax.DeclarativeTransactionalFallbackOutcomeProperties

/-! Full functionality transport through prioritized transactional fallback. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Prioritized transactional fallback preserves exact successful values when
both alternatives have exact outcomes. -/
theorem TransactionalFallbackOrdinaryParses.value_unique {alpha : Type}
    {primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop}
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : ExactDeterministicOutcomeSpec primaryParses
      primaryRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec fallbackParses
      fallbackRejects)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | primary leftPrimary =>
      cases rightParsed with
      | primary rightPrimary =>
          exact primaryOutcomes.successValueUnique leftPrimary rightPrimary
      | fallback rightPrimaryRejects rightFallback =>
          exact False.elim
            (primaryOutcomes.successRejectDisjoint rightPrimaryRejects
              ⟨_, _, leftPrimary⟩)
  | fallback leftPrimaryRejects leftFallback =>
      cases rightParsed with
      | primary rightPrimary =>
          exact False.elim
            (primaryOutcomes.successRejectDisjoint leftPrimaryRejects
              ⟨_, _, rightPrimary⟩)
      | fallback rightPrimaryRejects rightFallback =>
          exact fallbackOutcomes.successValueUnique leftFallback rightFallback

/-- Prioritized transactional fallback fixes its successful value and final
remainder when both alternatives have exact outcomes. -/
theorem TransactionalFallbackOrdinaryParses.result_unique {alpha : Type}
    {primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop}
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : ExactDeterministicOutcomeSpec primaryParses
      primaryRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec fallbackParses
      fallbackRejects)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique primaryOutcomes fallbackOutcomes rightParsed,
    leftParsed.output_unique primaryOutcomes.toDeterministicOutcomeSpec
      fallbackOutcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- A double transactional rejection always has the unique original-input
endpoint. -/
theorem TransactionalFallbackRejects.output_unique
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    {input left right : Remainder}
    (leftRejects : TransactionalFallbackRejects primaryRejects fallbackRejects
      input left)
    (rightRejects : TransactionalFallbackRejects primaryRejects
      fallbackRejects input right) : left = right := by
  cases leftRejects
  cases rightRejects
  rfl

/-- Exact branch outcomes lift through prioritized transactional fallback. -/
theorem transactionalFallbackExactOutcomeSpec {alpha : Type}
    (primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop)
    (primaryRejects fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : ExactDeterministicOutcomeSpec primaryParses
      primaryRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec fallbackParses
      fallbackRejects) :
    ExactDeterministicOutcomeSpec
      (TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (TransactionalFallbackRejects primaryRejects fallbackRejects) where
  toDeterministicOutcomeSpec :=
    transactionalFallbackDeterministicOutcomeSpec primaryParses
      fallbackParses primaryRejects fallbackRejects
      primaryOutcomes.toDeterministicOutcomeSpec
      fallbackOutcomes.toDeterministicOutcomeSpec
  successValueUnique := fun leftParsed rightParsed =>
    leftParsed.value_unique primaryOutcomes fallbackOutcomes rightParsed
  rejectOutputUnique := TransactionalFallbackRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
