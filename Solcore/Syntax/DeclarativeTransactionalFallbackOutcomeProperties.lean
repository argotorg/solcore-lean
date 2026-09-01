import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeTransactionalFallbackGrammar

/-! Deterministic laws for prioritized transactional fallback outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Transactional fallback has a unique output whenever both alternatives do. -/
theorem TransactionalFallbackOrdinaryParses.output_unique {alpha : Type}
    {primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop}
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes :
      DeterministicOutcomeSpec fallbackParses fallbackRejects)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | primary leftPrimary =>
      cases rightParsed with
      | primary rightPrimary =>
          exact primaryOutcomes.successOutputUnique leftPrimary rightPrimary
      | fallback rightPrimaryRejection rightFallback =>
          exact False.elim
            (primaryOutcomes.successRejectDisjoint rightPrimaryRejection
              ⟨_, _, leftPrimary⟩)
  | fallback leftPrimaryRejection leftFallback =>
      cases rightParsed with
      | primary rightPrimary =>
          exact False.elim
            (primaryOutcomes.successRejectDisjoint leftPrimaryRejection
              ⟨_, _, rightPrimary⟩)
      | fallback rightPrimaryRejection rightFallback =>
          exact fallbackOutcomes.successOutputUnique leftFallback
            rightFallback

/-- Rejection of both alternatives excludes every wrapper success. -/
theorem TransactionalFallbackRejects.disjointOrdinary {alpha : Type}
    {primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop}
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes :
      DeterministicOutcomeSpec fallbackParses fallbackRejects)
    {input rejected : Remainder}
    (rejection : TransactionalFallbackRejects primaryRejects fallbackRejects
      input rejected) :
    ¬ ∃ value output,
      TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses input value output := by
  rintro ⟨value, output, parsed⟩
  cases rejection with
  | both primaryRejection fallbackRejection =>
      cases parsed with
      | primary primaryParsed =>
          exact primaryOutcomes.successRejectDisjoint primaryRejection
            ⟨_, _, primaryParsed⟩
      | fallback otherPrimaryRejection fallbackParsed =>
          exact fallbackOutcomes.successRejectDisjoint fallbackRejection
            ⟨_, _, fallbackParsed⟩

/-- Build deterministic wrapper outcomes from deterministic branch outcomes. -/
theorem transactionalFallbackDeterministicOutcomeSpec {alpha : Type}
    (primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop)
    (primaryRejects fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes :
      DeterministicOutcomeSpec fallbackParses fallbackRejects) :
    DeterministicOutcomeSpec
      (TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (TransactionalFallbackRejects primaryRejects fallbackRejects) where
  successOutputUnique := fun leftParsed rightParsed =>
    leftParsed.output_unique primaryOutcomes fallbackOutcomes rightParsed
  successRejectDisjoint := fun rejection =>
    rejection.disjointOrdinary primaryOutcomes fallbackOutcomes

end Solcore.Syntax.DeclarativeGrammar
