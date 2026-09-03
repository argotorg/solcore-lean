import Solcore.Syntax.DeclarativeExactOutcomeSpec
import Solcore.Syntax.DeclarativeTransactionalFallbackOutcomeProperties

/-! Full functionality transport through prioritized transactional fallback. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Successful branch values and priority fix the wrapper value; neither
branch needs a unique raw rejection endpoint. -/
theorem TransactionalFallbackOrdinaryParses.value_unique_of_success {alpha : Type}
    {primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop}
    {primaryRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (primaryValues : ∀ {input left right afterLeft afterRight},
      primaryParses input left afterLeft →
      primaryParses input right afterRight → left = right)
    (fallbackValues : ∀ {input left right afterLeft afterRight},
      fallbackParses input left afterLeft →
      fallbackParses input right afterRight → left = right)
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
          exact primaryValues leftPrimary rightPrimary
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
          exact fallbackValues leftFallback rightFallback

/-- Prioritized transactional fallback preserves exact successful values when
both alternatives have exact outcomes. -/
theorem TransactionalFallbackOrdinaryParses.value_unique {alpha : Type}
    {primaryParses fallbackParses : Remainder → alpha → Remainder → Prop}
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
    left = right :=
  leftParsed.value_unique_of_success (fallbackParses := fallbackParses)
    primaryOutcomes.toDeterministicOutcomeSpec
    primaryOutcomes.successValueUnique fallbackOutcomes.successValueUnique
    rightParsed

/-- Deterministic branches with unique successful values fix the wrapper's
complete result without assumptions on their raw rejecting endpoints. -/
theorem TransactionalFallbackOrdinaryParses.result_unique_of_success {alpha : Type}
    {primaryParses fallbackParses : Remainder → alpha → Remainder → Prop}
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses fallbackRejects)
    (primaryValues : ∀ {input left right afterLeft afterRight},
      primaryParses input left afterLeft →
      primaryParses input right afterRight → left = right)
    (fallbackValues : ∀ {input left right afterLeft afterRight},
      fallbackParses input left afterLeft →
      fallbackParses input right afterRight → left = right)
    {input : Remainder} {left right : alpha}
    {afterLeft afterRight : Remainder}
    (leftParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input left afterLeft)
    (rightParsed : TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_success (fallbackParses := fallbackParses)
      primaryOutcomes primaryValues
      fallbackValues rightParsed,
    leftParsed.output_unique primaryOutcomes fallbackOutcomes rightParsed⟩

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

/-- Transactional rewind supplies exact rejecting endpoints independently of
the raw branch endpoints. Only deterministic branches and unique successful
values are needed to obtain the full wrapper contract. -/
theorem transactionalFallbackExactOutcomeSpecOfSuccess {alpha : Type}
    (primaryParses fallbackParses :
      Remainder → alpha → Remainder → Prop)
    (primaryRejects fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes : DeterministicOutcomeSpec fallbackParses fallbackRejects)
    (primaryValues : ∀ {input left right afterLeft afterRight},
      primaryParses input left afterLeft →
      primaryParses input right afterRight → left = right)
    (fallbackValues : ∀ {input left right afterLeft afterRight},
      fallbackParses input left afterLeft →
      fallbackParses input right afterRight → left = right) :
    ExactDeterministicOutcomeSpec
      (TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (TransactionalFallbackRejects primaryRejects fallbackRejects) where
  toDeterministicOutcomeSpec :=
    transactionalFallbackDeterministicOutcomeSpec primaryParses
      fallbackParses primaryRejects fallbackRejects
      primaryOutcomes fallbackOutcomes
  successValueUnique := fun leftParsed rightParsed =>
    leftParsed.value_unique_of_success (fallbackParses := fallbackParses)
      primaryOutcomes primaryValues
      fallbackValues rightParsed
  rejectOutputUnique := TransactionalFallbackRejects.output_unique

/-- Exact branch outcomes lift through prioritized transactional fallback. -/
theorem transactionalFallbackExactOutcomeSpec {alpha : Type}
    (primaryParses fallbackParses : Remainder → alpha → Remainder → Prop)
    (primaryRejects fallbackRejects : Remainder → Remainder → Prop)
    (primaryOutcomes : ExactDeterministicOutcomeSpec primaryParses primaryRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec fallbackParses fallbackRejects) :
    ExactDeterministicOutcomeSpec
      (TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses)
      (TransactionalFallbackRejects primaryRejects fallbackRejects) :=
  transactionalFallbackExactOutcomeSpecOfSuccess primaryParses fallbackParses
    primaryRejects fallbackRejects primaryOutcomes.toDeterministicOutcomeSpec
    fallbackOutcomes.toDeterministicOutcomeSpec primaryOutcomes.successValueUnique
    fallbackOutcomes.successValueUnique

end Solcore.Syntax.DeclarativeGrammar
