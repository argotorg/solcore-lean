import Solcore.Syntax.DeclarativeCorePatternPublicOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternRecoveryExactnessProperties

/-! Exact values and nonconsuming rejection at the public pattern layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Core success values and exact recovery make public pattern values unique.
The raw Core rejection endpoint need not be unique because recovery rewinds. -/
theorem PatternLayerOrdinaryParses.value_unique
    {coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    (coreValueUnique : ∀ {input left right afterLeft afterRight},
      coreOrdinary input left afterLeft →
      coreOrdinary input right afterRight → left = right)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternLayerOrdinaryParses coreOrdinary coreRejects input
      left afterLeft)
    (rightParsed : PatternLayerOrdinaryParses coreOrdinary coreRejects input
      right afterRight) : left = right := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact coreValueUnique leftCore rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (coreOutcomes.successRejectDisjoint coreRejected
              ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (coreOutcomes.successRejectDisjoint coreRejected
              ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.value_unique rightRecovery

/-- Every ordinary public pattern rejection fixes its original-input endpoint. -/
theorem PatternLayerRejects.output_unique
    {coreRejects : Remainder → Remainder → Prop}
    {input left right : Remainder}
    (leftRejected : PatternLayerRejects coreRejects input left)
    (rightRejected : PatternLayerRejects coreRejects input right) :
    left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Deterministic Core outcomes with unique successful values lift through
the public pattern recovery boundary to fully exact outcomes. -/
theorem patternLayerExactOutcomeSpec
    {coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    (coreValueUnique : ∀ {input left right afterLeft afterRight},
      coreOrdinary input left afterLeft →
      coreOrdinary input right afterRight → left = right) :
    ExactDeterministicOutcomeSpec
      (PatternLayerOrdinaryParses coreOrdinary coreRejects)
      (PatternLayerRejects coreRejects) where
  toDeterministicOutcomeSpec := patternLayerDeterministicOutcomeSpec coreOutcomes
  successValueUnique := PatternLayerOrdinaryParses.value_unique coreOutcomes
    coreValueUnique
  rejectOutputUnique := PatternLayerRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
