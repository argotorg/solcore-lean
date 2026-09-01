import Solcore.Syntax.DeclarativeCorePatternPublicOutcomeGrammar
import Solcore.Syntax.DeclarativeCorePatternRecoveryOutcomeProperties

/-! Deterministic outcomes at the public Core pattern recovery boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A pre-recovery boundary is also a stop of the recovery scan itself. -/
theorem PatternBoundaryStops.toRecoveryStop {input : Remainder}
    (stops : PatternBoundaryStops input) :
    PatternRecoveryStops input input := by
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | comma token => exact .comma token
  | rightParen token => exact .rightParen token
  | fatArrow token => exact .fatArrow token
  | pipe token => exact .pipe token
  | rightBrace token => exact .rightBrace token

/-- Preserved carrier and active-window evidence makes cursor-only rewind
exactly the original declarative input. -/
theorem PatternCoreRejectsWithPreservedWindow.exists_rewind_eq
    {coreRejects : Remainder → Remainder → Prop} {input : Remainder}
    (rejected : PatternCoreRejectsWithPreservedWindow coreRejects input) :
    ∃ failed, coreRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- Public ordinary pattern success has a functional output whenever the Core
outcome does. -/
theorem PatternLayerOrdinaryParses.output_unique
    {coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternLayerOrdinaryParses coreOrdinary coreRejects input
      left afterLeft)
    (rightParsed : PatternLayerOrdinaryParses coreOrdinary coreRejects input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact coreOutcomes.successOutputUnique leftCore rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim (coreOutcomes.successRejectDisjoint coreRejected
            ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim (coreOutcomes.successRejectDisjoint coreRejected
            ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Exact public rejection excludes both direct Core and recovered success. -/
theorem PatternLayerRejects.disjointOrdinary
    {coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input rejected : Remainder}
    (rejection : PatternLayerRejects coreRejects input rejected) :
    ¬ ∃ pattern output,
      PatternLayerOrdinaryParses coreOrdinary coreRejects input pattern
        output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | boundary coreRejected stops =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact coreOutcomes.successRejectDisjoint rejected
            ⟨_, _, coreParsed⟩
      | recovered otherRejected continues recovered => exact continues stops
  | recovery coreRejected continues recoveryRejected =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact coreOutcomes.successRejectDisjoint rejected
            ⟨_, _, coreParsed⟩
      | recovered otherRejected otherContinues recovered =>
          exact patternRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint recoveryRejected ⟨_, _, recovered⟩

/-- Every public pattern rejection leaves the rewound input unchanged. -/
theorem PatternLayerRejects.output_eq
    {coreRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : PatternLayerRejects coreRejects input rejected) :
    rejected = input := by
  cases rejection with
  | boundary => rfl
  | recovery coreRejected continues recoveryRejected =>
      exact recoveryRejected.output_eq

/-- Lift a deterministic Core-pattern outcome through rewind and recovery. -/
theorem patternLayerDeterministicOutcomeSpec
    {coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects) :
    DeterministicOutcomeSpec
      (PatternLayerOrdinaryParses coreOrdinary coreRejects)
      (PatternLayerRejects coreRejects) where
  successOutputUnique := PatternLayerOrdinaryParses.output_unique coreOutcomes
  successRejectDisjoint := PatternLayerRejects.disjointOrdinary coreOutcomes

end Solcore.Syntax.DeclarativeGrammar
