import Solcore.Syntax.DeclarativeImplDefaultMarkerExactnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.ImplHeadSoundnessProperties

/-! Complete executable ordinary outcomes for the optional `default` marker. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- Every optional-default success follows its exact prioritized grammar. -/
theorem implDefaultMarker_success_ordinaryOutcome_sound
    {input output : State} {marker : Option SourceSpan}
    (result : implDefaultMarker input = .ok marker output) :
    DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses
      input.declarativeRemainder marker output.declarativeRemainder :=
  implDefaultMarker_success_sound result

/-- The guarded optional-default parser cannot reject. -/
theorem implDefaultMarker_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : implDefaultMarker input = .reject failure rejected) :
    DeclarativeGrammar.OptionalImplDefaultMarkerRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold implDefaultMarker getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true .defaultKw .topItem present with
      ⟨marker, markerResult⟩
    simp [present, markerResult, pure] at result
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package optional-default success and impossible rejection. -/
theorem implDefaultMarker_ordinaryOutcome_sound :
    (∀ {input output : State} {marker : Option SourceSpan},
      implDefaultMarker input = .ok marker output →
        DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses
          input.declarativeRemainder marker output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      implDefaultMarker input = .reject failure rejected →
        DeclarativeGrammar.OptionalImplDefaultMarkerRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨implDefaultMarker_success_ordinaryOutcome_sound,
    implDefaultMarker_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic optional-default outcomes. -/
theorem implDefaultMarker_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses
      DeclarativeGrammar.OptionalImplDefaultMarkerRejects :=
  DeclarativeGrammar.optionalImplDefaultMarkerDeterministicOutcomeSpec

/-- Re-export exact optional-default values and rejection endpoints. -/
theorem implDefaultMarker_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses
      DeclarativeGrammar.OptionalImplDefaultMarkerRejects :=
  DeclarativeGrammar.optionalImplDefaultMarkerExactOutcomeSpec

/-- Two successful optional-default parses have the same marker and final
declarative remainder. -/
theorem implDefaultMarker_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : Option SourceSpan}
    (leftResult : implDefaultMarker input = .ok left leftOutput)
    (rightResult : implDefaultMarker input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses.result_unique
    (implDefaultMarker_success_ordinaryOutcome_sound leftResult)
    (implDefaultMarker_success_ordinaryOutcome_sound rightResult)

/-- Two impossible optional-default rejections have the same declarative
endpoint. -/
theorem implDefaultMarker_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implDefaultMarker input = .reject leftFailure leftOutput)
    (rightResult : implDefaultMarker input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalImplDefaultMarkerRejects.output_unique
    (implDefaultMarker_reject_ordinaryOutcome_sound leftResult)
    (implDefaultMarker_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ImplInternals
