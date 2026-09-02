import Solcore.Syntax.DeclarativeDeriveAttributeValidOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.DeriveTargetOrdinaryOutcomeSoundnessProperties

/-!
Exact ordinary-rejection reflection for the proof-visible normal
derive-attribute path.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_reject_tokenKindAbsentAt
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) := by
  by_cases present : isContextual input value = true
  · unfold isContextual State.peekKind? at present
    cases found : input.peek? with
    | none => simp [found] at present
    | some token =>
      simp only [found, Option.map_some] at present
      have parsed : contextual value context input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold contextual acceptToken
        simp only [found, present, ↓reduceIte]
      rw [parsed] at result
      contradiction
  · exact contextualAbsentAt_of_isContextual_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem contextual_reject_state_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.contextual value) context
    (·.isContextual value) result

namespace DeriveAttributeInternals

/-- Every normal-path derive-attribute rejection records its exact first
failing token or target-list stage and final rejection remainder. -/
theorem valid_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : valid input = .reject failure rejected) :
    DeclarativeGrammar.DeriveAttributeValidRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold valid at result
  cases hashResult : symbol .hash .topItem input with
  | invariant error => simp [bind, hashResult] at result
  | reject hashFailure hashRejected =>
      have rejectedEq := symbol_reject_state_eq .hash .topItem hashResult
      subst hashRejected
      simp only [bind, hashResult] at result
      cases result
      exact .hashMissing
        (symbol_reject_tokenKindAbsentAt .hash .topItem hashResult)
  | ok hash afterHash =>
      simp only [bind, hashResult] at result
      have hashParsed := symbol_success_exactTokenParses .hash .topItem
        hashResult
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp [openingResult] at result
      | reject openingFailure openingRejected =>
          have rejectedEq := symbol_reject_state_eq .leftBracket .topItem
            openingResult
          subst openingRejected
          simp only [openingResult] at result
          cases result
          exact .openingMissing hash.span hashParsed
            (symbol_reject_tokenKindAbsentAt .leftBracket .topItem
              openingResult)
      | ok opening afterOpening =>
          simp only [openingResult] at result
          have openingParsed := symbol_success_exactTokenParses .leftBracket
            .topItem openingResult
          cases markerResult : contextual .derive .topItem afterOpening with
          | invariant error => simp [markerResult] at result
          | reject markerFailure markerRejected =>
              have rejectedEq := contextual_reject_state_eq .derive .topItem
                markerResult
              subst markerRejected
              simp only [markerResult] at result
              cases result
              exact .markerMissing hash.span opening.span hashParsed
                openingParsed
                (contextual_reject_tokenKindAbsentAt .derive .topItem
                  markerResult)
          | ok marker afterMarker =>
              simp only [markerResult] at result
              have markerParsed := contextual_success_exactTokenParses
                .derive .topItem markerResult
              cases targetsResult : delimitedNoTrailing .leftParen
                  .rightParen true deriveTarget .topItem .topLevel
                  afterMarker with
              | invariant error => simp [targetsResult] at result
              | reject targetsFailure targetsRejected =>
                  simp only [targetsResult] at result
                  cases result
                  exact .targetsRejected hash.span opening.span marker.span
                    hashParsed openingParsed markerParsed
                    (delimitedNoTrailing_reject_sound .leftParen .rightParen
                      true deriveTarget DeclarativeGrammar.DeriveTargetParses
                      DeclarativeGrammar.DeriveTargetRejects .topItem
                      .topLevel deriveTarget_success_ordinaryOutcome_sound
                      deriveTarget_reject_ordinaryOutcome_sound targetsResult)
              | ok targets afterTargets =>
                  simp only [targetsResult] at result
                  have targetsParsed :=
                    delimitedNoTrailing_allowEmpty_success_sound .leftParen
                      .rightParen deriveTarget
                      DeclarativeGrammar.DeriveTargetParses .topItem .topLevel
                      deriveTarget_success_ordinaryOutcome_sound
                      deriveTarget_preservesTokenWindow targetsResult
                  cases closingResult : symbol .rightBracket .topItem
                      afterTargets with
                  | invariant error => simp [closingResult] at result
                  | reject closingFailure closingRejected =>
                      have rejectedEq := symbol_reject_state_eq .rightBracket
                        .topItem closingResult
                      subst closingRejected
                      simp only [closingResult] at result
                      cases result
                      exact .closingMissing hash.span opening.span marker.span
                        hashParsed openingParsed markerParsed targetsParsed
                        (symbol_reject_tokenKindAbsentAt .rightBracket .topItem
                          closingResult)
                  | ok closing afterClosing =>
                      by_cases empty : targets.elements.isEmpty
                      · simp only [closingResult, empty, if_true,
                          emitDiagnostic, modifyState, pure] at result
                        cases result
                      · simp only [closingResult, empty, Bool.false_eq_true,
                          if_false, pure] at result
                        cases result

end DeriveAttributeInternals
end Solcore.Syntax.Parser
