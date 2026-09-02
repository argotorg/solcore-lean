import Solcore.Syntax.DeclarativeDelimitedNoTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeDeriveAttributeValidOutcomeGrammar
import Solcore.Syntax.DeclarativeDeriveTargetOutcomeProperties

/-! Deterministic exact outcomes for the normal derive-attribute path. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem deriveTargetListDeterministicOutcomeSpec :
    DeterministicOutcomeSpec
      (NoTrailingDelimitedListParses .leftParen .rightParen
        DeriveTargetParses)
      (DelimitedListRejects .leftParen .rightParen true false
        DeriveTargetParses DeriveTargetRejects) :=
  noTrailingDelimitedListDeterministicOutcomeSpec .leftParen .rightParen
    deriveTargetDeterministicOutcomeSpec

/-- A successful normal derive attribute has one final remainder. -/
theorem DeriveAttributeParses.output_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeParses input left afterLeft)
    (rightParsed : DeriveAttributeParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftHashSpan, leftOpeningSpan, leftMarkerSpan, leftTargets,
      leftAfterTargets, leftClosingSpan, leftHash, leftOpening, leftMarker,
      leftTargetsParsed, leftClosing, leftOutput, leftShape⟩
  rcases rightParsed with
    ⟨rightHashSpan, rightOpeningSpan, rightMarkerSpan, rightTargets,
      rightAfterTargets, rightClosingSpan, rightHash, rightOpening,
      rightMarker, rightTargetsParsed, rightClosing, rightOutput,
      rightShape⟩
  have afterTargetsEq :=
    deriveTargetListDeterministicOutcomeSpec.successOutputUnique
      leftTargetsParsed rightTargetsParsed
  subst afterTargetsEq
  rw [leftOutput, rightOutput]

/-- Exact normal-path rejection excludes every normal derive-attribute
success. -/
theorem DeriveAttributeValidRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveAttributeValidRejects input rejected) :
    ¬ ∃ value output, DeriveAttributeParses input value output := by
  rintro ⟨value, output, successful⟩
  rcases successful with
    ⟨successfulHashSpan, successfulOpeningSpan, successfulMarkerSpan,
      targets, afterTargets, successfulClosingSpan, successfulHash,
      successfulOpening, successfulMarker, targetsParsed,
      successfulClosing, outputShape, attributeShape⟩
  cases rejection with
  | hashMissing hashAbsent =>
      exact absent_conflicts_token hashAbsent successfulHash
  | openingMissing hashSpan hashParsed openingAbsent =>
      rw [hashParsed.2] at openingAbsent
      exact absent_conflicts_token openingAbsent (by
        simpa only using successfulOpening)
  | markerMissing hashSpan openingSpan hashParsed openingParsed
      markerAbsent =>
      rw [hashParsed.2] at openingParsed
      rw [openingParsed.2] at markerAbsent
      exact absent_conflicts_token markerAbsent (by
        simpa only [Nat.add_assoc] using successfulMarker)
  | targetsRejected hashSpan openingSpan markerSpan hashParsed openingParsed
      markerParsed targetsRejected =>
      rw [hashParsed.2] at openingParsed
      rw [openingParsed.2] at markerParsed
      rw [markerParsed.2] at targetsRejected
      have normalizedRejection :
          DelimitedListRejects .leftParen .rightParen true false
            DeriveTargetParses DeriveTargetRejects
            { input with cursor := input.cursor + 3 } rejected := by
        simpa only [Nat.add_assoc] using targetsRejected
      exact deriveTargetListDeterministicOutcomeSpec.successRejectDisjoint
        normalizedRejection ⟨_, _, targetsParsed⟩
  | closingMissing hashSpan openingSpan markerSpan hashParsed openingParsed
      markerParsed rejectedTargets closingAbsent =>
      rw [hashParsed.2] at openingParsed
      rw [openingParsed.2] at markerParsed
      rw [markerParsed.2] at rejectedTargets
      have normalizedTargets := rejectedTargets
      simp only [Nat.add_assoc] at normalizedTargets
      have afterTargetsEq :=
        deriveTargetListDeterministicOutcomeSpec.successOutputUnique
          normalizedTargets targetsParsed
      subst afterTargetsEq
      exact absent_conflicts_token closingAbsent successfulClosing

/-- The normal derive-attribute path has deterministic and exclusive ordinary
outcomes. -/
theorem deriveAttributeValidDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveAttributeParses
      DeriveAttributeValidRejects where
  successOutputUnique := DeriveAttributeParses.output_unique
  successRejectDisjoint := DeriveAttributeValidRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
