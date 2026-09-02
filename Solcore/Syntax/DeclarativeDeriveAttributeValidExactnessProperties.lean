import Solcore.Syntax.DeclarativeDelimitedNoTrailingExactnessProperties
import Solcore.Syntax.DeclarativeDeriveAttributeValidOutcomeProperties
import Solcore.Syntax.DeclarativeDeriveTargetExactnessProperties

/-! Full functionality of the normal derive-attribute outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem deriveTargetListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (NoTrailingDelimitedListParses .leftParen .rightParen
        DeriveTargetParses)
      (DelimitedListRejects .leftParen .rightParen true false
        DeriveTargetParses DeriveTargetRejects) :=
  noTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    deriveTargetExactOutcomeSpec

/-- A successful normal derive attribute has one exact AST value. -/
theorem DeriveAttributeParses.value_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeParses input left afterLeft)
    (rightParsed : DeriveAttributeParses input right afterRight) :
    left = right := by
  rcases leftParsed with
    ⟨leftHashSpan, leftOpeningSpan, leftMarkerSpan, leftTargets,
      leftAfterTargets, leftClosingSpan, leftHash, leftOpening, leftMarker,
      leftTargetsParsed, leftClosing, leftOutput, leftShape⟩
  rcases rightParsed with
    ⟨rightHashSpan, rightOpeningSpan, rightMarkerSpan, rightTargets,
      rightAfterTargets, rightClosingSpan, rightHash, rightOpening,
      rightMarker, rightTargetsParsed, rightClosing, rightOutput,
      rightShape⟩
  have hashTokenEq := leftHash.token_unique rightHash
  have hashSpanEq : leftHashSpan = rightHashSpan :=
    congrArg (fun token : Token => token.span) hashTokenEq
  rcases deriveTargetListExactOutcomeSpec.successResultUnique
      leftTargetsParsed rightTargetsParsed with
    ⟨targetsEq, afterTargetsEq⟩
  subst targetsEq
  subst afterTargetsEq
  have closingTokenEq := leftClosing.token_unique rightClosing
  have closingSpanEq : leftClosingSpan = rightClosingSpan :=
    congrArg (fun token : Token => token.span) closingTokenEq
  subst hashSpanEq
  subst closingSpanEq
  exact leftShape.trans rightShape.symm

/-- A successful normal derive attribute fixes its AST and final remainder. -/
theorem DeriveAttributeParses.result_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeParses input left afterLeft)
    (rightParsed : DeriveAttributeParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A normal-path rejection has one exact first failing endpoint. -/
theorem DeriveAttributeValidRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveAttributeValidRejects input left)
    (rightRejects : DeriveAttributeValidRejects input right) : left = right :=
  by
    cases leftRejects with
    | hashMissing leftHashAbsent =>
        cases rightRejects with
        | hashMissing => rfl
        | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
            exact False.elim
              (absent_conflicts_token leftHashAbsent rightHash.1)
        | markerMissing rightHashSpan rightOpeningSpan rightHash rightOpening
              rightMarkerAbsent =>
            exact False.elim
              (absent_conflicts_token leftHashAbsent rightHash.1)
        | targetsRejected rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargetsRejects =>
            exact False.elim
              (absent_conflicts_token leftHashAbsent rightHash.1)
        | closingMissing rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargets
              rightClosingAbsent =>
            exact False.elim
              (absent_conflicts_token leftHashAbsent rightHash.1)
    | openingMissing leftHashSpan leftHash leftOpeningAbsent =>
        cases rightRejects with
        | hashMissing rightHashAbsent =>
            exact False.elim
              (absent_conflicts_token rightHashAbsent leftHash.1)
        | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
            exact leftHash.output_unique rightHash
        | markerMissing rightHashSpan rightOpeningSpan rightHash rightOpening
              rightMarkerAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token leftOpeningAbsent rightOpening.1)
        | targetsRejected rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargetsRejects =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token leftOpeningAbsent rightOpening.1)
        | closingMissing rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargets
              rightClosingAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token leftOpeningAbsent rightOpening.1)
    | markerMissing leftHashSpan leftOpeningSpan leftHash leftOpening
          leftMarkerAbsent =>
        cases rightRejects with
        | hashMissing rightHashAbsent =>
            exact False.elim
              (absent_conflicts_token rightHashAbsent leftHash.1)
        | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token rightOpeningAbsent leftOpening.1)
        | markerMissing rightHashSpan rightOpeningSpan rightHash rightOpening
              rightMarkerAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact leftOpening.output_unique rightOpening
        | targetsRejected rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargetsRejects =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            exact False.elim
              (absent_conflicts_token leftMarkerAbsent rightMarker.1)
        | closingMissing rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargets
              rightClosingAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            exact False.elim
              (absent_conflicts_token leftMarkerAbsent rightMarker.1)
    | targetsRejected leftHashSpan leftOpeningSpan leftMarkerSpan leftHash
          leftOpening leftMarker leftTargetsRejects =>
        cases rightRejects with
        | hashMissing rightHashAbsent =>
            exact False.elim
              (absent_conflicts_token rightHashAbsent leftHash.1)
        | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token rightOpeningAbsent leftOpening.1)
        | markerMissing rightHashSpan rightOpeningSpan rightHash rightOpening
              rightMarkerAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            exact False.elim
              (absent_conflicts_token rightMarkerAbsent leftMarker.1)
        | targetsRejected rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargetsRejects =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            have afterMarkerEq := leftMarker.output_unique rightMarker
            subst afterMarkerEq
            exact deriveTargetListExactOutcomeSpec.rejectOutputUnique
              leftTargetsRejects rightTargetsRejects
        | closingMissing rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargets
              rightClosingAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            have afterMarkerEq := leftMarker.output_unique rightMarker
            subst afterMarkerEq
            exact False.elim
              (deriveTargetListExactOutcomeSpec.successRejectDisjoint
                leftTargetsRejects ⟨_, _, rightTargets⟩)
    | closingMissing leftHashSpan leftOpeningSpan leftMarkerSpan leftHash
          leftOpening leftMarker leftTargets leftClosingAbsent =>
        cases rightRejects with
        | hashMissing rightHashAbsent =>
            exact False.elim
              (absent_conflicts_token rightHashAbsent leftHash.1)
        | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            exact False.elim
              (absent_conflicts_token rightOpeningAbsent leftOpening.1)
        | markerMissing rightHashSpan rightOpeningSpan rightHash rightOpening
              rightMarkerAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            exact False.elim
              (absent_conflicts_token rightMarkerAbsent leftMarker.1)
        | targetsRejected rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargetsRejects =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            have afterMarkerEq := leftMarker.output_unique rightMarker
            subst afterMarkerEq
            exact False.elim
              (deriveTargetListExactOutcomeSpec.successRejectDisjoint
                rightTargetsRejects ⟨_, _, leftTargets⟩)
        | closingMissing rightHashSpan rightOpeningSpan rightMarkerSpan
              rightHash rightOpening rightMarker rightTargets
              rightClosingAbsent =>
            have afterHashEq := leftHash.output_unique rightHash
            subst afterHashEq
            have afterOpeningEq := leftOpening.output_unique rightOpening
            subst afterOpeningEq
            have afterMarkerEq := leftMarker.output_unique rightMarker
            subst afterMarkerEq
            exact deriveTargetListExactOutcomeSpec.successOutputUnique
              leftTargets rightTargets

/-- The normal derive-attribute path has fully functional ordinary and
rejection outcomes. -/
theorem deriveAttributeValidExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveAttributeParses
      DeriveAttributeValidRejects where
  toDeterministicOutcomeSpec := deriveAttributeValidDeterministicOutcomeSpec
  successValueUnique := DeriveAttributeParses.value_unique
  rejectOutputUnique := DeriveAttributeValidRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
