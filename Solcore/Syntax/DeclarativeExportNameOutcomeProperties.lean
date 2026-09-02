import Solcore.Syntax.DeclarativeConstructorSelectionOutcomeProperties
import Solcore.Syntax.DeclarativeExportNameOutcomeGrammar
import Solcore.Syntax.DeclarativeSelectorNameOutcomeProperties

/-! Deterministic and exclusive broad ordinary outcomes for export names. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem present_conflicts_absent {input : Remainder}
    {kind : TokenKind}
    (present : ExportNameTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      kind) : False := by
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩

private theorem token_conflicts_absent {input : Remainder}
    {kind : TokenKind} {span : SourceSpan}
    (token : TokenAt input.tokens input.endIndex input.cursor {
      span
      value := kind
    })
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      kind) : False :=
  absent ⟨span, token⟩

private theorem operatorSelector_opening_present
    {input output : Remainder} {selector : Syntax.SelectorName}
    (parsed : OperatorSelectorParses input selector output) :
    ExportNameTokenPresentAt input (.symbol .leftParen) := by
  unfold OperatorSelectorParses at parsed
  rcases parsed with ⟨openingSpan, closingSpan, parts, closingIndex,
    tokensEq, endIndexEq, openingToken, partsParsed, partsNonempty,
    closingToken, cursorEq, selectorEq⟩
  exact ⟨openingSpan, openingToken⟩

private theorem constructorSelection_opening_present
    {input output : Remainder} {selection : Syntax.ConstructorSelection}
    (parsed : ConstructorSelectionOrdinaryParses input selection output) :
    ExportNameTokenPresentAt input (.symbol .leftParen) := by
  cases parsed with
  | all openingSpan markerSpan closingSpan openingToken markerToken
      closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | named namesParsed =>
      unfold ConstructorNamesParses NonemptyNoTrailingDelimitedListParses at namesParsed
      rcases namesParsed with ⟨openingSpan, first, afterFirst, rest,
        closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
        progress, tail, elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

private theorem optionalConstructorSelection_output_unique
    {input : Remainder}
    {left right : Option Syntax.ConstructorSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalConstructorSelectionParses input left afterLeft)
    (rightParsed : OptionalConstructorSelectionParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSelection =>
          exact False.elim (present_conflicts_absent
            (constructorSelection_opening_present rightSelection) leftAbsent)
  | present leftSelection =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (present_conflicts_absent
            (constructorSelection_opening_present leftSelection) rightAbsent)
      | present rightSelection =>
          exact constructorSelectionDeterministicOutcomeSpec
            |>.successOutputUnique leftSelection rightSelection

/-- Prioritized export-name success has one final remainder. -/
theorem ExportNameOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ExportName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportNameOrdinaryParses input left afterLeft)
    (rightParsed : ExportNameOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | wildcard leftSpan leftMarker =>
      cases rightParsed with
      | wildcard => rfl
      | operator rightStar rightOperator =>
          exact False.elim (token_conflicts_absent leftMarker rightStar)
      | identifier rightStar rightOpening rightName rightConstructors =>
          exact False.elim (token_conflicts_absent leftMarker rightStar)
  | operator leftStar leftOperator =>
      cases rightParsed with
      | wildcard rightSpan rightMarker =>
          exact False.elim (token_conflicts_absent rightMarker leftStar)
      | operator rightStar rightOperator =>
          exact OperatorSelectorParses.output_unique leftOperator
            rightOperator
      | identifier rightStar rightOpening rightName rightConstructors =>
          exact False.elim (present_conflicts_absent
            (operatorSelector_opening_present leftOperator) rightOpening)
  | identifier leftStar leftOpening leftName leftConstructors =>
      cases rightParsed with
      | wildcard rightSpan rightMarker =>
          exact False.elim (token_conflicts_absent rightMarker leftStar)
      | operator rightStar rightOperator =>
          exact False.elim (present_conflicts_absent
            (operatorSelector_opening_present rightOperator) leftOpening)
      | identifier rightStar rightOpening rightName rightConstructors =>
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          exact optionalConstructorSelection_output_unique leftConstructors
            rightConstructors

/-- Exact first-stage export-name rejection excludes ordinary success. -/
theorem ExportNameRejects.disjointOrdinary
    {input rejected : Remainder} (rejection : ExportNameRejects input rejected) :
    ¬ ∃ name output, ExportNameOrdinaryParses input name output := by
  rintro ⟨name, output, successful⟩
  cases rejection with
  | operatorRejected starAbsent openingPresent selectorRejected =>
      cases successful with
      | wildcard markerSpan markerToken =>
          exact token_conflicts_absent markerToken starAbsent
      | operator successfulStar operatorParsed =>
          exact selectorNameDeterministicOutcomeSpec.successRejectDisjoint
            selectorRejected ⟨_, _, .operator operatorParsed⟩
      | identifier successfulStar openingAbsent nameParsed constructorsParsed =>
          exact present_conflicts_absent openingPresent openingAbsent
  | identifierRejected starAbsent openingAbsent nameRejected =>
      cases successful with
      | wildcard markerSpan markerToken =>
          exact token_conflicts_absent markerToken starAbsent
      | operator successfulStar operatorParsed =>
          exact present_conflicts_absent
            (operatorSelector_opening_present operatorParsed) openingAbsent
      | identifier successfulStar successfulOpening nameParsed
          constructorsParsed =>
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, nameParsed⟩
  | constructorsRejected starAbsent openingAbsent rejectedName
      openingPresent selectionRejected =>
      cases successful with
      | wildcard markerSpan markerToken =>
          exact token_conflicts_absent markerToken starAbsent
      | operator successfulStar operatorParsed =>
          exact present_conflicts_absent
            (operatorSelector_opening_present operatorParsed) openingAbsent
      | identifier successfulStar successfulOpening successfulName
          successfulConstructors =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          cases successfulConstructors with
          | absent selectionAbsent =>
              exact present_conflicts_absent openingPresent selectionAbsent
          | present selectionParsed =>
              exact constructorSelectionDeterministicOutcomeSpec
                |>.successRejectDisjoint selectionRejected
                  ⟨_, _, selectionParsed⟩

/-- Export names have deterministic and exclusive broad ordinary outcomes. -/
theorem exportNameDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExportNameOrdinaryParses ExportNameRejects where
  successOutputUnique := ExportNameOrdinaryParses.output_unique
  successRejectDisjoint := ExportNameRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
