import Solcore.Syntax.DeclarativeConstructorSelectionOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeDelimitedFallbackProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingSuccessProperties

/-! Deterministic and exclusive broad outcomes for constructor selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem tokenAt_kind_eq {tokens : Array Token} {endIndex index : Nat}
    {leftSpan rightSpan : SourceSpan} {leftKind rightKind : TokenKind}
    (left : TokenAt tokens endIndex index {
      span := leftSpan
      value := leftKind
    })
    (right : TokenAt tokens endIndex index {
      span := rightSpan
      value := rightKind
    }) :
    leftKind = rightKind := by
  have tokenEq : ({ span := leftSpan, value := leftKind } : Token) = {
      span := rightSpan
      value := rightKind
    } := Option.some.inj (left.2.symm.trans right.2)
  exact congrArg (fun token : Token => token.value) tokenEq

private theorem star_conflicts_identifier {tokens : Array Token}
    {endIndex index : Nat} {starSpan nameSpan : SourceSpan} {name : String}
    (starToken : TokenAt tokens endIndex index {
      span := starSpan
      value := .symbol .star
    })
    (nameToken : TokenAt tokens endIndex index {
      span := nameSpan
      value := .identifier name
    }) : False := by
  cases tokenAt_kind_eq starToken nameToken

private theorem identifier_output_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierParses input left afterLeft)
    (rightParsed : IdentifierParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftToken, leftTokens, leftEndIndex, leftCursor⟩
  rcases rightParsed with
    ⟨rightToken, rightTokens, rightEndIndex, rightCursor⟩
  rcases afterLeft with ⟨afterLeftTokens, afterLeftEndIndex,
    afterLeftCursor⟩
  rcases afterRight with ⟨afterRightTokens, afterRightEndIndex,
    afterRightCursor⟩
  have tokensEq : afterLeftTokens = afterRightTokens :=
    leftTokens.trans rightTokens.symm
  have endIndexEq : afterLeftEndIndex = afterRightEndIndex :=
    leftEndIndex.trans rightEndIndex.symm
  have cursorEq : afterLeftCursor = afterRightCursor :=
    leftCursor.trans rightCursor.symm
  cases tokensEq
  cases endIndexEq
  cases cursorEq
  rfl

private theorem identifier_outcome_spec :
    DeterministicOutcomeSpec IdentifierParses IdentifierRejects where
  successOutputUnique := identifier_output_unique
  successRejectDisjoint := IdentifierRejects.disjoint

private theorem ConstructorNamesParses.opening_token
    {input output : Remainder} {constructors : NonemptyList Syntax.Identifier}
    {span : SourceSpan}
    (parsed : ConstructorNamesParses input constructors span output) :
    ∃ openingSpan, TokenAt input.tokens input.endIndex input.cursor {
      span := openingSpan
      value := .symbol .leftParen
    } := by
  unfold ConstructorNamesParses at parsed
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨openingSpan, openingToken⟩

private theorem ConstructorNamesParses.first_identifier_token
    {input output : Remainder} {constructors : NonemptyList Syntax.Identifier}
    {span : SourceSpan}
    (parsed : ConstructorNamesParses input constructors span output) :
    ∃ nameSpan name, TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := nameSpan
      value := .identifier name
    } := by
  unfold ConstructorNamesParses at parsed
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨first.span, first.value, by simpa using firstParsed.1⟩

/-- Constructor-selection success has one final remainder. -/
theorem ConstructorSelectionOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ConstructorSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorSelectionOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | all leftOpeningSpan leftMarkerSpan leftClosingSpan leftOpening
      leftMarker leftClosing =>
      cases rightParsed with
      | all => rfl
      | named rightNames =>
          rcases rightNames.first_identifier_token with
            ⟨nameSpan, name, nameToken⟩
          exact False.elim (star_conflicts_identifier leftMarker nameToken)
  | named leftNames =>
      cases rightParsed with
      | all rightOpeningSpan rightMarkerSpan rightClosingSpan rightOpening
          rightMarker rightClosing =>
          rcases leftNames.first_identifier_token with
            ⟨nameSpan, name, nameToken⟩
          exact False.elim (star_conflicts_identifier rightMarker nameToken)
      | named rightNames =>
          unfold ConstructorNamesParses at leftNames rightNames
          exact NonemptyNoTrailingDelimitedListParses.output_unique
            (opening := .leftParen) (closing := .rightParen)
            (elementParses := IdentifierParses)
            identifier_output_unique leftNames rightNames

/-- Exact constructor-selection rejection excludes every ordinary success. -/
theorem ConstructorSelectionRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ConstructorSelectionRejects input rejected) :
    ¬ ∃ selection output,
      ConstructorSelectionOrdinaryParses input selection output := by
  rintro ⟨selection, output, successful⟩
  cases rejection with
  | openingMissing markerSpan markerToken openingAbsent =>
      cases successful with
      | all openingSpan successfulMarkerSpan closingSpan openingToken
          successfulMarker closingToken =>
          exact absent_conflicts_token openingAbsent openingToken
      | named namesParsed =>
          rcases namesParsed.opening_token with ⟨openingSpan, openingToken⟩
          exact absent_conflicts_token openingAbsent openingToken
  | closingMissing openingSpan markerSpan openingParsed markerParsed
      closingAbsent =>
      cases successful with
      | all successfulOpeningSpan successfulMarkerSpan successfulClosingSpan
          successfulOpening successfulMarker successfulClosing =>
          apply closingAbsent
          refine ⟨successfulClosingSpan, ?_⟩
          simpa [markerParsed.2, openingParsed.2, Nat.add_assoc] using
            successfulClosing
      | named namesParsed =>
          rcases namesParsed.first_identifier_token with
            ⟨nameSpan, name, nameToken⟩
          have markerAtInput : TokenAt input.tokens input.endIndex
              (input.cursor + 1) {
                span := markerSpan
                value := .symbol .star
              } := by
            simpa [openingParsed.2] using markerParsed.1
          exact star_conflicts_identifier markerAtInput nameToken
  | namedRejected markerAbsent namesRejected =>
      cases successful with
      | all openingSpan markerSpan closingSpan openingToken markerToken
          closingToken =>
          exact absent_conflicts_token markerAbsent markerToken
      | named namesParsed =>
          unfold ConstructorNamesParses at namesParsed
          exact namesRejected.disjointNonemptyNoTrailing
            identifier_outcome_spec (fun parsed => parsed)
            ⟨_, _, namesParsed⟩

/-- Constructor selections have deterministic and exclusive broad outcomes. -/
theorem constructorSelectionDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ConstructorSelectionOrdinaryParses
      ConstructorSelectionRejects where
  successOutputUnique := ConstructorSelectionOrdinaryParses.output_unique
  successRejectDisjoint := ConstructorSelectionRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
