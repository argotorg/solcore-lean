import Solcore.Syntax.DeclarativeConstructorSelectionOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingExactnessProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact all-or-named export constructor selections and optional presence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem constructorNames_first_token
    {input output : Remainder} {names : NonemptyList Syntax.Identifier}
    {span : SourceSpan} (parsed : ConstructorNamesParses input names span output) :
    ∃ name : Syntax.Identifier,
      TokenAt input.tokens input.endIndex (input.cursor + 1)
        { span := name.span, value := .identifier name.value } := by
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, opening, firstParsed, progress, tail, valuesEq, spanEq⟩
  exact ⟨first, firstParsed.1⟩

/-- Named constructor selections fix their nonempty source-order names,
covering span, and final remainder. -/
theorem ConstructorNamesParses.result_unique
    {input : Remainder} {left right : NonemptyList Syntax.Identifier}
    {leftSpan rightSpan : SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorNamesParses input left leftSpan afterLeft)
    (rightParsed : ConstructorNamesParses input right rightSpan afterRight) :
    left = right ∧ leftSpan = rightSpan ∧ afterLeft = afterRight := by
  rcases (nonemptyNoTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    identifierExactOutcomeSpec).successResultUnique leftParsed rightParsed with
    ⟨valuesEq, outputsEq⟩
  cases left
  cases right
  simp_all [NonemptyList.toList]

/-- Every successful constructor selection begins with a left parenthesis. -/
theorem ConstructorSelectionOrdinaryParses.opening_token
    {input output : Remainder} {selection : Syntax.ConstructorSelection}
    (parsed : ConstructorSelectionOrdinaryParses input selection output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .symbol .leftParen } := by
  cases parsed with
  | all openingSpan markerSpan closingSpan opening marker closing =>
      exact ⟨openingSpan, opening⟩
  | named names =>
      rcases names with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, opening, firstParsed, progress, tail, valuesEq,
        spanEq⟩
      exact ⟨openingSpan, opening⟩

/-- All and named selections fix their complete located constructor AST. -/
theorem ConstructorSelectionOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.ConstructorSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorSelectionOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | all leftOpeningSpan leftMarkerSpan leftClosingSpan leftOpening leftMarker
      leftClosing =>
      cases rightParsed with
      | all rightOpeningSpan rightMarkerSpan rightClosingSpan rightOpening
          rightMarker rightClosing =>
          grind [TokenAt.token_unique]
      | named rightNames =>
          obtain ⟨name, nameToken⟩ := constructorNames_first_token rightNames
          cases leftMarker.token_unique nameToken
  | named leftNames =>
      cases rightParsed with
      | all rightOpeningSpan rightMarkerSpan rightClosingSpan rightOpening
          rightMarker rightClosing =>
          obtain ⟨name, nameToken⟩ := constructorNames_first_token leftNames
          cases rightMarker.token_unique nameToken
      | named rightNames =>
          rcases leftNames.result_unique rightNames with ⟨namesEq, spanEq, _⟩
          cases namesEq
          cases spanEq
          rfl

/-- Constructor-selection success fixes its complete AST and remainder. -/
theorem ConstructorSelectionOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.ConstructorSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ConstructorSelectionOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

private theorem constructorSelection_marker_at_input
    {input afterOpening afterMarker : Remainder}
    {openingSpan markerSpan : SourceSpan}
    (opening : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
    (marker : ExactTokenParses (.symbol .star) afterOpening markerSpan afterMarker) :
    TokenAt input.tokens input.endIndex (input.cursor + 1)
      { span := markerSpan, value := .symbol .star } := by
  simpa [opening.2] using marker.1

private theorem constructorSelection_absent_conflicts_token
    {tokens : Array Token} {endIndex cursor : Nat} {kind : TokenKind}
    {span : SourceSpan} (absent : TokenKindAbsentAt tokens endIndex cursor kind)
    (present : TokenAt tokens endIndex cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Constructor-selection rejection fixes its priority-selected endpoint. -/
theorem ConstructorSelectionRejects.output_unique
    {input left right : Remainder}
    (leftRejected : ConstructorSelectionRejects input left)
    (rightRejected : ConstructorSelectionRejects input right) : left = right := by
  have namesOutcomes := nonemptyNoTrailingDelimitedListExactOutcomeSpec
    .leftParen .rightParen identifierExactOutcomeSpec
  cases leftRejected <;> cases rightRejected <;>
    grind [constructorSelection_absent_conflicts_token,
      constructorSelection_marker_at_input, ExactTokenParses,
      namesOutcomes.rejectOutputUnique]

/-- Constructor selections have unconditional exact ordinary outcomes. -/
theorem constructorSelectionExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ConstructorSelectionOrdinaryParses
      ConstructorSelectionRejects where
  toDeterministicOutcomeSpec := constructorSelectionDeterministicOutcomeSpec
  successValueUnique := ConstructorSelectionOrdinaryParses.value_unique
  rejectOutputUnique := ConstructorSelectionRejects.output_unique

/-- Optional selection presence fixes its value and final remainder. -/
theorem OptionalConstructorSelectionParses.result_unique
    {input : Remainder} {left right : Option Syntax.ConstructorSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalConstructorSelectionParses input left afterLeft)
    (rightParsed : OptionalConstructorSelectionParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present rightSelection =>
          exact False.elim (leftAbsent
            (ConstructorSelectionOrdinaryParses.opening_token rightSelection))
  | present leftSelection =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (rightAbsent
            (ConstructorSelectionOrdinaryParses.opening_token leftSelection))
      | present rightSelection =>
          rcases ConstructorSelectionOrdinaryParses.result_unique leftSelection
            rightSelection with ⟨valueEq, afterEq⟩
          exact ⟨congrArg some valueEq, afterEq⟩

end Solcore.Syntax.DeclarativeGrammar
