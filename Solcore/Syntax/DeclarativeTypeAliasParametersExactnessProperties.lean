import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.DeclarativeTypeAliasParametersOutcomeProperties

/-! Exact values and rejection endpoints for optional type-alias parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exact_absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem exact_typeAliasParameters_opening_present
    {input output : Remainder} {parameters : DelimitedList Syntax.Identifier}
    (parsed : TypeAliasParametersOrdinaryParses input parameters output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftParen } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- The allow-empty, allow-trailing alias parameter list has one exact value,
final remainder, and rejecting endpoint. -/
theorem typeAliasParametersExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TypeAliasParametersOrdinaryParses
      TypeAliasParametersRejects :=
  trailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    identifierExactOutcomeSpec

/-- Optional alias parameters have one exact optional list value. -/
theorem OptionalTypeAliasParametersOrdinaryParses.value_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.Identifier)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalTypeAliasParametersOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalTypeAliasParametersOrdinaryParses input right
      afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftOpeningAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightParameters =>
          rcases exact_typeAliasParameters_opening_present rightParameters with
            ⟨span, openingToken⟩
          exact False.elim
            (exact_absent_conflicts_token leftOpeningAbsent openingToken)
  | present leftParameters =>
      cases rightParsed with
      | absent rightOpeningAbsent =>
          rcases exact_typeAliasParameters_opening_present leftParameters with
            ⟨span, openingToken⟩
          exact False.elim
            (exact_absent_conflicts_token rightOpeningAbsent openingToken)
      | present rightParameters =>
          have parametersEq :=
            typeAliasParametersExactOutcomeSpec.successValueUnique
              leftParameters rightParameters
          subst parametersEq
          rfl

/-- Optional alias parameters fix both their value and final remainder. -/
theorem OptionalTypeAliasParametersOrdinaryParses.result_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.Identifier)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalTypeAliasParametersOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalTypeAliasParametersOrdinaryParses input right
      afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- A committed optional-parameter rejection has one failing endpoint. -/
theorem OptionalTypeAliasParametersRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalTypeAliasParametersRejects input left)
    (rightRejected : OptionalTypeAliasParametersRejects input right) :
    left = right := by
  cases leftRejected with
  | present leftOpening leftParameters =>
      cases rightRejected with
      | present rightOpening rightParameters =>
          exact typeAliasParametersExactOutcomeSpec.rejectOutputUnique
            leftParameters rightParameters

/-- Optional type-alias parameters have exact ordinary outcomes. -/
theorem optionalTypeAliasParametersExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      OptionalTypeAliasParametersOrdinaryParses
      OptionalTypeAliasParametersRejects where
  toDeterministicOutcomeSpec :=
    optionalTypeAliasParametersDeterministicOutcomeSpec
  successValueUnique :=
    OptionalTypeAliasParametersOrdinaryParses.value_unique
  rejectOutputUnique :=
    OptionalTypeAliasParametersRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
