import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeTypeAliasOutcomeGrammar

/-! Deterministic exact outcomes for optional type-alias parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem typeAliasParameters_opening_present
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

/-- The exact allow-empty, allow-trailing alias parameter list has deterministic
and exclusive identifier outcomes. -/
theorem typeAliasParametersDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TypeAliasParametersOrdinaryParses
      TypeAliasParametersRejects :=
  trailingDelimitedListDeterministicOutcomeSpec .leftParen .rightParen
    identifierDeterministicOutcomeSpec

/-- Optional type-alias parameter success has one final remainder. -/
theorem OptionalTypeAliasParametersOrdinaryParses.output_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.Identifier)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalTypeAliasParametersOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalTypeAliasParametersOrdinaryParses input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightParsed =>
          rcases typeAliasParameters_opening_present rightParsed with
            ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token leftAbsent openingPresent)
  | present leftParsed =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases typeAliasParameters_opening_present leftParsed with
            ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token rightAbsent openingPresent)
      | present rightParsed =>
          exact typeAliasParametersDeterministicOutcomeSpec
            |>.successOutputUnique leftParsed rightParsed

/-- Exact optional alias-parameter rejection excludes absent and present
success. -/
theorem OptionalTypeAliasParametersRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalTypeAliasParametersRejects input rejected) :
    ¬ ∃ parameters output,
      OptionalTypeAliasParametersOrdinaryParses input parameters output := by
  rintro ⟨parameters, output, successful⟩
  cases rejection with
  | present openingPresent parametersRejected =>
      cases successful with
      | absent openingAbsent =>
          rcases openingPresent with ⟨span, openingToken⟩
          exact absent_conflicts_token openingAbsent openingToken
      | present parametersParsed =>
          exact typeAliasParametersDeterministicOutcomeSpec
            |>.successRejectDisjoint parametersRejected
              ⟨_, _, parametersParsed⟩

/-- Optional type-alias parameters have deterministic and exclusive ordinary
outcomes. -/
theorem optionalTypeAliasParametersDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalTypeAliasParametersOrdinaryParses
      OptionalTypeAliasParametersRejects where
  successOutputUnique :=
    OptionalTypeAliasParametersOrdinaryParses.output_unique
  successRejectDisjoint :=
    OptionalTypeAliasParametersRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
