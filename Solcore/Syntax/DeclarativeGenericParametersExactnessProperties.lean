import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.DeclarativeGenericParametersOutcomeProperties

/-! Full value and rejection-endpoint functionality for generic parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem generic_absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem genericParameterListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (NonemptyTrailingDelimitedListParses .less .greater IdentifierParses)
      (DelimitedListRejects .less .greater false true IdentifierParses
        IdentifierRejects) :=
  nonemptyTrailingDelimitedListExactOutcomeSpec .less .greater
    identifierExactOutcomeSpec

/-- A required generic-parameter list fixes its nonempty AST value. -/
theorem GenericParametersParses.value_unique
    {input : Remainder} {left right : Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : GenericParametersParses input left afterLeft)
    (rightParsed : GenericParametersParses input right afterRight) :
    left = right := by
  have encodedEq := genericParameterListExactOutcomeSpec.successValueUnique
    leftParsed rightParsed
  cases left with
  | mk leftSpan leftElements =>
      cases leftElements with
      | mk leftHead leftTail =>
          cases right with
          | mk rightSpan rightElements =>
              cases rightElements with
              | mk rightHead rightTail =>
                  simp [Syntax.NonemptyList.toList] at encodedEq
                  simp_all

/-- A required generic-parameter list fixes its value and final remainder. -/
theorem GenericParametersParses.result_unique
    {input : Remainder} {left right : Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : GenericParametersParses input left afterLeft)
    (rightParsed : GenericParametersParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A required generic-parameter rejection has one failing endpoint. -/
theorem GenericParametersRejects.output_unique
    {input left right : Remainder}
    (leftRejected : GenericParametersRejects input left)
    (rightRejected : GenericParametersRejects input right) : left = right :=
  genericParameterListExactOutcomeSpec.rejectOutputUnique leftRejected
    rightRejected

/-- Required generic parameters have fully exact ordinary outcomes. -/
theorem genericParametersExactOutcomeSpec :
    ExactDeterministicOutcomeSpec GenericParametersParses
      GenericParametersRejects where
  toDeterministicOutcomeSpec := genericParametersDeterministicOutcomeSpec
  successValueUnique := GenericParametersParses.value_unique
  rejectOutputUnique := GenericParametersRejects.output_unique

private theorem genericParameters_opening_present
    {input output : Remainder} {parameters : Syntax.GenericParameters}
    (parsed : GenericParametersParses input parameters output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .less } := by
  unfold GenericParametersParses at parsed
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨openingSpan, openingToken⟩

/-- Optional generic parameters fix their absent or present AST value. -/
theorem OptionalGenericParametersParses.value_unique
    {input : Remainder} {left right : Option Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalGenericParametersParses input left afterLeft)
    (rightParsed : OptionalGenericParametersParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightParameters =>
          rcases genericParameters_opening_present rightParameters with
            ⟨span, openingToken⟩
          exact False.elim
            (generic_absent_conflicts_token leftAbsent openingToken)
  | present leftParameters =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases genericParameters_opening_present leftParameters with
            ⟨span, openingToken⟩
          exact False.elim
            (generic_absent_conflicts_token rightAbsent openingToken)
      | present rightParameters =>
          rw [leftParameters.value_unique rightParameters]

/-- Optional generic parameters fix their value and final remainder. -/
theorem OptionalGenericParametersParses.result_unique
    {input : Remainder} {left right : Option Syntax.GenericParameters}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalGenericParametersParses input left afterLeft)
    (rightParsed : OptionalGenericParametersParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A committed optional-generic rejection has one failing endpoint. -/
theorem OptionalGenericParametersRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalGenericParametersRejects input left)
    (rightRejected : OptionalGenericParametersRejects input right) :
    left = right := by
  cases leftRejected with
  | present _ leftParameters =>
      cases rightRejected with
      | present _ rightParameters =>
          exact leftParameters.output_unique rightParameters

/-- Optional generic parameters have fully exact ordinary outcomes. -/
theorem optionalGenericParametersExactOutcomeSpec :
    ExactDeterministicOutcomeSpec OptionalGenericParametersParses
      OptionalGenericParametersRejects where
  toDeterministicOutcomeSpec :=
    optionalGenericParametersDeterministicOutcomeSpec
  successValueUnique := OptionalGenericParametersParses.value_unique
  rejectOutputUnique := OptionalGenericParametersRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
