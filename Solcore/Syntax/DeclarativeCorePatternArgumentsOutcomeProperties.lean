import Solcore.Syntax.DeclarativeCorePatternArgumentsOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedFallbackProperties

/-! Deterministic ordinary outcomes for constructor-pattern arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Required constructor arguments expose their exact opening token. -/
theorem ConstructorArgumentsOrdinaryParses.opening_token
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {input output : Remainder}
    {arguments : NonemptyDelimitedList Syntax.Pattern}
    (parsed : ConstructorArgumentsOrdinaryParses nestedOrdinary input
      arguments output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol .leftParen
    } := by
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact ⟨openingSpan, openingToken⟩

/-- Required constructor-argument success has a unique output. -/
theorem ConstructorArgumentsOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorArgumentsOrdinaryParses nestedOrdinary input left
      afterLeft)
    (rightParsed : ConstructorArgumentsOrdinaryParses nestedOrdinary input
      right afterRight) : afterLeft = afterRight := by
  change NonemptyNoTrailingDelimitedListParses .leftParen .rightParen
      nestedOrdinary input {
        span := left.span
        elements := left.elements.toList
      } afterLeft at leftParsed
  change NonemptyNoTrailingDelimitedListParses .leftParen .rightParen
      nestedOrdinary input {
        span := right.span
        elements := right.elements.toList
      } afterRight at rightParsed
  exact NonemptyNoTrailingDelimitedListParses.output_unique
    (opening := .leftParen) (closing := .rightParen)
    (elementParses := nestedOrdinary) nestedOutcomes.successOutputUnique
      leftParsed rightParsed

/-- Exact required-argument rejection excludes ordinary success. -/
theorem ConstructorArgumentsOrdinaryRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : ConstructorArgumentsOrdinaryRejects nestedOrdinary nestedRejects
      input rejected) :
    ¬ ∃ arguments output,
      ConstructorArgumentsOrdinaryParses nestedOrdinary input arguments
        output := by
  rintro ⟨arguments, output, parsed⟩
  exact DelimitedListRejects.disjointNonemptyNoTrailing nestedOutcomes
    (fun parsed => parsed) rejection ⟨_, _, parsed⟩

/-- Lift deterministic nested pattern outcomes through required arguments. -/
theorem constructorArgumentsDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (ConstructorArgumentsOrdinaryParses nestedOrdinary)
      (ConstructorArgumentsOrdinaryRejects nestedOrdinary nestedRejects) where
  successOutputUnique :=
    ConstructorArgumentsOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    ConstructorArgumentsOrdinaryRejects.disjointOrdinary nestedOutcomes

/-- Transactional optional constructor arguments have functional output. -/
theorem OptionalConstructorArgumentsOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder}
    {left right : Option (NonemptyDelimitedList Syntax.Pattern)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalConstructorArgumentsOrdinaryParses nestedOrdinary
      nestedRejects input left afterLeft)
    (rightParsed : OptionalConstructorArgumentsOrdinaryParses nestedOrdinary
      nestedRejects input right afterRight) : afterLeft = afterRight := by
  have argumentsOutcomes :=
    constructorArgumentsDeterministicOutcomeSpec nestedOutcomes
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | rewound => rfl
      | present rightPresent =>
          rcases rightPresent.opening_token with ⟨span, token⟩
          exact False.elim (leftAbsent ⟨span, token⟩)
  | rewound leftOpeningSpan leftOpening leftRejected =>
      cases rightParsed with
      | absent => rfl
      | rewound => rfl
      | present rightPresent =>
          rcases leftRejected with ⟨rejected, rejection⟩
          exact False.elim
            (argumentsOutcomes.successRejectDisjoint rejection
              ⟨_, _, rightPresent⟩)
  | present leftPresent =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases leftPresent.opening_token with ⟨span, token⟩
          exact False.elim (rightAbsent ⟨span, token⟩)
      | rewound rightOpeningSpan rightOpening rightRejected =>
          rcases rightRejected with ⟨rejected, rejection⟩
          exact False.elim
            (argumentsOutcomes.successRejectDisjoint rejection
              ⟨_, _, leftPresent⟩)
      | present rightPresent =>
          exact argumentsOutcomes.successOutputUnique leftPresent rightPresent

/-- Lift deterministic nested outcomes through transactional optional
arguments. -/
theorem optionalConstructorArgumentsDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (OptionalConstructorArgumentsOrdinaryParses nestedOrdinary nestedRejects)
      OptionalConstructorArgumentsRejects where
  successOutputUnique :=
    OptionalConstructorArgumentsOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint := by
    intro input rejected rejection
    exact False.elim rejection

end Solcore.Syntax.DeclarativeGrammar
