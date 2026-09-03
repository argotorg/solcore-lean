import Solcore.Syntax.DeclarativeCorePatternArgumentsOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingExactnessProperties

/-! Exact required and transactionally optional constructor-pattern arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Required pattern arguments fix their nonempty carrier and covering span. -/
theorem ConstructorArgumentsOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorArgumentsOrdinaryParses nestedOrdinary input left
      afterLeft)
    (rightParsed : ConstructorArgumentsOrdinaryParses nestedOrdinary input right
      afterRight) : left = right := by
  have valueEq := NonemptyNoTrailingDelimitedListParses.value_unique
    nestedOutcomes leftParsed rightParsed
  cases left with
  | mk leftSpan leftElements =>
      cases leftElements with
      | mk leftHead leftTail =>
          cases right with
          | mk rightSpan rightElements =>
              cases rightElements with
              | mk rightHead rightTail =>
                  simp_all [NonemptyList.toList]

/-- Required pattern arguments fix their AST and final remainder. -/
theorem ConstructorArgumentsOrdinaryParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ConstructorArgumentsOrdinaryParses nestedOrdinary input left
      afterLeft)
    (rightParsed : ConstructorArgumentsOrdinaryParses nestedOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique nestedOutcomes rightParsed,
    leftParsed.output_unique nestedOutcomes.toDeterministicOutcomeSpec
      rightParsed⟩

/-- Required nonempty pattern arguments have exact ordinary outcomes. -/
theorem constructorArgumentsExactOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    ExactDeterministicOutcomeSpec
      (ConstructorArgumentsOrdinaryParses nestedOrdinary)
      (ConstructorArgumentsOrdinaryRejects nestedOrdinary nestedRejects) where
  toDeterministicOutcomeSpec := constructorArgumentsDeterministicOutcomeSpec
    nestedOutcomes.toDeterministicOutcomeSpec
  successValueUnique := ConstructorArgumentsOrdinaryParses.value_unique
    nestedOutcomes
  rejectOutputUnique :=
    (nonemptyNoTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
      nestedOutcomes).rejectOutputUnique

/-- Optional arguments fix either the exact nonempty value or rewound absence. -/
theorem OptionalConstructorArgumentsOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder}
    {left right : Option (NonemptyDelimitedList Syntax.Pattern)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalConstructorArgumentsOrdinaryParses nestedOrdinary
      nestedRejects input left afterLeft)
    (rightParsed : OptionalConstructorArgumentsOrdinaryParses nestedOrdinary
      nestedRejects input right afterRight) : left = right := by
  have argumentsOutcomes := constructorArgumentsExactOutcomeSpec nestedOutcomes
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent | rewound => rfl
      | present rightPresent =>
          exact False.elim (leftAbsent rightPresent.opening_token)
  | rewound leftSpan leftOpening leftRejected =>
      cases rightParsed with
      | absent | rewound => rfl
      | present rightPresent =>
          rcases leftRejected with ⟨rejected, rejection⟩
          exact False.elim
            (argumentsOutcomes.successRejectDisjoint rejection
              ⟨_, _, rightPresent⟩)
  | present leftPresent =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (rightAbsent leftPresent.opening_token)
      | rewound rightSpan rightOpening rightRejected =>
          rcases rightRejected with ⟨rejected, rejection⟩
          exact False.elim
            (argumentsOutcomes.successRejectDisjoint rejection
              ⟨_, _, leftPresent⟩)
      | present rightPresent =>
          exact congrArg some
            (argumentsOutcomes.successValueUnique leftPresent rightPresent)

/-- Optional pattern arguments fix their value and final remainder. -/
theorem OptionalConstructorArgumentsOrdinaryParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder}
    {left right : Option (NonemptyDelimitedList Syntax.Pattern)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalConstructorArgumentsOrdinaryParses nestedOrdinary
      nestedRejects input left afterLeft)
    (rightParsed : OptionalConstructorArgumentsOrdinaryParses nestedOrdinary
      nestedRejects input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique nestedOutcomes rightParsed,
    leftParsed.output_unique nestedOutcomes.toDeterministicOutcomeSpec
      rightParsed⟩

/-- Transactional optional pattern arguments have exact outcomes and cannot
ordinarily reject. -/
theorem optionalConstructorArgumentsExactOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    ExactDeterministicOutcomeSpec
      (OptionalConstructorArgumentsOrdinaryParses nestedOrdinary nestedRejects)
      OptionalConstructorArgumentsRejects where
  toDeterministicOutcomeSpec :=
    optionalConstructorArgumentsDeterministicOutcomeSpec
      nestedOutcomes.toDeterministicOutcomeSpec
  successValueUnique := OptionalConstructorArgumentsOrdinaryParses.value_unique
    nestedOutcomes
  rejectOutputUnique := by
    intro input left right leftRejected
    exact False.elim leftRejected

end Solcore.Syntax.DeclarativeGrammar
