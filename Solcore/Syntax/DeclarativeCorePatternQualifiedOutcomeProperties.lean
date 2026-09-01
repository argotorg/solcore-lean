import Solcore.Syntax.DeclarativeCorePatternArgumentsOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternQualifiedOutcomeGrammar

/-! Deterministic ordinary outcomes for qualified Core patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Qualified binder-or-constructor success has one output remainder. -/
theorem QualifiedPatternOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects
      input left afterLeft)
    (rightParsed : QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects
      input right afterRight) : afterLeft = afterRight := by
  have nameOutcomes := patternQualifiedNameDeterministicOutcomeSpec
  have argumentsOutcomes :=
    optionalConstructorArgumentsDeterministicOutcomeSpec nestedOutcomes
  cases leftParsed with
  | binder leftPath leftArguments leftComponents leftChoice =>
      cases rightParsed with
      | binder rightPath rightArguments rightComponents rightChoice
      | constructor rightPath rightArguments rightComponents rightChoice =>
          have afterPathEq := nameOutcomes.successOutputUnique leftPath
            rightPath
          cases afterPathEq
          exact argumentsOutcomes.successOutputUnique leftArguments
            rightArguments
  | constructor leftPath leftArguments leftComponents leftChoice =>
      cases rightParsed with
      | binder rightPath rightArguments rightComponents rightChoice
      | constructor rightPath rightArguments rightComponents rightChoice =>
          have afterPathEq := nameOutcomes.successOutputUnique leftPath
            rightPath
          cases afterPathEq
          exact argumentsOutcomes.successOutputUnique leftArguments
            rightArguments

/-- Exact qualified-pattern rejection excludes every ordinary success. -/
theorem QualifiedPatternRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : QualifiedPatternRejects nestedOrdinary nestedRejects input
      rejected) :
    ¬ ∃ pattern output,
      QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects input pattern
        output := by
  rintro ⟨pattern, output, successful⟩
  have nameOutcomes := patternQualifiedNameDeterministicOutcomeSpec
  have argumentsOutcomes :=
    optionalConstructorArgumentsDeterministicOutcomeSpec nestedOutcomes
  cases rejection with
  | pathRejected rejectedPath =>
      cases successful with
      | binder parsedPath arguments components choice
      | constructor parsedPath arguments components choice =>
          exact nameOutcomes.successRejectDisjoint rejectedPath
            ⟨_, _, parsedPath⟩
  | argumentsRejected rejectedPath rejectedArguments =>
      cases successful with
      | binder parsedPath parsedArguments components choice
      | constructor parsedPath parsedArguments components choice =>
          have afterPathEq := nameOutcomes.successOutputUnique rejectedPath
            parsedPath
          cases afterPathEq
          exact argumentsOutcomes.successRejectDisjoint rejectedArguments
            ⟨_, _, parsedArguments⟩

/-- Lift deterministic nested-pattern outcomes through a qualified pattern. -/
theorem qualifiedPatternDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects)
      (QualifiedPatternRejects nestedOrdinary nestedRejects) where
  successOutputUnique :=
    QualifiedPatternOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    QualifiedPatternRejects.disjointOrdinary nestedOutcomes

end Solcore.Syntax.DeclarativeGrammar
