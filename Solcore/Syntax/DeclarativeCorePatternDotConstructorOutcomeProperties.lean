import Solcore.Syntax.DeclarativeCorePatternArgumentsOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternDotConstructorOutcomeGrammar

/-! Deterministic ordinary outcomes for leading-dot Core constructor patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (left : ExactTokenParses kind input leftSpan leftOutput)
    (right : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [left.2, right.2]

private theorem tokenAbsent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A leading-dot constructor-pattern success has one output remainder. -/
theorem DotConstructorPatternOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : DotConstructorPatternOrdinaryParses nestedOrdinary
      nestedRejects input left afterLeft)
    (rightParsed : DotConstructorPatternOrdinaryParses nestedOrdinary
      nestedRejects input right afterRight) : afterLeft = afterRight := by
  have nameOutcomes := patternNameDeterministicOutcomeSpec
  have argumentsOutcomes :=
    optionalConstructorArgumentsDeterministicOutcomeSpec nestedOutcomes
  cases leftParsed with
  | parsed leftDotSpan leftDot leftName leftArguments =>
      cases rightParsed with
      | parsed rightDotSpan rightDot rightName rightArguments =>
          have afterDotEq := exactToken_output_unique leftDot rightDot
          cases afterDotEq
          have afterNameEq := nameOutcomes.successOutputUnique leftName
            rightName
          cases afterNameEq
          exact argumentsOutcomes.successOutputUnique leftArguments
            rightArguments

/-- Exact rejection at the first failing stage excludes ordinary success. -/
theorem DotConstructorPatternRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : DotConstructorPatternRejects nestedOrdinary nestedRejects
      input rejected) :
    ¬ ∃ pattern output,
      DotConstructorPatternOrdinaryParses nestedOrdinary nestedRejects input
        pattern output := by
  rintro ⟨pattern, output, successful⟩
  have nameOutcomes := patternNameDeterministicOutcomeSpec
  have argumentsOutcomes :=
    optionalConstructorArgumentsDeterministicOutcomeSpec nestedOutcomes
  cases rejection with
  | dotMissing dotAbsent =>
      cases successful with
      | parsed dotSpan dotParsed nameParsed argumentsParsed =>
          exact tokenAbsent_conflicts_exact dotAbsent dotParsed
  | nameRejected rejectedDotSpan rejectedDot rejectedName =>
      cases successful with
      | parsed successfulDotSpan successfulDot successfulName
            successfulArguments =>
          have afterDotEq := exactToken_output_unique rejectedDot successfulDot
          cases afterDotEq
          exact nameOutcomes.successRejectDisjoint rejectedName
            ⟨_, _, successfulName⟩
  | argumentsRejected rejectedDotSpan rejectedDot rejectedName
        rejectedArguments =>
      cases successful with
      | parsed successfulDotSpan successfulDot successfulName
            successfulArguments =>
          have afterDotEq := exactToken_output_unique rejectedDot successfulDot
          cases afterDotEq
          have afterNameEq := nameOutcomes.successOutputUnique rejectedName
            successfulName
          cases afterNameEq
          exact argumentsOutcomes.successRejectDisjoint rejectedArguments
            ⟨_, _, successfulArguments⟩

/-- Lift deterministic nested-pattern outcomes through a leading-dot
constructor pattern. -/
theorem dotConstructorPatternDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (DotConstructorPatternOrdinaryParses nestedOrdinary nestedRejects)
      (DotConstructorPatternRejects nestedOrdinary nestedRejects) where
  successOutputUnique :=
    DotConstructorPatternOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    DotConstructorPatternRejects.disjointOrdinary nestedOutcomes

end Solcore.Syntax.DeclarativeGrammar
