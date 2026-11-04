import Solcore.Syntax.Grammar.Patterns
import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Internal.DelimitedOutcomes

/-!
Properties of the declarative grammar of patterns: outcomes are deterministic, and
successful values and rejection points are unique. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternArgumentsOutcomeProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternDotConstructorOutcomeProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternQualifiedOutcomeProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternArgumentsExactnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternComptimeOutcomeProperties
/-! Deterministic ordinary outcomes for Core compile-time patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary compile-time-pattern success has one output remainder. -/
theorem ComptimePatternOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ComptimePatternOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ComptimePatternOrdinaryParses expressionOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftExpression =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightExpression =>
          have markerOutputEq := exactToken_output_unique leftMarker rightMarker
          cases markerOutputEq
          exact expressionOutcomes.successOutputUnique leftExpression
            rightExpression

/-- Exact compile-time-pattern rejection excludes ordinary success. -/
theorem ComptimePatternRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : ComptimePatternRejects expressionRejects input rejected) :
    ¬ ∃ pattern output,
      ComptimePatternOrdinaryParses expressionOrdinary input pattern output := by
  rintro ⟨pattern, output, parsed⟩
  cases rejection with
  | markerMissing markerAbsent =>
      cases parsed with
      | parsed markerSpan markerParsed expressionParsed =>
          exact tokenAbsent_conflicts_exact markerAbsent markerParsed
  | expressionRejected rejectedMarkerSpan rejectedMarker rejectedExpression =>
      cases parsed with
      | parsed parsedMarkerSpan parsedMarker parsedExpression =>
          have markerOutputEq := exactToken_output_unique rejectedMarker
            parsedMarker
          cases markerOutputEq
          exact expressionOutcomes.successRejectDisjoint rejectedExpression
            ⟨_, _, parsedExpression⟩

/-- Lift deterministic expression outcomes through a compile-time pattern. -/
theorem comptimePatternDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (ComptimePatternOrdinaryParses expressionOrdinary)
      (ComptimePatternRejects expressionRejects) where
  successOutputUnique :=
    ComptimePatternOrdinaryParses.output_unique
      expressionOutcomes
  successRejectDisjoint :=
    ComptimePatternRejects.disjointOrdinary expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternCoreOutcomeLeafProperties
/-! Deterministic ordinary outcomes of the three infallible selected leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Wildcard success has one output remainder. -/
theorem WildcardPatternOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : WildcardPatternOrdinaryParses input left afterLeft)
    (rightParsed : WildcardPatternOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed _ leftMarker =>
      cases rightParsed with
      | parsed _ rightMarker => rw [leftMarker.2, rightMarker.2]

/-- Wildcard rejection excludes wildcard success. -/
theorem WildcardPatternRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : WildcardPatternRejects input rejected) :
    ¬ ∃ pattern output, WildcardPatternOrdinaryParses input pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | absent markerAbsent =>
      cases successful with
      | parsed span markerParsed => exact markerAbsent ⟨span, markerParsed.1⟩

/-- Wildcard leaves have deterministic ordinary outcomes. -/
theorem wildcardPatternDeterministicOutcomeSpec :
    DeterministicOutcomeSpec WildcardPatternOrdinaryParses
      WildcardPatternRejects where
  successOutputUnique := WildcardPatternOrdinaryParses.output_unique
  successRejectDisjoint := WildcardPatternRejects.disjointOrdinary

/-- Literal-pattern success has one output remainder. -/
theorem LiteralPatternOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : LiteralPatternOrdinaryParses input left afterLeft)
    (rightParsed : LiteralPatternOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftLiteral =>
      cases rightParsed with
      | parsed rightLiteral =>
          exact CoreLiteralOrdinaryParses.output_unique leftLiteral
            rightLiteral

/-- Literal-pattern rejection excludes literal-pattern success. -/
theorem LiteralPatternRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : LiteralPatternRejects input rejected) :
    ¬ ∃ pattern output, LiteralPatternOrdinaryParses input pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | absent literalAbsent =>
      cases successful with
      | parsed parsed =>
          cases parsed with
          | decimal token => exact literalAbsent.1 ⟨_, _, token⟩
          | hexadecimal token => exact literalAbsent.2.1 ⟨_, _, token⟩
          | string token => exact literalAbsent.2.2 ⟨_, _, token⟩

/-- Literal-pattern leaves have deterministic ordinary outcomes. -/
theorem literalPatternDeterministicOutcomeSpec :
    DeterministicOutcomeSpec LiteralPatternOrdinaryParses
      LiteralPatternRejects where
  successOutputUnique := LiteralPatternOrdinaryParses.output_unique
  successRejectDisjoint := LiteralPatternRejects.disjointOrdinary

/-- Boolean-binder success has one output remainder. -/
theorem BooleanBinderPatternOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : BooleanBinderPatternOrdinaryParses input left afterLeft)
    (rightParsed : BooleanBinderPatternOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftName =>
      cases rightParsed with
      | parsed rightName => cases leftName <;> cases rightName <;> rfl

/-- Boolean-binder rejection excludes Boolean-binder success. -/
theorem BooleanBinderPatternRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : BooleanBinderPatternRejects input rejected) :
    ¬ ∃ pattern output,
      BooleanBinderPatternOrdinaryParses input pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | absent booleanAbsent =>
      cases successful with
      | parsed parsed =>
          cases parsed with
          | trueKeyword token => exact booleanAbsent.1 ⟨_, token⟩
          | falseKeyword token => exact booleanAbsent.2 ⟨_, token⟩

/-- Boolean-binder leaves have deterministic ordinary outcomes. -/
theorem booleanBinderPatternDeterministicOutcomeSpec :
    DeterministicOutcomeSpec BooleanBinderPatternOrdinaryParses
      BooleanBinderPatternRejects where
  successOutputUnique := BooleanBinderPatternOrdinaryParses.output_unique
  successRejectDisjoint := BooleanBinderPatternRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternCoreOutcomeSelectionProperties
/-! Unique selection of the seven ordered `patternCore` branches. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex cursor : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex cursor kind)
    (present : TokenAt tokens endIndex cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Ordered Core-pattern guard evidence selects a unique branch. -/
theorem PatternCoreBranchSelected.branch_unique
    {left right : PatternCoreBranch} {input : Remainder}
    (leftSelected : PatternCoreBranchSelected left input)
    (rightSelected : PatternCoreBranchSelected right input) : left = right := by
  cases leftSelected with
  | wildcard leftMarker =>
      cases rightSelected with
      | wildcard => rfl
      | literal rightAbsent _
      | boolean rightAbsent _ _
      | parenthesized rightAbsent _ _ _
      | dotConstructor rightAbsent _ _ _ _
      | comptime rightAbsent _ _ _ _ _
      | qualified rightAbsent _ _ _ _ _ _ =>
          exact False.elim (absent_conflicts_token rightAbsent leftMarker)
  | literal leftUnderscoreAbsent leftStarts =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal => rfl
      | boolean _ rightAbsent _
      | parenthesized _ rightAbsent _ _
      | dotConstructor _ rightAbsent _ _ _
      | comptime _ rightAbsent _ _ _ _
      | qualified _ rightAbsent _ _ _ _ _ =>
          exact False.elim (rightAbsent leftStarts)
  | boolean leftUnderscoreAbsent leftLiteralAbsent leftStarts =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal _ rightStarts => exact False.elim (leftLiteralAbsent rightStarts)
      | boolean => rfl
      | parenthesized _ _ rightAbsent _
      | dotConstructor _ _ rightAbsent _ _
      | comptime _ _ rightAbsent _ _ _
      | qualified _ _ rightAbsent _ _ _ _ =>
          exact False.elim (rightAbsent leftStarts)
  | parenthesized leftUnderscoreAbsent leftLiteralAbsent leftBooleanAbsent
        leftMarker =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal _ rightStarts => exact False.elim (leftLiteralAbsent rightStarts)
      | boolean _ _ rightStarts =>
          exact False.elim (leftBooleanAbsent rightStarts)
      | parenthesized => rfl
      | dotConstructor _ _ _ rightAbsent _
      | comptime _ _ _ rightAbsent _ _
      | qualified _ _ _ rightAbsent _ _ _ =>
          exact False.elim (absent_conflicts_token rightAbsent leftMarker)
  | dotConstructor leftUnderscoreAbsent leftLiteralAbsent leftBooleanAbsent
        leftParenAbsent leftMarker =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal _ rightStarts => exact False.elim (leftLiteralAbsent rightStarts)
      | boolean _ _ rightStarts =>
          exact False.elim (leftBooleanAbsent rightStarts)
      | parenthesized _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token leftParenAbsent rightMarker)
      | dotConstructor => rfl
      | comptime _ _ _ _ rightAbsent _
      | qualified _ _ _ _ rightAbsent _ _ =>
          exact False.elim (absent_conflicts_token rightAbsent leftMarker)
  | comptime leftUnderscoreAbsent leftLiteralAbsent leftBooleanAbsent
        leftParenAbsent leftDotAbsent leftMarker =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal _ rightStarts => exact False.elim (leftLiteralAbsent rightStarts)
      | boolean _ _ rightStarts =>
          exact False.elim (leftBooleanAbsent rightStarts)
      | parenthesized _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token leftParenAbsent rightMarker)
      | dotConstructor _ _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token leftDotAbsent rightMarker)
      | comptime => rfl
      | qualified _ _ _ _ _ rightAbsent _ =>
          exact False.elim (absent_conflicts_token rightAbsent leftMarker)
  | qualified leftUnderscoreAbsent leftLiteralAbsent leftBooleanAbsent
        leftParenAbsent leftDotAbsent leftComptimeAbsent leftMarker =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal _ rightStarts => exact False.elim (leftLiteralAbsent rightStarts)
      | boolean _ _ rightStarts =>
          exact False.elim (leftBooleanAbsent rightStarts)
      | parenthesized _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token leftParenAbsent rightMarker)
      | dotConstructor _ _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token leftDotAbsent rightMarker)
      | comptime _ _ _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token leftComptimeAbsent rightMarker)
      | qualified => rfl

/-- Every ordinary success retains its exact branch selection. -/
theorem PatternCoreOrdinaryParses.exists_branch_selected
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {input output : Remainder} {pattern : Syntax.Pattern}
    (parsed : PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary input pattern
        output) :
    ∃ branch, PatternCoreBranchSelected branch input := by
  cases parsed with
  | selected selection _ => exact ⟨_, selection⟩

/-- The exact final rejection excludes every selected branch. -/
theorem PatternCoreFinalRejects.disjointSelected
    {input rejected : Remainder}
    (rejection : PatternCoreFinalRejects input rejected) :
    ¬ ∃ branch, PatternCoreBranchSelected branch input := by
  rintro ⟨branch, selected⟩
  cases rejection with
  | final underscoreAbsent literalAbsent booleanAbsent leftParenAbsent
        dotAbsent comptimeAbsent identifierAbsent =>
      cases selected with
      | wildcard marker => exact absent_conflicts_token underscoreAbsent marker
      | literal _ starts => exact literalAbsent starts
      | boolean _ _ starts => exact booleanAbsent starts
      | parenthesized _ _ _ marker =>
          exact absent_conflicts_token leftParenAbsent marker
      | dotConstructor _ _ _ _ marker =>
          exact absent_conflicts_token dotAbsent marker
      | comptime _ _ _ _ _ marker =>
          exact absent_conflicts_token comptimeAbsent marker
      | qualified _ _ _ _ _ _ marker =>
          exact identifierAbsent ⟨_, _, marker⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternCoreOutcomeProperties
/-! Deterministic outcomes for the generic ordered `patternCore` dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One selected branch has functional output. -/
theorem PatternCoreBranchOrdinaryParses.output_unique
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop}
    (parenthesizedOutcomes : DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeterministicOutcomeSpec comptimeOrdinary
      comptimeRejects)
    (qualifiedOutcomes : DeterministicOutcomeSpec qualifiedOrdinary
      qualifiedRejects)
    {branch : PatternCoreBranch} {input : Remainder}
    {left right : Syntax.Pattern} {afterLeft afterRight : Remainder}
    (leftParsed : PatternCoreBranchOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary branch input
        left afterLeft)
    (rightParsed : PatternCoreBranchOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary branch input
        right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | wildcard left =>
      cases rightParsed with
      | wildcard right => exact left.output_unique right
  | literal left =>
      cases rightParsed with
      | literal right => exact left.output_unique right
  | boolean left =>
      cases rightParsed with
      | boolean right => exact left.output_unique right
  | parenthesized left =>
      cases rightParsed with
      | parenthesized right =>
          exact parenthesizedOutcomes.successOutputUnique left right
  | dotConstructor left =>
      cases rightParsed with
      | dotConstructor right =>
          exact dotConstructorOutcomes.successOutputUnique left right
  | comptime left =>
      cases rightParsed with
      | comptime right => exact comptimeOutcomes.successOutputUnique left right
  | qualified left =>
      cases rightParsed with
      | qualified right =>
          exact qualifiedOutcomes.successOutputUnique left right

/-- Ordered Core-pattern success has functional output. -/
theorem PatternCoreOrdinaryParses.output_unique
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop}
    (parenthesizedOutcomes : DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeterministicOutcomeSpec comptimeOrdinary
      comptimeRejects)
    (qualifiedOutcomes : DeterministicOutcomeSpec qualifiedOrdinary
      qualifiedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary input left
        afterLeft)
    (rightParsed : PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary input right
        afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | selected leftSelection leftBranch =>
      cases rightParsed with
      | selected rightSelection rightBranch =>
          have branchEq := leftSelection.branch_unique rightSelection
          subst branchEq
          exact leftBranch.output_unique parenthesizedOutcomes
            dotConstructorOutcomes comptimeOutcomes qualifiedOutcomes
              rightBranch

/-- A selected branch rejection excludes success of that branch. -/
theorem PatternCoreBranchRejects.disjointOrdinary
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop}
    (parenthesizedOutcomes : DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeterministicOutcomeSpec comptimeOrdinary
      comptimeRejects)
    (qualifiedOutcomes : DeterministicOutcomeSpec qualifiedOrdinary
      qualifiedRejects)
    {branch : PatternCoreBranch} {input rejected : Remainder}
    (rejection : PatternCoreBranchRejects parenthesizedRejects
      dotConstructorRejects comptimeRejects qualifiedRejects branch input
        rejected) :
    ¬ ∃ pattern output,
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary branch input
          pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | parenthesized rejected =>
      cases successful with
      | parenthesized parsed =>
          exact parenthesizedOutcomes.successRejectDisjoint rejected
            ⟨_, _, parsed⟩
  | dotConstructor rejected =>
      cases successful with
      | dotConstructor parsed =>
          exact dotConstructorOutcomes.successRejectDisjoint rejected
            ⟨_, _, parsed⟩
  | comptime rejected =>
      cases successful with
      | comptime parsed =>
          exact comptimeOutcomes.successRejectDisjoint rejected ⟨_, _, parsed⟩
  | qualified rejected =>
      cases successful with
      | qualified parsed =>
          exact qualifiedOutcomes.successRejectDisjoint rejected ⟨_, _, parsed⟩

/-- Exact selected/final rejection excludes every ordinary success. -/
theorem PatternCoreRejects.disjointOrdinary
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop}
    (parenthesizedOutcomes : DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeterministicOutcomeSpec comptimeOrdinary
      comptimeRejects)
    (qualifiedOutcomes : DeterministicOutcomeSpec qualifiedOrdinary
      qualifiedRejects)
    {input rejected : Remainder}
    (rejection : PatternCoreRejects parenthesizedRejects
      dotConstructorRejects comptimeRejects qualifiedRejects input rejected) :
    ¬ ∃ pattern output,
      PatternCoreOrdinaryParses parenthesizedOrdinary dotConstructorOrdinary
        comptimeOrdinary qualifiedOrdinary input pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | selected rejectedSelection branchRejected =>
      cases successful with
      | selected successfulSelection branchParsed =>
          have branchEq := rejectedSelection.branch_unique successfulSelection
          subst branchEq
          exact branchRejected.disjointOrdinary parenthesizedOutcomes
            dotConstructorOutcomes comptimeOutcomes qualifiedOutcomes
              ⟨_, _, branchParsed⟩
  | final finalRejected =>
      exact finalRejected.disjointSelected
        successful.exists_branch_selected

/-- Lift four deterministic recursive branches through the ordered core. -/
theorem patternCoreDeterministicOutcomeSpec
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop}
    (parenthesizedOutcomes : DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeterministicOutcomeSpec comptimeOrdinary
      comptimeRejects)
    (qualifiedOutcomes : DeterministicOutcomeSpec qualifiedOrdinary
      qualifiedRejects) :
    DeterministicOutcomeSpec
      (PatternCoreOrdinaryParses parenthesizedOrdinary dotConstructorOrdinary
        comptimeOrdinary qualifiedOrdinary)
      (PatternCoreRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects) where
  successOutputUnique := PatternCoreOrdinaryParses.output_unique
    parenthesizedOutcomes dotConstructorOutcomes comptimeOutcomes
      qualifiedOutcomes
  successRejectDisjoint := PatternCoreRejects.disjointOrdinary
    parenthesizedOutcomes dotConstructorOutcomes comptimeOutcomes
      qualifiedOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternLeafValueProperties
/-! Unique ordinary values for non-recursive Core pattern leaves and names. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem patternLiteral_value_unique {input : Remainder}
    {left right : Syntax.CoreLiteral} {afterLeft afterRight : Remainder}
    (leftParsed : CoreLiteralParses input left afterLeft)
    (rightParsed : CoreLiteralParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;> grind [TokenAt.token_unique]

private theorem patternBoolean_value_unique {input : Remainder}
    {left right : Syntax.Identifier} {afterLeft afterRight : Remainder}
    (leftParsed : BooleanIdentifierParses input left afterLeft)
    (rightParsed : BooleanIdentifierParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;> grind [TokenAt.token_unique]

/-- A wildcard token fixes the complete wildcard pattern and its span. -/
theorem WildcardPatternOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : WildcardPatternOrdinaryParses input left afterLeft)
    (rightParsed : WildcardPatternOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftToken =>
      cases rightParsed with
      | parsed rightSpan rightToken =>
          have spanEq := leftToken.span_unique rightToken
          subst spanEq
          rfl

/-- A literal token fixes the literal pattern's payload and source span. -/
theorem LiteralPatternOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : LiteralPatternOrdinaryParses input left afterLeft)
    (rightParsed : LiteralPatternOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftLiteral =>
      cases rightParsed with
      | parsed rightLiteral =>
          have literalEq := patternLiteral_value_unique leftLiteral rightLiteral
          subst literalEq
          rfl

/-- A Boolean keyword fixes the binder-shaped pattern's name and span. -/
theorem BooleanBinderPatternOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : BooleanBinderPatternOrdinaryParses input left afterLeft)
    (rightParsed : BooleanBinderPatternOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftName =>
      cases rightParsed with
      | parsed rightName =>
          have nameEq := patternBoolean_value_unique leftName rightName
          subst nameEq
          rfl

/-- Boolean-first pattern names fix their exact identifier value. -/
theorem PatternNameOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternNameOrdinaryParses input left afterLeft)
    (rightParsed : PatternNameOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | boolean leftBoolean =>
      cases rightParsed with
      | boolean rightBoolean =>
          exact patternBoolean_value_unique leftBoolean rightBoolean
      | identifier trueAbsent falseAbsent rightName =>
          cases leftBoolean with
          | trueKeyword token => exact False.elim (trueAbsent ⟨_, token⟩)
          | falseKeyword token => exact False.elim (falseAbsent ⟨_, token⟩)
  | identifier trueAbsent falseAbsent leftName =>
      cases rightParsed with
      | boolean rightBoolean =>
          cases rightBoolean with
          | trueKeyword token => exact False.elim (trueAbsent ⟨_, token⟩)
          | falseKeyword token => exact False.elim (falseAbsent ⟨_, token⟩)
      | identifier rightTrueAbsent rightFalseAbsent rightName =>
          exact identifierExactOutcomeSpec.successValueUnique leftName rightName

/-- Boolean-first pattern names fix their value and final remainder. -/
theorem PatternNameOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternNameOrdinaryParses input left afterLeft)
    (rightParsed : PatternNameOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨PatternNameOrdinaryParses.value_unique leftParsed rightParsed,
    patternNameDeterministicOutcomeSpec.successOutputUnique leftParsed
      rightParsed⟩

/-- Pattern names have exact ordinary values and nonconsuming rejections. -/
theorem patternNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PatternNameOrdinaryParses
      PatternNameRejects where
  toDeterministicOutcomeSpec := patternNameDeterministicOutcomeSpec
  successValueUnique := PatternNameOrdinaryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    cases leftRejected
    cases rightRejected
    rfl

/-- Qualified pattern names reuse the exact maximal dotted-name contract. -/
theorem patternQualifiedNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PatternQualifiedNameOrdinaryParses
      PatternQualifiedNameRejects :=
  typeQualifiedNameExactOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternCoreValueProperties
/-! Successful-value functionality of the ordered Core pattern dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Value functionality of four recursive branches suffices for the complete
ordered Core-pattern success relation; no raw rejection uniqueness is needed. -/
theorem PatternCoreOrdinaryParses.value_unique
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    (parenthesizedUnique : ∀ {input left right afterLeft afterRight},
      parenthesizedOrdinary input left afterLeft →
      parenthesizedOrdinary input right afterRight → left = right)
    (dotConstructorUnique : ∀ {input left right afterLeft afterRight},
      dotConstructorOrdinary input left afterLeft →
      dotConstructorOrdinary input right afterRight → left = right)
    (comptimeUnique : ∀ {input left right afterLeft afterRight},
      comptimeOrdinary input left afterLeft →
      comptimeOrdinary input right afterRight → left = right)
    (qualifiedUnique : ∀ {input left right afterLeft afterRight},
      qualifiedOrdinary input left afterLeft →
      qualifiedOrdinary input right afterRight → left = right)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary input left
      afterLeft)
    (rightParsed : PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | selected leftSelection leftBranch =>
      cases rightParsed with
      | selected rightSelection rightBranch =>
          have branchEq := leftSelection.branch_unique rightSelection
          subst branchEq
          cases leftBranch with
          | wildcard leftLeaf =>
              cases rightBranch with
              | wildcard rightLeaf =>
                  exact leftLeaf.value_unique rightLeaf
          | literal leftLeaf =>
              cases rightBranch with
              | literal rightLeaf =>
                  exact leftLeaf.value_unique rightLeaf
          | boolean leftLeaf =>
              cases rightBranch with
              | boolean rightLeaf =>
                  exact leftLeaf.value_unique rightLeaf
          | parenthesized leftLeaf =>
              cases rightBranch with
              | parenthesized rightLeaf =>
                  exact parenthesizedUnique leftLeaf rightLeaf
          | dotConstructor leftLeaf =>
              cases rightBranch with
              | dotConstructor rightLeaf =>
                  exact dotConstructorUnique leftLeaf rightLeaf
          | comptime leftLeaf =>
              cases rightBranch with
              | comptime rightLeaf => exact comptimeUnique leftLeaf rightLeaf
          | qualified leftLeaf =>
              cases rightBranch with
              | qualified rightLeaf => exact qualifiedUnique leftLeaf rightLeaf

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternConstructorValueProperties
/-! Unique values for constructor, qualified, and compile-time patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact nested arguments fix a leading-dot constructor's complete AST. -/
theorem DotConstructorPatternOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : DotConstructorPatternOrdinaryParses nestedOrdinary nestedRejects
      input left afterLeft)
    (rightParsed : DotConstructorPatternOrdinaryParses nestedOrdinary nestedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftDotSpan leftDot leftName leftArguments =>
      cases rightParsed with
      | parsed rightDotSpan rightDot rightName rightArguments =>
          rcases leftDot.result_unique rightDot with ⟨dotEq, afterDotEq⟩
          subst dotEq
          subst afterDotEq
          rcases patternNameExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          have argumentsEq := leftArguments.value_unique nestedOutcomes
            rightArguments
          subst argumentsEq
          rfl

/-- Exact nested arguments and the fixed name path select one binder or
constructor value, including its source-order qualifiers. -/
theorem QualifiedPatternOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects
      input left afterLeft)
    (rightParsed : QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | binder leftPath leftArguments leftComponents leftChoice
  | constructor leftPath leftArguments leftComponents leftChoice =>
      cases rightParsed with
      | binder rightPath rightArguments rightComponents rightChoice
      | constructor rightPath rightArguments rightComponents rightChoice =>
          rcases patternQualifiedNameExactOutcomeSpec.successResultUnique
              leftPath rightPath with ⟨pathEq, afterPathEq⟩
          subst pathEq
          subst afterPathEq
          have argumentsEq := leftArguments.value_unique nestedOutcomes
            rightArguments
          subst argumentsEq
          grind

/-- The contextual marker and exact expression value fix a comptime pattern. -/
theorem ComptimePatternOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ComptimePatternOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ComptimePatternOrdinaryParses expressionOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftExpression =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightExpression =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerEq, afterMarkerEq⟩
          subst markerEq
          subst afterMarkerEq
          have expressionEq := expressionOutcomes.successValueUnique
            leftExpression rightExpression
          subst expressionEq
          rfl

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternRecoveryOutcomeProperties
/-! Functionality and outcome exclusion for Core pattern recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- Every pattern recovery stop preserves its complete remainder. -/
theorem PatternRecoveryStops.output_eq {input stopped : Remainder}
    (stops : PatternRecoveryStops input stopped) : stopped = input := by
  cases stops <;> rfl

/-- A pattern recovery scan has functional output from one remainder. -/
theorem PatternRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.Pattern} {afterLeft afterRight : Remainder},
      PatternRecoveryScanParses first leftLast input left afterLeft →
      PatternRecoveryScanParses first rightLast input right afterRight →
      afterLeft = afterRight := by
  intro first leftLast rightLast input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- Complete ordinary pattern recovery has functional output. -/
theorem PatternRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternRecoveryParses input left afterLeft)
    (rightParsed : PatternRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every complete pattern recovery rejection is non-consuming. -/
theorem PatternRecoveryRejects.output_eq {input rejected : Remainder}
    (rejection : PatternRecoveryRejects input rejected) : rejected = input := by
  cases rejection <;> rfl

/-- A present first token excludes complete pattern recovery rejection. -/
theorem PatternRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : PatternRecoveryRejects input rejected) :
    ¬ ∃ pattern output, PatternRecoveryParses input pattern output := by
  rintro ⟨pattern, output, parsed⟩
  cases parsed with
  | recovered current scan =>
      cases rejection with
      | windowEnd atEnd =>
          exact False.elim (Nat.not_lt_of_ge atEnd current.1)
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- Deterministic ordinary outcome contract for complete pattern recovery. -/
theorem patternRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PatternRecoveryParses PatternRecoveryRejects where
  successOutputUnique := PatternRecoveryParses.output_unique
  successRejectDisjoint := PatternRecoveryRejects.disjointParses

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternRecoveryExactnessProperties
/-! Exact error values and endpoints for ordinary Core pattern recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- With fixed first and last retained spans, recovery fixes its error pattern
and final remainder. -/
theorem PatternRecoveryScanParses.result_unique :
    ∀ {first last : SourceSpan} {input : Remainder}
      {left right : Syntax.Pattern} {afterLeft afterRight : Remainder},
      PatternRecoveryScanParses first last input left afterLeft →
      PatternRecoveryScanParses first last input right afterRight →
      left = right ∧ afterLeft = afterRight := by
  intro first last input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => exact ⟨rfl, rfl⟩
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- With fixed retained endpoint spans, recovery fixes its complete error AST. -/
theorem PatternRecoveryScanParses.value_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.Pattern} {afterLeft afterRight : Remainder}
    (leftParsed : PatternRecoveryScanParses first last input left afterLeft)
    (rightParsed : PatternRecoveryScanParses first last input right afterRight) :
    left = right :=
  (leftParsed.result_unique rightParsed).1

/-- The mandatory first token fixes both scan spans and the recovery result. -/
theorem PatternRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternRecoveryParses input left afterLeft)
    (rightParsed : PatternRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightCurrent rightScan =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact leftScan.result_unique rightScan

/-- Complete pattern recovery fixes its error AST. -/
theorem PatternRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternRecoveryParses input left afterLeft)
    (rightParsed : PatternRecoveryParses input right afterRight) :
    left = right :=
  (leftParsed.result_unique rightParsed).1

/-- An unavailable mandatory token yields one nonconsuming rejection endpoint. -/
theorem PatternRecoveryRejects.output_unique
    {input left right : Remainder}
    (leftRejected : PatternRecoveryRejects input left)
    (rightRejected : PatternRecoveryRejects input right) : left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Ordinary malformed-pattern recovery has fully exact outcomes. -/
theorem patternRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PatternRecoveryParses PatternRecoveryRejects where
  toDeterministicOutcomeSpec := patternRecoveryDeterministicOutcomeSpec
  successValueUnique := PatternRecoveryParses.value_unique
  rejectOutputUnique := PatternRecoveryRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternPublicOutcomeProperties
/-! Deterministic outcomes at the public Core pattern recovery boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A pre-recovery boundary is also a stop of the recovery scan itself. -/
theorem PatternBoundaryStops.toRecoveryStop {input : Remainder}
    (stops : PatternBoundaryStops input) :
    PatternRecoveryStops input input := by
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | comma token => exact .comma token
  | rightParen token => exact .rightParen token
  | fatArrow token => exact .fatArrow token
  | pipe token => exact .pipe token
  | rightBrace token => exact .rightBrace token

/-- Preserved carrier and active-window evidence makes cursor-only rewind
exactly the original declarative input. -/
theorem PatternCoreRejectsWithPreservedWindow.exists_rewind_eq
    {coreRejects : Remainder → Remainder → Prop} {input : Remainder}
    (rejected : PatternCoreRejectsWithPreservedWindow coreRejects input) :
    ∃ failed, coreRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- Public ordinary pattern success has a functional output whenever the Core
outcome does. -/
theorem PatternLayerOrdinaryParses.output_unique
    {coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternLayerOrdinaryParses coreOrdinary coreRejects input
      left afterLeft)
    (rightParsed : PatternLayerOrdinaryParses coreOrdinary coreRejects input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact coreOutcomes.successOutputUnique leftCore rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim (coreOutcomes.successRejectDisjoint coreRejected
            ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim (coreOutcomes.successRejectDisjoint coreRejected
            ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Exact public rejection excludes both direct Core and recovered success. -/
theorem PatternLayerRejects.disjointOrdinary
    {coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input rejected : Remainder}
    (rejection : PatternLayerRejects coreRejects input rejected) :
    ¬ ∃ pattern output,
      PatternLayerOrdinaryParses coreOrdinary coreRejects input pattern
        output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | boundary coreRejected stops =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact coreOutcomes.successRejectDisjoint rejected
            ⟨_, _, coreParsed⟩
      | recovered otherRejected continues recovered => exact continues stops
  | recovery coreRejected continues recoveryRejected =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact coreOutcomes.successRejectDisjoint rejected
            ⟨_, _, coreParsed⟩
      | recovered otherRejected otherContinues recovered =>
          exact patternRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint recoveryRejected ⟨_, _, recovered⟩

/-- Every public pattern rejection leaves the rewound input unchanged. -/
theorem PatternLayerRejects.output_eq
    {coreRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : PatternLayerRejects coreRejects input rejected) :
    rejected = input := by
  cases rejection with
  | boundary => rfl
  | recovery coreRejected continues recoveryRejected =>
      exact recoveryRejected.output_eq

/-- Lift a deterministic Core-pattern outcome through rewind and recovery. -/
theorem patternLayerDeterministicOutcomeSpec
    {coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects) :
    DeterministicOutcomeSpec
      (PatternLayerOrdinaryParses coreOrdinary coreRejects)
      (PatternLayerRejects coreRejects) where
  successOutputUnique := PatternLayerOrdinaryParses.output_unique coreOutcomes
  successRejectDisjoint := PatternLayerRejects.disjointOrdinary coreOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternLayerExactnessProperties
/-! Exact values and nonconsuming rejection at the public pattern layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Core success values and exact recovery make public pattern values unique.
The raw Core rejection endpoint need not be unique because recovery rewinds. -/
theorem PatternLayerOrdinaryParses.value_unique
    {coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    (coreValueUnique : ∀ {input left right afterLeft afterRight},
      coreOrdinary input left afterLeft →
      coreOrdinary input right afterRight → left = right)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternLayerOrdinaryParses coreOrdinary coreRejects input
      left afterLeft)
    (rightParsed : PatternLayerOrdinaryParses coreOrdinary coreRejects input
      right afterRight) : left = right := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact coreValueUnique leftCore rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (coreOutcomes.successRejectDisjoint coreRejected
              ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (coreOutcomes.successRejectDisjoint coreRejected
              ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.value_unique rightRecovery

/-- Every ordinary public pattern rejection fixes its original-input endpoint. -/
theorem PatternLayerRejects.output_unique
    {coreRejects : Remainder → Remainder → Prop}
    {input left right : Remainder}
    (leftRejected : PatternLayerRejects coreRejects input left)
    (rightRejected : PatternLayerRejects coreRejects input right) :
    left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Deterministic Core outcomes with unique successful values lift through
the public pattern recovery boundary to fully exact outcomes. -/
theorem patternLayerExactOutcomeSpec
    {coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    (coreValueUnique : ∀ {input left right afterLeft afterRight},
      coreOrdinary input left afterLeft →
      coreOrdinary input right afterRight → left = right) :
    ExactDeterministicOutcomeSpec
      (PatternLayerOrdinaryParses coreOrdinary coreRejects)
      (PatternLayerRejects coreRejects) where
  toDeterministicOutcomeSpec := patternLayerDeterministicOutcomeSpec coreOutcomes
  successValueUnique := PatternLayerOrdinaryParses.value_unique coreOutcomes
    coreValueUnique
  rejectOutputUnique := PatternLayerRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternParenthesizedTailOutcomeProperties
/-! Determinism and rejection exclusion for parenthesized-pattern tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem exactToken_output_unique_variant {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- Every successful pattern tuple tail starts with its selected comma. -/
theorem ParenthesizedPatternTupleTailParses.comma_conflicts_absent
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {input output : Remainder} {elements : List Syntax.Pattern}
    {closingSpan : SourceSpan}
    (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .comma))
    (parsed : ParenthesizedPatternTupleTailParses nestedOrdinary input elements
      closingSpan output) : False := by
  cases parsed with
  | trailing commaSpan closingSpan commaParsed closingParsed =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | final commaSpan closingSpan commaParsed closingAbsent elementParsed
        progress laterCommaAbsent closingParsed =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | next commaSpan closingSpan commaParsed closingAbsent elementParsed
        progress tail =>
      exact absent_conflicts_exact commaAbsent commaParsed

/-- Every rejected pattern tuple tail starts with its selected comma. -/
theorem ParenthesizedPatternTupleTailRejects.comma_conflicts_absent
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .comma))
    (rejection : ParenthesizedPatternTupleTailRejects nestedOrdinary
      nestedRejects input rejected) : False := by
  cases rejection with
  | elementRejected commaSpan commaParsed closingAbsent elementRejected =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | closingMissing commaSpan commaParsed closingAbsentAfterComma
        elementParsed progress laterCommaAbsent closingAbsent =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | laterRejected commaSpan commaParsed closingAbsent elementParsed progress
        tailRejected =>
      exact absent_conflicts_exact commaAbsent commaParsed

/-- Successful maximal pattern tuple tails have a unique output remainder. -/
theorem ParenthesizedPatternTupleTailParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    (nestedOutputUnique : ∀ {input : Remainder}
      {left right : Syntax.Pattern} {afterLeft afterRight : Remainder},
      nestedOrdinary input left afterLeft →
      nestedOrdinary input right afterRight → afterLeft = afterRight) :
    ∀ {input : Remainder} {left right : List Syntax.Pattern}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      ParenthesizedPatternTupleTailParses nestedOrdinary input left
          leftClosing afterLeft →
      ParenthesizedPatternTupleTailParses nestedOrdinary input right
          rightClosing afterRight →
      afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight
    leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | trailing leftCommaSpan leftClosingSpan leftComma leftClosing =>
      intro rightParsed
      cases rightParsed with
      | trailing rightCommaSpan rightClosingSpan rightComma rightClosing =>
          have afterCommaEq := exactToken_output_unique_variant leftComma rightComma
          subst afterCommaEq
          exact exactToken_output_unique_variant leftClosing rightClosing
      | final rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightCommaAbsent rightClosing =>
          have afterCommaEq := exactToken_output_unique_variant leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
      | next rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightTail =>
          have afterCommaEq := exactToken_output_unique_variant leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
  | final leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
        leftElement leftProgress leftCommaAbsent leftClosing =>
      intro rightParsed
      cases rightParsed with
      | trailing rightCommaSpan rightClosingSpan rightComma rightClosing =>
          have afterCommaEq := exactToken_output_unique_variant leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | final rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightCommaAbsent rightClosing =>
          have afterCommaEq := exactToken_output_unique_variant leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact exactToken_output_unique_variant leftClosing rightClosing
      | next rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightTail =>
          have afterCommaEq := exactToken_output_unique_variant leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact False.elim
            (rightTail.comma_conflicts_absent leftCommaAbsent)
  | next leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
        leftElement leftProgress leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | trailing rightCommaSpan rightClosingSpan rightComma rightClosing =>
          have afterCommaEq := exactToken_output_unique_variant leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | final rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightCommaAbsent rightClosing =>
          have afterCommaEq := exactToken_output_unique_variant leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact False.elim
            (leftTail.comma_conflicts_absent rightCommaAbsent)
      | next rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightTail =>
          have afterCommaEq := exactToken_output_unique_variant leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact inductionHypothesis rightTail

/-- Exact pattern tuple-tail rejection excludes every successful tail. -/
theorem ParenthesizedPatternTupleTailRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : ParenthesizedPatternTupleTailRejects nestedOrdinary
      nestedRejects input rejected) :
    ¬ ∃ elements closingSpan output,
      ParenthesizedPatternTupleTailParses nestedOrdinary input elements
        closingSpan output := by
  induction rejection with
  | elementRejected rejectedCommaSpan rejectedComma rejectedClosingAbsent
        rejectedElement =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | trailing successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosing =>
          have afterCommaEq := exactToken_output_unique_variant rejectedComma
            successfulComma
          subst afterCommaEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | final successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterCommaEq := exactToken_output_unique_variant rejectedComma
            successfulComma
          subst afterCommaEq
          exact nestedOutcomes.successRejectDisjoint rejectedElement
            ⟨_, _, successfulElement⟩
      | next successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulTail =>
          have afterCommaEq := exactToken_output_unique_variant rejectedComma
            successfulComma
          subst afterCommaEq
          exact nestedOutcomes.successRejectDisjoint rejectedElement
            ⟨_, _, successfulElement⟩
  | closingMissing rejectedCommaSpan rejectedComma
        rejectedClosingAbsentAfterComma rejectedElement rejectedProgress
        rejectedCommaAbsent rejectedClosingAbsent =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | trailing successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosing =>
          have afterCommaEq := exactToken_output_unique_variant rejectedComma
            successfulComma
          subst afterCommaEq
          exact absent_conflicts_exact rejectedClosingAbsentAfterComma
            successfulClosing
      | final successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterCommaEq := exactToken_output_unique_variant rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | next successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulTail =>
          have afterCommaEq := exactToken_output_unique_variant rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact successfulTail.comma_conflicts_absent rejectedCommaAbsent
  | laterRejected rejectedCommaSpan rejectedComma rejectedClosingAbsent
        rejectedElement rejectedProgress rejectedTail inductionHypothesis =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | trailing successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosing =>
          have afterCommaEq := exactToken_output_unique_variant rejectedComma
            successfulComma
          subst afterCommaEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | final successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterCommaEq := exactToken_output_unique_variant rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact rejectedTail.comma_conflicts_absent successfulCommaAbsent
      | next successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulTail =>
          have afterCommaEq := exactToken_output_unique_variant rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternParenthesizedOutcomeProperties
/-! Deterministic ordinary outcomes for Core parenthesized patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A parenthesized-pattern success has a unique maximal remainder. -/
theorem ParenthesizedPatternOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input left
      afterLeft)
    (rightParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | empty leftOpeningSpan leftClosingSpan leftOpening leftClosing =>
      cases rightParsed with
      | empty rightOpeningSpan rightClosingSpan rightOpening rightClosing =>
          have afterOpeningEq := exactToken_output_unique_variant leftOpening
            rightOpening
          subst afterOpeningEq
          exact exactToken_output_unique_variant leftClosing rightClosing
      | group rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightElement rightProgress rightCommaAbsent
            rightClosing =>
          have afterOpeningEq := exactToken_output_unique_variant leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
      | tuple rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightFirst rightProgress rightTail =>
          have afterOpeningEq := exactToken_output_unique_variant leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
  | group leftOpeningSpan leftClosingSpan leftOpening leftClosingAbsent
        leftElement leftProgress leftCommaAbsent leftClosing =>
      cases rightParsed with
      | empty rightOpeningSpan rightClosingSpan rightOpening rightClosing =>
          have afterOpeningEq := exactToken_output_unique_variant leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | group rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightElement rightProgress rightCommaAbsent
            rightClosing =>
          have afterOpeningEq := exactToken_output_unique_variant leftOpening
            rightOpening
          subst afterOpeningEq
          have afterElementEq := nestedOutcomes.successOutputUnique leftElement
            rightElement
          subst afterElementEq
          exact exactToken_output_unique_variant leftClosing rightClosing
      | tuple rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightFirst rightProgress rightTail =>
          have afterOpeningEq := exactToken_output_unique_variant leftOpening
            rightOpening
          subst afterOpeningEq
          have afterElementEq := nestedOutcomes.successOutputUnique leftElement
            rightFirst
          subst afterElementEq
          exact False.elim
            (rightTail.comma_conflicts_absent leftCommaAbsent)
  | tuple leftOpeningSpan leftClosingSpan leftOpening leftClosingAbsent
        leftFirst leftProgress leftTail =>
      cases rightParsed with
      | empty rightOpeningSpan rightClosingSpan rightOpening rightClosing =>
          have afterOpeningEq := exactToken_output_unique_variant leftOpening
            rightOpening
          subst afterOpeningEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | group rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightElement rightProgress rightCommaAbsent
            rightClosing =>
          have afterOpeningEq := exactToken_output_unique_variant leftOpening
            rightOpening
          subst afterOpeningEq
          have afterElementEq := nestedOutcomes.successOutputUnique leftFirst
            rightElement
          subst afterElementEq
          exact False.elim
            (leftTail.comma_conflicts_absent rightCommaAbsent)
      | tuple rightOpeningSpan rightClosingSpan rightOpening
            rightClosingAbsent rightFirst rightProgress rightTail =>
          have afterOpeningEq := exactToken_output_unique_variant leftOpening
            rightOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique leftFirst
            rightFirst
          subst afterFirstEq
          exact ParenthesizedPatternTupleTailParses.output_unique
            (nestedOrdinary := nestedOrdinary)
            nestedOutcomes.successOutputUnique leftTail rightTail

/-- Exact parenthesized-pattern rejection excludes every ordinary success. -/
theorem ParenthesizedPatternRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : ParenthesizedPatternRejects nestedOrdinary nestedRejects
      input rejected) :
    ¬ ∃ pattern output,
      ParenthesizedPatternOrdinaryParses nestedOrdinary input pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | openingMissing openingAbsent =>
      cases successful with
      | empty openingSpan closingSpan opening closing =>
          exact absent_conflicts_exact openingAbsent opening
      | group openingSpan closingSpan opening closingAbsent element progress
            commaAbsent closing =>
          exact absent_conflicts_exact openingAbsent opening
      | tuple openingSpan closingSpan opening closingAbsent first progress
            tail =>
          exact absent_conflicts_exact openingAbsent opening
  | firstRejected rejectedOpeningSpan rejectedOpening rejectedClosingAbsent
        rejectedFirst =>
      cases successful with
      | empty successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosing =>
          have afterOpeningEq := exactToken_output_unique_variant rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | group successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterOpeningEq := exactToken_output_unique_variant rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact nestedOutcomes.successRejectDisjoint rejectedFirst
            ⟨_, _, successfulFirst⟩
      | tuple successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulTail =>
          have afterOpeningEq := exactToken_output_unique_variant rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact nestedOutcomes.successRejectDisjoint rejectedFirst
            ⟨_, _, successfulFirst⟩
  | closingMissing rejectedOpeningSpan rejectedOpening
        rejectedClosingAbsentAfterOpening rejectedFirst rejectedProgress
        rejectedCommaAbsent rejectedClosingAbsent =>
      cases successful with
      | empty successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosing =>
          have afterOpeningEq := exactToken_output_unique_variant rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact absent_conflicts_exact rejectedClosingAbsentAfterOpening
            successfulClosing
      | group successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterOpeningEq := exactToken_output_unique_variant rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | tuple successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulTail =>
          have afterOpeningEq := exactToken_output_unique_variant rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact successfulTail.comma_conflicts_absent rejectedCommaAbsent
  | tailRejected rejectedOpeningSpan rejectedOpening rejectedClosingAbsent
        rejectedFirst rejectedProgress rejectedTail =>
      cases successful with
      | empty successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosing =>
          have afterOpeningEq := exactToken_output_unique_variant rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | group successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterOpeningEq := exactToken_output_unique_variant rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact rejectedTail.comma_conflicts_absent successfulCommaAbsent
      | tuple successfulOpeningSpan successfulClosingSpan successfulOpening
            successfulClosingAbsent successfulFirst successfulProgress
            successfulTail =>
          have afterOpeningEq := exactToken_output_unique_variant rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterFirstEq := nestedOutcomes.successOutputUnique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact rejectedTail.disjointOrdinary nestedOutcomes
            ⟨_, _, _, successfulTail⟩

/-- Lift deterministic nested pattern outcomes through parentheses. -/
theorem parenthesizedPatternDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (ParenthesizedPatternOrdinaryParses nestedOrdinary)
      (ParenthesizedPatternRejects nestedOrdinary nestedRejects) where
  successOutputUnique :=
    ParenthesizedPatternOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    ParenthesizedPatternRejects.disjointOrdinary nestedOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternParenthesizedValueProperties
/-! Exact success values for parenthesized Core patterns and tuple tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem patternTuple_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Exact nested patterns fix a tuple tail's forward list, closing span, and
final remainder, including its trailing-comma branch. -/
theorem ParenthesizedPatternTupleTailParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    ∀ {input : Remainder} {left right : List Syntax.Pattern}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      ParenthesizedPatternTupleTailParses nestedOrdinary input left
        leftClosing afterLeft →
      ParenthesizedPatternTupleTailParses nestedOrdinary input right
        rightClosing afterRight →
      left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | trailing leftCommaSpan leftClosingSpan leftComma leftClosing =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique,
          patternTuple_absent_conflicts_exact]
  | final leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
      leftElement leftProgress leftCommaAbsent leftClosing =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique,
          nestedOutcomes.successResultUnique,
          patternTuple_absent_conflicts_exact,
          ParenthesizedPatternTupleTailParses.comma_conflicts_absent]
  | next leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
      leftElement leftProgress leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed <;>
        grind [ExactTokenParses.result_unique,
          nestedOutcomes.successResultUnique,
          patternTuple_absent_conflicts_exact,
          ParenthesizedPatternTupleTailParses.comma_conflicts_absent]

/-- Exact nested patterns fix the complete empty, group, or tuple AST. -/
theorem ParenthesizedPatternOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input left
      afterLeft)
    (rightParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input right
      afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [ExactTokenParses.result_unique,
      nestedOutcomes.successResultUnique,
      ParenthesizedPatternTupleTailParses.result_unique nestedOutcomes,
      patternTuple_absent_conflicts_exact,
      ParenthesizedPatternTupleTailParses.comma_conflicts_absent]

/-- Parenthesized pattern success fixes its complete AST and final remainder. -/
theorem ParenthesizedPatternOrdinaryParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input left
      afterLeft)
    (rightParsed : ParenthesizedPatternOrdinaryParses nestedOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique nestedOutcomes rightParsed,
    leftParsed.output_unique nestedOutcomes.toDeterministicOutcomeSpec
      rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternStepOutcomeProperties
/-! Deterministic outcomes for one complete Core pattern recursion step. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Compose nested pattern and expression contracts through the four recursive
branches, ordered core dispatcher, and public recovery boundary. -/
theorem corePatternStepDeterministicOutcomeSpec
    (relations : CorePatternStepRelations)
    (nestedOutcomes : DeterministicOutcomeSpec relations.nestedOrdinary
      relations.nestedRejects)
    (expressionOutcomes : DeterministicOutcomeSpec
      relations.expressionOrdinary relations.expressionRejects) :
    DeterministicOutcomeSpec
      (CorePatternStepOrdinaryParses relations)
      (CorePatternStepRejects relations) := by
  have parenthesizedOutcomes : DeterministicOutcomeSpec
      relations.parenthesizedOrdinary relations.parenthesizedRejects :=
    parenthesizedPatternDeterministicOutcomeSpec nestedOutcomes
  have dotOutcomes : DeterministicOutcomeSpec
      relations.dotConstructorOrdinary relations.dotConstructorRejects :=
    dotConstructorPatternDeterministicOutcomeSpec nestedOutcomes
  have comptimeOutcomes : DeterministicOutcomeSpec relations.comptimeOrdinary
      relations.comptimeRejects :=
    comptimePatternDeterministicOutcomeSpec expressionOutcomes
  have qualifiedOutcomes : DeterministicOutcomeSpec
      relations.qualifiedOrdinary relations.qualifiedRejects :=
    qualifiedPatternDeterministicOutcomeSpec nestedOutcomes
  have coreOutcomes : DeterministicOutcomeSpec relations.coreOrdinary
      relations.coreRejects :=
    patternCoreDeterministicOutcomeSpec parenthesizedOutcomes dotOutcomes
      comptimeOutcomes qualifiedOutcomes
  exact patternLayerDeterministicOutcomeSpec coreOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternStepExactnessProperties
/-! Exact outcomes of one recursive Core pattern step. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact preceding pattern and expression outcomes make the complete next
pattern step exact without a raw Core-rejection uniqueness premise. -/
theorem corePatternStepExactOutcomeSpec
    (relations : CorePatternStepRelations)
    (nestedOutcomes : ExactDeterministicOutcomeSpec relations.nestedOrdinary
      relations.nestedRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      relations.expressionOrdinary relations.expressionRejects) :
    ExactDeterministicOutcomeSpec
      (CorePatternStepOrdinaryParses relations)
      (CorePatternStepRejects relations) := by
  have coreOutcomes : DeterministicOutcomeSpec relations.coreOrdinary
      relations.coreRejects :=
    patternCoreDeterministicOutcomeSpec
      (parenthesizedPatternDeterministicOutcomeSpec
        nestedOutcomes.toDeterministicOutcomeSpec)
      (dotConstructorPatternDeterministicOutcomeSpec
        nestedOutcomes.toDeterministicOutcomeSpec)
      (comptimePatternDeterministicOutcomeSpec
        expressionOutcomes.toDeterministicOutcomeSpec)
      (qualifiedPatternDeterministicOutcomeSpec
        nestedOutcomes.toDeterministicOutcomeSpec)
  exact patternLayerExactOutcomeSpec coreOutcomes
    (PatternCoreOrdinaryParses.value_unique
      (parenthesizedOrdinary := relations.parenthesizedOrdinary)
      (dotConstructorOrdinary := relations.dotConstructorOrdinary)
      (comptimeOrdinary := relations.comptimeOrdinary)
      (qualifiedOrdinary := relations.qualifiedOrdinary)
      (ParenthesizedPatternOrdinaryParses.value_unique nestedOutcomes)
      (DotConstructorPatternOrdinaryParses.value_unique nestedOutcomes)
      (ComptimePatternOrdinaryParses.value_unique expressionOutcomes)
      (QualifiedPatternOrdinaryParses.value_unique nestedOutcomes))

/-- One complete pattern step fixes its successful AST and final remainder. -/
theorem CorePatternStepOrdinaryParses.result_unique
    {relations : CorePatternStepRelations}
    (nestedOutcomes : ExactDeterministicOutcomeSpec relations.nestedOrdinary
      relations.nestedRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      relations.expressionOrdinary relations.expressionRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : CorePatternStepOrdinaryParses relations input left afterLeft)
    (rightParsed : CorePatternStepOrdinaryParses relations input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  (corePatternStepExactOutcomeSpec relations nestedOutcomes expressionOutcomes)
    |>.successResultUnique leftParsed rightParsed

end Solcore.Syntax.DeclarativeGrammar
end
