import Solcore.Syntax.DeclarativeCoreExpressionDotConstructorOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreExpressionNameOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingOutcomeProperties

/-! Deterministic ordinary outcomes for a guarded leading-dot constructor. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem noTrailing_opening_present {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : NoTrailingDelimitedListParses opening closing elementParses input
      values output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol opening
    } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- Optional leading-dot arguments have a unique ordinary output. -/
theorem OptionalDotConstructorArgumentsOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.Expr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalDotConstructorArgumentsOrdinaryParses
      nestedOrdinary input left afterLeft)
    (rightParsed : OptionalDotConstructorArgumentsOrdinaryParses
      nestedOrdinary input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightArguments =>
          rcases noTrailing_opening_present rightArguments with
            ⟨span, openingToken⟩
          exact False.elim (absent_conflicts_token leftAbsent openingToken)
  | present leftArguments =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases noTrailing_opening_present leftArguments with
            ⟨span, openingToken⟩
          exact False.elim (absent_conflicts_token rightAbsent openingToken)
      | present rightArguments =>
          exact NoTrailingDelimitedListParses.output_unique
            (opening := .leftParen) (closing := .rightParen)
            (elementParses := nestedOrdinary)
            nestedOutcomes.successOutputUnique leftArguments rightArguments

/-- Present optional-argument rejection excludes both the absent and present
ordinary branches. -/
theorem OptionalDotConstructorArgumentsRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : OptionalDotConstructorArgumentsRejects nestedOrdinary
      nestedRejects input rejected) :
    ¬ ∃ arguments output,
      OptionalDotConstructorArgumentsOrdinaryParses nestedOrdinary input
        arguments output := by
  rintro ⟨arguments, output, successful⟩
  cases rejection with
  | present openingSpan openingToken argumentsRejected =>
      cases successful with
      | absent openingAbsent =>
          exact absent_conflicts_token openingAbsent openingToken
      | present argumentsParsed =>
          exact argumentsRejected.disjointAllowEmptyNoTrailing nestedOutcomes
            ⟨_, _, argumentsParsed⟩

/-- Optional leading-dot arguments form a deterministic ordinary outcome. -/
theorem optionalDotConstructorArgumentsDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (OptionalDotConstructorArgumentsOrdinaryParses nestedOrdinary)
      (OptionalDotConstructorArgumentsRejects nestedOrdinary nestedRejects)
      where
  successOutputUnique :=
    OptionalDotConstructorArgumentsOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    OptionalDotConstructorArgumentsRejects.disjointOrdinary nestedOutcomes

/-- Pointwise nested inclusion lifts through optional leading-dot
arguments. -/
theorem OptionalDotConstructorArgumentsParses.mapNestedRelation
    {source target : Remainder → Syntax.Expr → Remainder → Prop}
    (includeNested : ∀ {input expression output},
      source input expression output → target input expression output)
    {input output : Remainder}
    {arguments : Option (DelimitedList Syntax.Expr)}
    (parsed : OptionalDotConstructorArgumentsParses source input arguments
      output) :
    OptionalDotConstructorArgumentsOrdinaryParses target input arguments
      output := by
  cases parsed with
  | absent openingAbsent => exact .absent openingAbsent
  | present argumentsParsed =>
      exact .present (argumentsParsed.mapElementRelation includeNested)

/-- Ordinary leading-dot construction has the unique output selected by its
name and optional arguments. -/
theorem DotConstructorOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : DotConstructorOrdinaryParses nestedOrdinary input left
      afterLeft)
    (rightParsed : DotConstructorOrdinaryParses nestedOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftDotSpan leftDot leftName leftArguments =>
      cases rightParsed with
      | parsed rightDotSpan rightDot rightName rightArguments =>
          have afterDotEq := exactToken_output_unique leftDot rightDot
          subst afterDotEq
          have afterNameEq :=
            ExpressionNameOrdinaryParses.output_unique leftName rightName
          subst afterNameEq
          exact OptionalDotConstructorArgumentsOrdinaryParses.output_unique
            nestedOutcomes leftArguments rightArguments

/-- Rejection at the name or argument stage excludes every ordinary
leading-dot constructor success. -/
theorem DotConstructorRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : DotConstructorRejects nestedOrdinary nestedRejects input
      rejected) :
    ¬ ∃ expression output,
      DotConstructorOrdinaryParses nestedOrdinary input expression output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | nameRejected rejectedDotSpan rejectedDot rejectedName =>
      cases successful with
      | parsed successfulDotSpan successfulDot successfulName arguments =>
          have afterDotEq := exactToken_output_unique rejectedDot successfulDot
          subst afterDotEq
          exact rejectedName.disjointOrdinary
            ⟨_, _, successfulName⟩
  | argumentsRejected rejectedDotSpan rejectedDot rejectedName
        rejectedArguments =>
      cases successful with
      | parsed successfulDotSpan successfulDot successfulName
            successfulArguments =>
          have afterDotEq := exactToken_output_unique rejectedDot successfulDot
          subst afterDotEq
          have afterNameEq := ExpressionNameOrdinaryParses.output_unique
            rejectedName successfulName
          subst afterNameEq
          exact rejectedArguments.disjointOrdinary nestedOutcomes
            ⟨_, _, successfulArguments⟩

/-- Guarded leading-dot constructor outcomes are deterministic whenever the
nested expression outcome is. -/
theorem dotConstructorDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec (DotConstructorOrdinaryParses nestedOrdinary)
      (DotConstructorRejects nestedOrdinary nestedRejects) where
  successOutputUnique :=
    DotConstructorOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    DotConstructorRejects.disjointOrdinary nestedOutcomes

/-- The existing clean leading-dot grammar embeds through any supplied
clean-to-ordinary nested-expression bridge. -/
theorem DotConstructorParses.toOrdinary
    {source target : Remainder → Syntax.Expr → Remainder → Prop}
    (nestedToOrdinary : ∀ {input expression output},
      source input expression output → target input expression output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : DotConstructorParses source input expression output) :
    DotConstructorOrdinaryParses target input expression output := by
  cases parsed with
  | parsed dotSpan dotParsed nameParsed argumentsParsed =>
      exact .parsed dotSpan dotParsed nameParsed
        (argumentsParsed.mapNestedRelation nestedToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
