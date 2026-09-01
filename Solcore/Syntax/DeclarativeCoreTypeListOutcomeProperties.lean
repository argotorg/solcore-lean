import Solcore.Syntax.DeclarativeCoreTypeSuccessProperties
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-! Disjointness of generic list rejection from recursive Core-type lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Generic and recursive successful type tails end at the same cursor. -/
theorem TrailingDelimitedTailParses.output_uniqueTypeTail
    {closing : Symbol} {input : Remainder}
    {left right : List Syntax.TypeExpr}
    {leftClosing rightClosing : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : TrailingDelimitedTailParses closing TypeExprParses input
      left leftClosing afterLeft)
    (rightParsed : TypeExprTrailingDelimitedTailParses closing input right
      rightClosing afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing right rightClosing afterRight with
  | close commaAbsent closingToken =>
      cases rightParsed with
      | close => rfl
      | trailing commaToken _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token commaAbsent commaToken)
      | next commaToken _ _ _ _ _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token commaAbsent commaToken)
  | trailing commaToken closingToken =>
      cases rightParsed with
      | close commaAbsent _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token commaAbsent commaToken)
      | trailing => rfl
      | next _ closingAbsent _ _ _ _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent closingToken)
  | next commaToken closingAbsent elementParsed progress tail
        inductionHypothesis =>
      cases rightParsed with
      | close commaAbsent _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token commaAbsent commaToken)
      | trailing _ closingToken =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent closingToken)
      | next _ _ _ _ successfulElement successfulTail =>
          have outputEq := TypeExprParses.output_unique elementParsed
            successfulElement
          subst outputEq
          exact inductionHypothesis successfulTail

/-- Generic and recursive successful type lists end at the same cursor. -/
theorem TrailingDelimitedListParses.output_uniqueTypeList
    {opening closing : Symbol} {input : Remainder}
    {left right : DelimitedList Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TrailingDelimitedListParses opening closing TypeExprParses
      input left afterLeft)
    (rightParsed : TypeExprTrailingDelimitedListParses opening closing input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | empty _ _ _ closingToken =>
      cases rightParsed with
      | empty => rfl
      | nonempty _ _ closingAbsent _ _ _ _ _ _ _ _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent closingToken)
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      cases rightParsed with
      | empty _ _ _ _ _ closingToken =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent closingToken)
      | nonempty _ _ _ _ _ _ _ _ _ successfulFirst successfulTail =>
          have outputEq := TypeExprParses.output_unique firstParsed
            successfulFirst
          subst outputEq
          exact tail.output_uniqueTypeTail successfulTail

/-- A generic trailing-tail rejection excludes the recursive type-tail
success judgment used by `TypeExprParses`. -/
theorem DelimitedTailRejects.disjointTypeTail
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {closing : Symbol} {input rejected : Remainder}
    (rejection : DelimitedTailRejects closing true TypeExprParses
      nestedRejects input rejected) :
    ¬ ∃ values closingSpan output,
      TypeExprTrailingDelimitedTailParses closing input values closingSpan
        output := by
  induction rejection with
  | delimiterMissing commaAbsent closingAbsent =>
      rintro ⟨values, closingSpan, output, parsed⟩
      cases parsed with
      | close _ closingToken =>
          exact typeTokenAbsent_conflicts_token closingAbsent closingToken
      | trailing commaToken _ =>
          exact typeTokenAbsent_conflicts_token commaAbsent commaToken
      | next commaToken _ _ _ _ _ =>
          exact typeTokenAbsent_conflicts_token commaAbsent commaToken
  | elementRejected commaSpan commaToken continues nestedRejected =>
      cases continues with
      | absent closingAbsent =>
          rintro ⟨values, closingSpan, output, parsed⟩
          cases parsed with
          | close commaAbsent _ =>
              exact typeTokenAbsent_conflicts_token commaAbsent commaToken
          | trailing _ closingToken =>
              exact typeTokenAbsent_conflicts_token closingAbsent closingToken
          | next _ _ _ _ elementParsed _ =>
              exact outcomes.successRejectDisjoint nestedRejected
                ⟨_, _, elementParsed⟩
  | laterRejected commaSpan commaToken continues elementParsed progress
        tailRejected inductionHypothesis =>
      cases continues with
      | absent closingAbsent =>
          rintro ⟨values, closingSpan, output, parsed⟩
          cases parsed with
          | close commaAbsent _ =>
              exact typeTokenAbsent_conflicts_token commaAbsent commaToken
          | trailing _ closingToken =>
              exact typeTokenAbsent_conflicts_token closingAbsent closingToken
          | next _ _ _ _ successfulElement successfulTail =>
              have outputEq := outcomes.successOutputUnique elementParsed
                successfulElement
              subst outputEq
              exact inductionHypothesis ⟨_, _, _, successfulTail⟩

/-- A generic allow-empty/trailing list rejection excludes the recursive
type-list success judgment. -/
theorem DelimitedListRejects.disjointTypeList
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {opening closing : Symbol} {input rejected : Remainder}
    (rejection : DelimitedListRejects opening closing true true
      TypeExprParses nestedRejects input rejected) :
    ¬ ∃ values output,
      TypeExprTrailingDelimitedListParses opening closing input values
        output := by
  rintro ⟨values, output, successful⟩
  cases rejection with
  | openingMissing openingAbsent =>
      rcases successful.opening_token with ⟨span, openingToken⟩
      exact typeTokenAbsent_conflicts_token openingAbsent openingToken
  | firstRejected openingSpan openingToken continues nestedRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty _ _ _ _ _ closingToken =>
              exact typeTokenAbsent_conflicts_token closingAbsent closingToken
          | nonempty _ _ _ _ _ _ _ _ _ firstParsed _ =>
              exact outcomes.successRejectDisjoint nestedRejected
                ⟨_, _, firstParsed⟩
  | tailRejected openingSpan openingToken continues firstParsed progress
        tailRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty _ _ _ _ _ closingToken =>
              exact typeTokenAbsent_conflicts_token closingAbsent closingToken
          | nonempty _ _ _ _ _ _ _ _ _ successfulFirst successfulTail =>
              have outputEq := outcomes.successOutputUnique firstParsed
                successfulFirst
              subst outputEq
              exact tailRejected.disjointTypeTail outcomes
                ⟨_, _, _, successfulTail⟩

/-- A selected nonempty named-type argument rejection excludes the optional
argument success branch. -/
theorem DelimitedListRejects.disjointNamedTypeArguments
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected : Remainder}
    (rejection : DelimitedListRejects .less .greater false true
      TypeExprParses nestedRejects input rejected) :
    ¬ ∃ arguments output,
      OptionalNamedTypeArgumentsParses input (some arguments) output := by
  rintro ⟨arguments, output, successful⟩
  cases successful with
  | present openingSpan closingSpan successfulOpening progress tokensEq
        endIndexEq elementsEq spanEq successfulFirst successfulTail =>
      cases rejection with
      | openingMissing openingAbsent =>
          exact typeTokenAbsent_conflicts_token openingAbsent
            successfulOpening
      | firstRejected _ _ continues nestedRejected =>
          cases continues
          exact outcomes.successRejectDisjoint nestedRejected
            ⟨_, _, successfulFirst⟩
      | tailRejected _ _ continues firstParsed _ tailRejected =>
          cases continues
          have outputEq := outcomes.successOutputUnique firstParsed
            successfulFirst
          subst outputEq
          exact tailRejected.disjointTypeTail outcomes
            ⟨_, _, _, successfulTail⟩

end Solcore.Syntax.DeclarativeGrammar
