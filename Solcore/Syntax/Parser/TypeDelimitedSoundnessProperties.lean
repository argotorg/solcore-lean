import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties

/-! Adapters from generic delimiter grammar to recursive type grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Generic recursive type tails embed in the concrete mutual type grammar. -/
theorem typeExprTrailingDelimitedTailParses_of_generic
    {closing : Symbol} {input output : DeclarativeGrammar.Remainder}
    {elements : List TypeExpr} {closingSpan : SourceSpan}
    (parsed : DeclarativeGrammar.TrailingDelimitedTailParses closing
      DeclarativeGrammar.TypeExprParses input elements closingSpan output) :
    DeclarativeGrammar.TypeExprTrailingDelimitedTailParses closing input
      elements closingSpan output := by
  induction parsed with
  | close commaAbsent closingToken =>
      exact .close commaAbsent closingToken
  | trailing commaToken closingToken =>
      exact .trailing commaToken closingToken
  | next commaToken closingAbsent elementParsed progress tail
      inductionHypothesis =>
      exact .next commaToken closingAbsent progress rfl elementParsed
        inductionHypothesis

/-- Generic possibly-empty type lists embed in the concrete mutual grammar. -/
theorem typeExprTrailingDelimitedListParses_of_generic
    {opening closing : Symbol}
    {input output : DeclarativeGrammar.Remainder}
    {values : DelimitedList TypeExpr}
    (parsed : DeclarativeGrammar.TrailingDelimitedListParses opening closing
      DeclarativeGrammar.TypeExprParses input values output) :
    DeclarativeGrammar.TypeExprTrailingDelimitedListParses opening closing
      input values output := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact .empty openingSpan closingSpan rfl rfl openingToken closingToken
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact .nonempty openingSpan closingSpan closingAbsent openingToken
        progress tokensEq endIndexEq elementsEq spanEq firstParsed
        (typeExprTrailingDelimitedTailParses_of_generic tail)

/-- A generic nonempty angle list supplies present named-type arguments. -/
theorem optionalNamedTypeArguments_present_of_nonemptyTrailing
    {input output : DeclarativeGrammar.Remainder}
    {arguments : NonemptyDelimitedList TypeExpr}
    (parsed : DeclarativeGrammar.NonemptyTrailingDelimitedListParses
      .less .greater DeclarativeGrammar.TypeExprParses input {
        span := arguments.span
        elements := arguments.elements.toList
      } output) :
    DeclarativeGrammar.OptionalNamedTypeArgumentsParses input
      (some arguments) output := by
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact .present openingSpan closingSpan openingToken progress tokensEq
    endIndexEq elementsEq spanEq firstParsed
    (typeExprTrailingDelimitedTailParses_of_generic tail)

end Solcore.Syntax.Parser
