import Solcore.Syntax.DeclarativeCoreArrayLiteralOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionAtomCoreOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreExpressionLambdaOutcomeProperties
import Solcore.Syntax.DeclarativeCoreIdentifierExpressionOutcomeProperties
import Solcore.Syntax.DeclarativeCoreLiteralOutcomeProperties
import Solcore.Syntax.DeclarativeCoreParenthesizedOutcomeProperties
import Solcore.Syntax.DeclarativeCoreProxyExpressionOutcomeProperties

/-! Starter evidence retained by every ordered Core atom branch outcome. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary literal leaves expose the literal dispatcher guard. -/
theorem LiteralExpressionOrdinaryParses.coreLiteralStartsAt
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : LiteralExpressionOrdinaryParses input expression output) :
    CoreLiteralStartsAt input := by
  cases parsed with
  | parsed literalParsed =>
      cases literalParsed with
      | decimal token => exact Or.inl ⟨_, _, token⟩
      | hexadecimal token => exact Or.inr (Or.inl ⟨_, _, token⟩)
      | string token => exact Or.inr (Or.inr ⟨_, _, token⟩)

/-- Ordinary identifier leaves expose the Boolean-or-identifier guard. -/
theorem IdentifierExpressionOrdinaryParses.expressionNameStartsAt
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : IdentifierExpressionOrdinaryParses input expression output) :
    ExpressionNameStartsAt input := by
  cases parsed with
  | parsed nameParsed =>
      cases nameParsed with
      | boolean booleanParsed =>
          cases booleanParsed with
          | trueKeyword token => exact Or.inl ⟨_, token⟩
          | falseKeyword token => exact Or.inr (Or.inl ⟨_, token⟩)
      | identifier trueAbsent falseAbsent identifierParsed =>
          exact Or.inr (Or.inr ⟨_, _, identifierParsed.1⟩)

/-- Ordinary leading-dot construction exposes its selected marker. -/
theorem DotConstructorOrdinaryParses.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : DotConstructorOrdinaryParses nestedOrdinary input expression
      output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .dot } := by
  cases parsed with
  | parsed dotSpan dotParsed nameParsed argumentsParsed =>
      exact ⟨dotSpan, dotParsed.1⟩

/-- Rejected leading-dot construction retains the same selected marker. -/
theorem DotConstructorRejects.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : DotConstructorRejects nestedOrdinary nestedRejects input
      rejected) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .dot } := by
  cases rejection with
  | nameRejected dotSpan dotParsed nameRejected =>
      exact ⟨dotSpan, dotParsed.1⟩
  | argumentsRejected dotSpan dotParsed nameParsed argumentsRejected =>
      exact ⟨dotSpan, dotParsed.1⟩

/-- Ordinary proxy construction exposes its selected `@`. -/
theorem ProxyExpressionOrdinaryParses.marker_present
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ProxyExpressionOrdinaryParses typeOrdinary input expression
      output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .at } := by
  cases parsed with
  | parsed markerSpan markerParsed typeParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

/-- Rejected proxy construction retains its selected `@`. -/
theorem ProxyExpressionRejects.marker_present
    {typeRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : ProxyExpressionRejects typeRejects input rejected) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .at } := by
  cases rejection with
  | typeRejected markerSpan markerParsed typeRejected =>
      exact ⟨markerSpan, markerParsed.1⟩

/-- Ordinary parenthesized atoms expose their selected opening marker. -/
theorem ParenthesizedExpressionOrdinaryParses.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input
      expression output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftParen } := by
  cases parsed with
  | empty openingSpan closingSpan openingParsed closingParsed =>
      exact ⟨openingSpan, openingParsed.1⟩
  | group openingSpan closingSpan openingParsed closingAbsent elementParsed
        progress commaAbsent closingParsed =>
      exact ⟨openingSpan, openingParsed.1⟩
  | tuple openingSpan closingSpan openingParsed closingAbsent firstParsed
        progress tail =>
      exact ⟨openingSpan, openingParsed.1⟩

/-- Rejected parenthesized atoms retain their selected opening marker. -/
theorem ParenthesizedExpressionRejects.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : ParenthesizedExpressionRejects nestedOrdinary nestedRejects
      input rejected) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftParen } := by
  cases rejection with
  | firstRejected openingSpan openingParsed closingAbsent firstRejected =>
      exact ⟨openingSpan, openingParsed.1⟩
  | closingMissing openingSpan openingParsed closingAbsent firstParsed
        progress commaAbsent closingAbsent =>
      exact ⟨openingSpan, openingParsed.1⟩
  | tailRejected openingSpan openingParsed closingAbsent firstParsed progress
        tailRejected =>
      exact ⟨openingSpan, openingParsed.1⟩

/-- Ordinary arrays expose their selected opening bracket. -/
theorem ArrayLiteralExpressionOrdinaryParses.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input
      expression output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftBracket } := by
  cases parsed with
  | parsed valuesParsed =>
      cases valuesParsed with
      | empty openingSpan closingSpan openingToken closingToken =>
          exact ⟨openingSpan, openingToken⟩
      | nonempty closingAbsent nonemptyParsed =>
          rcases nonemptyParsed with ⟨openingSpan, first, afterFirst, rest,
            closingSpan, tokensEq, endIndexEq, openingToken, firstParsed,
            progress, tail, elementsEq, spanEq⟩
          exact ⟨openingSpan, openingToken⟩

/-- Rejected arrays retain their selected opening bracket. -/
theorem ArrayLiteralExpressionRejects.marker_present
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : ArrayLiteralExpressionRejects nestedOrdinary nestedRejects
      input rejected) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftBracket } := by
  cases rejection with
  | present openingSpan openingToken valuesRejected =>
      exact ⟨openingSpan, openingToken⟩

end Solcore.Syntax.DeclarativeGrammar
