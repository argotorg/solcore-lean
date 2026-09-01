import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent grammar for parenthesized and array Core expression atoms.

The parenthesized grammar records the parser's delimiter priorities and keeps
tuple elements in source order.  In particular, it mirrors `closeTuple`:
exactly one accumulated element is a group, even when followed by a comma.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Pure forward-order counterpart of the parser's `closeTuple` result. -/
def closeParenthesizedExpression (openingSpan closingSpan : SourceSpan)
    (elements : List Syntax.Expr) : Syntax.Expr :=
  let span := SourceSpan.cover openingSpan closingSpan
  match elements with
  | [only] => { span, value := .group only }
  | _ => { span, value := .tuple { span, elements } }

/--
Exact continuation after the first comma of a parenthesized expression.
The returned elements are in source order and exclude those parsed earlier.
-/
inductive ParenthesizedTupleTailParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → List Syntax.Expr → SourceSpan → Remainder → Prop where
  | trailing {input afterComma output : Remainder}
      (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterComma
        closingSpan output) :
      ParenthesizedTupleTailParses nestedParses input [] closingSpan output
  | final {input afterComma afterElement output : Remainder}
      {element : Syntax.Expr} (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedParses afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens
        afterElement.endIndex afterElement.cursor (.symbol .comma))
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterElement
        closingSpan output) :
      ParenthesizedTupleTailParses nestedParses input [element] closingSpan
        output
  | next {input afterComma afterElement output : Remainder}
      {element : Syntax.Expr} {elements : List Syntax.Expr}
      (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedParses afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (tail : ParenthesizedTupleTailParses nestedParses afterElement elements
        closingSpan output) :
      ParenthesizedTupleTailParses nestedParses input (element :: elements)
        closingSpan output

/-- Exact prioritized grammar of a grouped or tuple expression atom. -/
inductive ParenthesizedExpressionParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | empty {input afterOpening output : Remainder}
      (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterOpening
        closingSpan output) :
      ParenthesizedExpressionParses nestedParses input
        (closeParenthesizedExpression openingSpan closingSpan []) output
  | group {input afterOpening afterElement output : Remainder}
      {element : Syntax.Expr} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (elementParsed : nestedParses afterOpening element afterElement)
      (progress : afterOpening.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens
        afterElement.endIndex afterElement.cursor (.symbol .comma))
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterElement
        closingSpan output) :
      ParenthesizedExpressionParses nestedParses input
        (closeParenthesizedExpression openingSpan closingSpan [element])
        output
  | tuple {input afterOpening afterFirst output : Remainder}
      {first : Syntax.Expr} {rest : List Syntax.Expr}
      (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : nestedParses afterOpening first afterFirst)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tail : ParenthesizedTupleTailParses nestedParses afterFirst rest
        closingSpan output) :
      ParenthesizedExpressionParses nestedParses input
        (closeParenthesizedExpression openingSpan closingSpan (first :: rest))
        output

/-- Exact no-trailing-comma grammar of an array expression atom. -/
inductive ArrayLiteralExpressionParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input output : Remainder}
      {values : DelimitedList Syntax.Expr}
      (valuesParsed : NoTrailingDelimitedListParses .leftBracket .rightBracket
        nestedParses input values output) :
      ArrayLiteralExpressionParses nestedParses input {
        span := values.span
        value := .array values
      } output

end Solcore.Syntax.DeclarativeGrammar
