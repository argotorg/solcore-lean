import Solcore.Syntax.DeclarativeCoreLiteralGrammar

/-!
Parser-independent grammar for the basic Core pattern leaves and
parenthesized patterns.

The parenthesized grammar records the executable parser's delimiter
priorities and keeps tuple elements in source order.  Exactly one accumulated
element closes as a group, including the source form `(pattern,)`.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact grammar of the canonical wildcard pattern. -/
inductive WildcardPatternParses :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | parsed {input output : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.symbol .underscore) input
        markerSpan output) :
      WildcardPatternParses input {
        span := markerSpan
        value := .wildcard markerSpan
      } output

/-- Exact grammar of a literal pattern leaf. -/
inductive LiteralPatternParses :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | parsed {input output : Remainder} {literal : Syntax.CoreLiteral}
      (literalParsed : CoreLiteralParses input literal output) :
      LiteralPatternParses input {
        span := literal.span
        value := .literal literal
      } output

/-- Exact grammar of a Boolean builtin used as a binder-shaped pattern. -/
inductive BooleanBinderPatternParses :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | parsed {input output : Remainder} {name : Syntax.Identifier}
      (nameParsed : BooleanIdentifierParses input name output) :
      BooleanBinderPatternParses input {
        span := name.span
        value := .binder name
      } output

/-- Pure forward-order counterpart of `closePatternTuple`. -/
def closeParenthesizedPattern (openingSpan closingSpan : SourceSpan)
    (elements : List Syntax.Pattern) : Syntax.Pattern :=
  let span := SourceSpan.cover openingSpan closingSpan
  match elements with
  | [only] => { span, value := .group only }
  | _ => { span, value := .tuple { span, elements } }

/--
Exact continuation after the first comma of a parenthesized pattern.
Returned elements are in source order and exclude those parsed earlier.
-/
inductive ParenthesizedPatternTupleTailParses
    (nestedParses : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → List Syntax.Pattern → SourceSpan → Remainder → Prop where
  | trailing {input afterComma output : Remainder}
      (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterComma
        closingSpan output) :
      ParenthesizedPatternTupleTailParses nestedParses input [] closingSpan
        output
  | final {input afterComma afterElement output : Remainder}
      {element : Syntax.Pattern} (commaSpan closingSpan : SourceSpan)
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
      ParenthesizedPatternTupleTailParses nestedParses input [element]
        closingSpan output
  | next {input afterComma afterElement output : Remainder}
      {element : Syntax.Pattern} {elements : List Syntax.Pattern}
      (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedParses afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (tail : ParenthesizedPatternTupleTailParses nestedParses afterElement
        elements closingSpan output) :
      ParenthesizedPatternTupleTailParses nestedParses input
        (element :: elements) closingSpan output

/-- Exact prioritized grammar of an empty tuple, group, or tuple pattern. -/
inductive ParenthesizedPatternParses
    (nestedParses : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | empty {input afterOpening output : Remainder}
      (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterOpening
        closingSpan output) :
      ParenthesizedPatternParses nestedParses input
        (closeParenthesizedPattern openingSpan closingSpan []) output
  | group {input afterOpening afterElement output : Remainder}
      {element : Syntax.Pattern} (openingSpan closingSpan : SourceSpan)
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
      ParenthesizedPatternParses nestedParses input
        (closeParenthesizedPattern openingSpan closingSpan [element]) output
  | tuple {input afterOpening afterFirst output : Remainder}
      {first : Syntax.Pattern} {rest : List Syntax.Pattern}
      (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : nestedParses afterOpening first afterFirst)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tail : ParenthesizedPatternTupleTailParses nestedParses afterFirst rest
        closingSpan output) :
      ParenthesizedPatternParses nestedParses input
        (closeParenthesizedPattern openingSpan closingSpan (first :: rest))
        output

end Solcore.Syntax.DeclarativeGrammar
