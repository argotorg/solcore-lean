import Solcore.Syntax.DeclarativeCoreCollectionAtomGrammar
import Solcore.Syntax.Parser.Diagnostic

/-! Independent prioritized parenthesized success traces. Tail results contain
only newly read forward elements, their closing span, and ordered child events.
Fuel and the already-accumulated reverse prefix are deliberately absent. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ParenthesizedTupleTailTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → List Syntax.Expr → SourceSpan → Remainder → List ParseDiagnostic → Prop where
  | trailing {input afterComma output : Remainder} (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterComma closingSpan output) :
      ParenthesizedTupleTailTraceParses elementTrace source endByte input [] closingSpan output []
  | final {input afterComma afterElement output : Remainder} {element : Syntax.Expr}
      {events : List ParseDiagnostic} (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : elementTrace source endByte afterComma element afterElement events)
      (progress : afterComma.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .comma))
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterElement closingSpan output) :
      ParenthesizedTupleTailTraceParses elementTrace source endByte input [element] closingSpan output events
  | next {input afterComma afterElement output : Remainder} {element : Syntax.Expr} {elements : List Syntax.Expr}
      {headEvents tailEvents : List ParseDiagnostic} (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : elementTrace source endByte afterComma element afterElement headEvents)
      (progress : afterComma.cursor < afterElement.cursor)
      (tail : ParenthesizedTupleTailTraceParses elementTrace source endByte afterElement elements closingSpan output tailEvents) :
      ParenthesizedTupleTailTraceParses elementTrace source endByte input (element :: elements) closingSpan output
        (headEvents ++ tailEvents)

inductive ParenthesizedExpressionTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | empty {input afterOpening output : Remainder} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterOpening closingSpan output) :
      ParenthesizedExpressionTraceParses elementTrace source endByte input
        (closeParenthesizedExpression openingSpan closingSpan []) output []
  | group {input afterOpening afterElement output : Remainder} {element : Syntax.Expr}
      {events : List ParseDiagnostic} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (elementParsed : elementTrace source endByte afterOpening element afterElement events)
      (progress : afterOpening.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens afterElement.endIndex afterElement.cursor (.symbol .comma))
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterElement closingSpan output) :
      ParenthesizedExpressionTraceParses elementTrace source endByte input
        (closeParenthesizedExpression openingSpan closingSpan [element]) output events
  | tuple {input afterOpening afterFirst output : Remainder} {first : Syntax.Expr} {rest : List Syntax.Expr}
      {headEvents tailEvents : List ParseDiagnostic} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : elementTrace source endByte afterOpening first afterFirst headEvents)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tail : ParenthesizedTupleTailTraceParses elementTrace source endByte afterFirst rest closingSpan output tailEvents) :
      ParenthesizedExpressionTraceParses elementTrace source endByte input
        (closeParenthesizedExpression openingSpan closingSpan (first :: rest)) output (headEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
