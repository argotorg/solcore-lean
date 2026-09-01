import Solcore.Syntax.DeclarativeCoreCollectionAtomGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes for the guarded Core parenthesized atom.

The rejection relations follow the bespoke `tupleTail` loop rather than a
generic list abstraction, so the single-element group/tuple distinction and
the parser's comma/closing priorities remain explicit.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The existing exact parenthesized grammar admits arbitrary ordinary nested
expression outcomes as-is. -/
abbrev ParenthesizedExpressionOrdinaryParses :=
  ParenthesizedExpressionParses

/-- Exact ordinary rejection after a comma selected the tuple-tail loop. -/
inductive ParenthesizedTupleTailRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | elementRejected {input afterComma rejected : Remainder}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementRejected : nestedRejects afterComma rejected) :
      ParenthesizedTupleTailRejects nestedOrdinary nestedRejects input
        rejected
  | closingMissing {input afterComma afterElement : Remainder}
      {element : Syntax.Expr} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsentAfterComma : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedOrdinary afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens
        afterElement.endIndex afterElement.cursor (.symbol .comma))
      (closingAbsent : TokenKindAbsentAt afterElement.tokens
        afterElement.endIndex afterElement.cursor (.symbol .rightParen)) :
      ParenthesizedTupleTailRejects nestedOrdinary nestedRejects input
        afterElement
  | laterRejected {input afterComma afterElement rejected : Remainder}
      {element : Syntax.Expr} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedOrdinary afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (tailRejected : ParenthesizedTupleTailRejects nestedOrdinary
        nestedRejects afterElement rejected) :
      ParenthesizedTupleTailRejects nestedOrdinary nestedRejects input
        rejected

/-- Exact rejection after the atom dispatcher selected a present `(`. -/
inductive ParenthesizedExpressionRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | firstRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstRejected : nestedRejects afterOpening rejected) :
      ParenthesizedExpressionRejects nestedOrdinary nestedRejects input
        rejected
  | closingMissing {input afterOpening afterFirst : Remainder}
      {first : Syntax.Expr} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsentAfterOpening : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : nestedOrdinary afterOpening first afterFirst)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (commaAbsent : TokenKindAbsentAt afterFirst.tokens afterFirst.endIndex
        afterFirst.cursor (.symbol .comma))
      (closingAbsent : TokenKindAbsentAt afterFirst.tokens afterFirst.endIndex
        afterFirst.cursor (.symbol .rightParen)) :
      ParenthesizedExpressionRejects nestedOrdinary nestedRejects input
        afterFirst
  | tailRejected {input afterOpening afterFirst rejected : Remainder}
      {first : Syntax.Expr} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : nestedOrdinary afterOpening first afterFirst)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tailRejected : ParenthesizedTupleTailRejects nestedOrdinary
        nestedRejects afterFirst rejected) :
      ParenthesizedExpressionRejects nestedOrdinary nestedRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
