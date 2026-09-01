import Solcore.Syntax.DeclarativeCorePatternBasicGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes for Core parenthesized patterns.

The tuple-tail rejection relation starts after the executable comma guard has
selected the tail.  Fuel exhaustion and non-progress are invariant failures,
so neither is represented by an ordinary relation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary parenthesized-pattern success is the existing exact grammar. -/
abbrev ParenthesizedPatternOrdinaryParses := ParenthesizedPatternParses

/-- Exact ordinary rejection after a comma selected the tuple-tail loop. -/
inductive ParenthesizedPatternTupleTailRejects
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | elementRejected {input afterComma rejected : Remainder}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementRejected : nestedRejects afterComma rejected) :
      ParenthesizedPatternTupleTailRejects nestedOrdinary nestedRejects input
        rejected
  | closingMissing {input afterComma afterElement : Remainder}
      {element : Syntax.Pattern} (commaSpan : SourceSpan)
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
      ParenthesizedPatternTupleTailRejects nestedOrdinary nestedRejects input
        afterElement
  | laterRejected {input afterComma afterElement rejected : Remainder}
      {element : Syntax.Pattern} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedOrdinary afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (tailRejected : ParenthesizedPatternTupleTailRejects nestedOrdinary
        nestedRejects afterElement rejected) :
      ParenthesizedPatternTupleTailRejects nestedOrdinary nestedRejects input
        rejected

/-- Exact ordinary rejection of the public parenthesized-pattern parser. -/
inductive ParenthesizedPatternRejects
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      ParenthesizedPatternRejects nestedOrdinary nestedRejects input input
  | firstRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstRejected : nestedRejects afterOpening rejected) :
      ParenthesizedPatternRejects nestedOrdinary nestedRejects input rejected
  | closingMissing {input afterOpening afterFirst : Remainder}
      {first : Syntax.Pattern} (openingSpan : SourceSpan)
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
      ParenthesizedPatternRejects nestedOrdinary nestedRejects input afterFirst
  | tailRejected {input afterOpening afterFirst rejected : Remainder}
      {first : Syntax.Pattern} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : nestedOrdinary afterOpening first afterFirst)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tailRejected : ParenthesizedPatternTupleTailRejects nestedOrdinary
        nestedRejects afterFirst rejected) :
      ParenthesizedPatternRejects nestedOrdinary nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
