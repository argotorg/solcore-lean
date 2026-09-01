import Solcore.Syntax.DeclarativeCoreExpressionPostfixGrammar
import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingOutcomeProperties

/-!
Parser-independent ordinary success and exact rejection for maximal Core
postfix expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The existing postfix grammar admits ordinary nested outcomes as-is. -/
abbrev PostfixTailOrdinaryParses := PostfixTailParses

/-- Exact rejection while extending an already parsed Core atom. -/
inductive PostfixTailRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | indexNestedRejected {input afterOpening rejected : Remainder}
      {base : Syntax.Expr} (openingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input
        openingSpan afterOpening)
      (nestedRejected : nestedRejects afterOpening rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected
  | indexClosingMissing {input afterOpening afterIndex : Remainder}
      {base index : Syntax.Expr} (openingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input
        openingSpan afterOpening)
      (indexParsed : nestedOrdinary afterOpening index afterIndex)
      (closingAbsent : TokenKindAbsentAt afterIndex.tokens afterIndex.endIndex
        afterIndex.cursor (.symbol .rightBracket)) :
      PostfixTailRejects nestedOrdinary nestedRejects input base afterIndex
  | indexLaterRejected
      {input afterOpening afterIndex afterClosing rejected : Remainder}
      {base index : Syntax.Expr} (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input
        openingSpan afterOpening)
      (indexParsed : nestedOrdinary afterOpening index afterIndex)
      (closingToken : ExactTokenParses (.symbol .rightBracket) afterIndex
        closingSpan afterClosing)
      (tailRejected : PostfixTailRejects nestedOrdinary nestedRejects
        afterClosing {
          span := SourceSpan.cover base.span closingSpan
          value := .index base (SourceSpan.cover openingSpan closingSpan) index
        } rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected
  | callArgumentsRejected {input rejected : Remainder}
      {base : Syntax.Expr} (openingSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftParen
      })
      (argumentsRejected : DelimitedListRejects .leftParen .rightParen true
        false nestedOrdinary nestedRejects input rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected
  | callLaterRejected {input afterArguments rejected : Remainder}
      {base : Syntax.Expr} {arguments : DelimitedList Syntax.Expr}
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (argumentsParsed : NoTrailingDelimitedListParses .leftParen .rightParen
        nestedOrdinary input arguments afterArguments)
      (tailRejected : PostfixTailRejects nestedOrdinary nestedRejects
        afterArguments {
          span := SourceSpan.cover base.span arguments.span
          value := .call base arguments
        } rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected
  | fieldNameRejected {input afterDot rejected : Remainder}
      {base : Syntax.Expr} (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameRejected : IdentifierRejects afterDot rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected
  | fieldLaterRejected {input afterDot afterName rejected : Remainder}
      {base : Syntax.Expr} {name : Syntax.Identifier} (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : IdentifierParses afterDot name afterName)
      (tailRejected : PostfixTailRejects nestedOrdinary nestedRejects afterName {
        span := SourceSpan.cover base.span name.span
        value := .field base dotSpan name
      } rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected

/-- The existing complete postfix grammar admits ordinary outcomes as-is. -/
abbrev ExpressionPostfixOrdinaryParses := ExpressionPostfixParses

/-- Exact rejection of a complete atom-plus-postfix attempt. -/
inductive ExpressionPostfixRejects
    (atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop)
    (atomRejects nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | atomRejected {input rejected : Remainder}
      (rejectedAtom : atomRejects input rejected) :
      ExpressionPostfixRejects atomOrdinary nestedOrdinary atomRejects
        nestedRejects input rejected
  | tailRejected {input afterAtom rejected : Remainder} {base : Syntax.Expr}
      (atomParsed : atomOrdinary input base afterAtom)
      (rejectedTail : PostfixTailRejects nestedOrdinary nestedRejects
        afterAtom base rejected) :
      ExpressionPostfixRejects atomOrdinary nestedOrdinary atomRejects
        nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
