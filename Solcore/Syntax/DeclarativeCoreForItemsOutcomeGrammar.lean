import Solcore.Syntax.DeclarativeCoreForItemOutcomeGrammar

/-!
Diagnostic-inclusive ordinary success and exact rejection for Core `for`
header item lists.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary forward suffix after an already parsed Core `for` item. -/
abbrev ForItemsTailOrdinaryParses := ForItemsTailParses

/-- Exact rejection of the comma-led tail, including the committed comma
immediately followed by the enclosing stop symbol. -/
inductive ForItemsTailRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (stop : Symbol) : Remainder → Remainder → Prop where
  | stopAfterComma {input afterComma : Remainder}
      (commaSpan stopSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (stopCurrent : TokenAt afterComma.tokens afterComma.endIndex
        afterComma.cursor { span := stopSpan, value := .symbol stop }) :
      ForItemsTailRejects expressionOrdinary expressionRejects stop input
        afterComma
  | itemRejected {input afterComma rejected : Remainder}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (stopAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol stop))
      (itemRejected : ForItemRejects expressionOrdinary expressionRejects
        TypeExprRejects afterComma rejected) :
      ForItemsTailRejects expressionOrdinary expressionRejects stop input
        rejected
  | laterRejected {input afterComma afterItem rejected : Remainder}
      {item : Syntax.ForItem} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (stopAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol stop))
      (itemParsed : ForItemOrdinaryParses expressionOrdinary afterComma item
        afterItem)
      (progress : afterComma.cursor < afterItem.cursor)
      (tailRejected : ForItemsTailRejects expressionOrdinary expressionRejects
        stop afterItem rejected) :
      ForItemsTailRejects expressionOrdinary expressionRejects stop input
        rejected

/-- Ordinary public Core `for` header item list. -/
abbrev ForItemsOrdinaryParses := ForItemsParses

/-- Exact rejection of the public stop-prioritized item list. -/
inductive ForItemsRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (stop : Symbol) : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (stopAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol stop))
      (firstRejected : ForItemRejects expressionOrdinary expressionRejects
        TypeExprRejects input rejected) :
      ForItemsRejects expressionOrdinary expressionRejects stop input rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.ForItem}
      (stopAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol stop))
      (firstParsed : ForItemOrdinaryParses expressionOrdinary input first
        afterFirst)
      (progress : input.cursor < afterFirst.cursor)
      (tailRejected : ForItemsTailRejects expressionOrdinary expressionRejects
        stop afterFirst rejected) :
      ForItemsRejects expressionOrdinary expressionRejects stop input rejected

end Solcore.Syntax.DeclarativeGrammar
