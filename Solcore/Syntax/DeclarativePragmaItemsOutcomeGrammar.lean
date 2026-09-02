import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for pragma item scanning. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact positive current-token guard used by pragma item dispatch. -/
def PragmaItemsTokenPresentAt (input : Remainder) (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := kind
  }

/-- Exact successful suffix after a pragma's first item. -/
inductive PragmaItemsTailOrdinaryParses :
    Remainder → List Syntax.Identifier → Remainder → Prop where
  | done {input : Remainder}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .comma)) :
      PragmaItemsTailOrdinaryParses input [] input
  | trailing {input afterComma : Remainder} (commaSpan : SourceSpan)
      (commaPresent : PragmaItemsTokenPresentAt input (.symbol .comma))
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (semicolonPresent : PragmaItemsTokenPresentAt afterComma
        (.symbol .semicolon)) :
      PragmaItemsTailOrdinaryParses input [] afterComma
  | next {input afterComma afterItem output : Remainder}
      {item : Syntax.Identifier} {items : List Syntax.Identifier}
      (commaSpan : SourceSpan)
      (commaPresent : PragmaItemsTokenPresentAt input (.symbol .comma))
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (semicolonAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .semicolon))
      (itemParsed : IdentifierParses afterComma item afterItem)
      (tailParsed : PragmaItemsTailOrdinaryParses afterItem items output) :
      PragmaItemsTailOrdinaryParses input (item :: items) output

/-- Exact first rejecting stage of a pragma item suffix. -/
inductive PragmaItemsTailRejects : Remainder → Remainder → Prop where
  | identifierRejected {input afterComma rejected : Remainder}
      (commaSpan : SourceSpan)
      (commaPresent : PragmaItemsTokenPresentAt input (.symbol .comma))
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (semicolonAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .semicolon))
      (itemRejected : IdentifierRejects afterComma rejected) :
      PragmaItemsTailRejects input rejected
  | laterRejected {input afterComma afterItem rejected : Remainder}
      {item : Syntax.Identifier} (commaSpan : SourceSpan)
      (commaPresent : PragmaItemsTokenPresentAt input (.symbol .comma))
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (semicolonAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .semicolon))
      (itemParsed : IdentifierParses afterComma item afterItem)
      (tailRejected : PragmaItemsTailRejects afterItem rejected) :
      PragmaItemsTailRejects input rejected

/-- Exact successful scan of all pragma items before the semicolon. -/
inductive PragmaItemsOrdinaryParses :
    Remainder → List Syntax.Identifier → Remainder → Prop where
  | empty {input : Remainder}
      (semicolonPresent : PragmaItemsTokenPresentAt input
        (.symbol .semicolon)) :
      PragmaItemsOrdinaryParses input [] input
  | nonempty {input afterFirst output : Remainder}
      {first : Syntax.Identifier} {rest : List Syntax.Identifier}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (firstParsed : IdentifierParses input first afterFirst)
      (tailParsed : PragmaItemsTailOrdinaryParses afterFirst rest output) :
      PragmaItemsOrdinaryParses input (first :: rest) output

/-- Exact first rejecting stage of the complete pragma item scan. -/
inductive PragmaItemsRejects : Remainder → Remainder → Prop where
  | firstIdentifierRejected {input rejected : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (firstRejected : IdentifierRejects input rejected) :
      PragmaItemsRejects input rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.Identifier}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon))
      (firstParsed : IdentifierParses input first afterFirst)
      (tailRejected : PragmaItemsTailRejects afterFirst rejected) :
      PragmaItemsRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
