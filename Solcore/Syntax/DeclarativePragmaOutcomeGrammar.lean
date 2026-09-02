import Solcore.Syntax.DeclarativePragmaItemsOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for complete pragmas. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad pragma success in executable stage order. -/
inductive PragmaDeclOrdinaryParses :
    Remainder → Syntax.PragmaDecl → Remainder → Prop where
  | parsed {input afterKeyword afterName afterItems output : Remainder}
      {name : Syntax.Identifier} {items : List Syntax.Identifier}
      (keywordSpan semicolonSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input keywordSpan
        afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (itemsParsed : PragmaItemsOrdinaryParses afterName items afterItems)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) afterItems
        semicolonSpan output) :
      PragmaDeclOrdinaryParses input {
        span := SourceSpan.cover keywordSpan semicolonSpan
        value := { name, items }
      } output

/-- Exact first rejecting stage of one complete pragma attempt. -/
inductive PragmaDeclRejects : Remainder → Remainder → Prop where
  | keywordMissing {input : Remainder}
      (keywordAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .pragmaKw)) :
      PragmaDeclRejects input input
  | nameRejected {input afterKeyword rejected : Remainder}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input keywordSpan
        afterKeyword)
      (nameRejected : IdentifierRejects afterKeyword rejected) :
      PragmaDeclRejects input rejected
  | itemsRejected {input afterKeyword afterName rejected : Remainder}
      {name : Syntax.Identifier} (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input keywordSpan
        afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (itemsRejected : PragmaItemsRejects afterName rejected) :
      PragmaDeclRejects input rejected
  | semicolonMissing
      {input afterKeyword afterName afterItems : Remainder}
      {name : Syntax.Identifier} {items : List Syntax.Identifier}
      (keywordSpan : SourceSpan)
      (keywordParsed : ExactTokenParses (.keyword .pragmaKw) input keywordSpan
        afterKeyword)
      (nameParsed : IdentifierParses afterKeyword name afterName)
      (itemsParsed : PragmaItemsOrdinaryParses afterName items afterItems)
      (semicolonAbsent : TokenKindAbsentAt afterItems.tokens
        afterItems.endIndex afterItems.cursor (.symbol .semicolon)) :
      PragmaDeclRejects input afterItems

end Solcore.Syntax.DeclarativeGrammar
