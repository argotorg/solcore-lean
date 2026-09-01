import Solcore.Syntax.DeclarativeCoreBlockGrammar

/-!
Parser-independent ordinary success and exact rejection for raw Core blocks.

Ordinary success deliberately omits `CoreBlockTailsValid`: the executable tail
validator reports violations with diagnostics while retaining the successful
block, token window, and cursor.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive success of a raw Core block.  The policy is retained
to identify the executable parser, but diagnostic tail validation does not
change the accepted syntax value or remainder. -/
inductive CoreBlockOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (policy : CoreBlockTailPolicy) :
    Remainder → Syntax.Block → Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {body : List Syntax.Statement} (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (bodyParsed : CoreBlockItemsParses statementOrdinary afterOpening body
        closingSpan output) :
      CoreBlockOrdinaryParses statementOrdinary policy input {
        span := SourceSpan.cover openingSpan closingSpan
        value := body
      } output

/-- Exact rejection after a Core block opening brace has been consumed. -/
inductive CoreBlockItemsRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | missingClose {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (atEnd : input.endIndex ≤ input.cursor) :
      CoreBlockItemsRejects statementOrdinary statementRejects input input
  | statementRejected {input rejected : Remainder}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementRejected : statementRejects input rejected) :
      CoreBlockItemsRejects statementOrdinary statementRejects input rejected
  | laterRejected {input afterStatement rejected : Remainder}
      {statement : Syntax.Statement}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementOrdinary input statement afterStatement)
      (progress : input.cursor < afterStatement.cursor)
      (tailRejected : CoreBlockItemsRejects statementOrdinary statementRejects
        afterStatement rejected) :
      CoreBlockItemsRejects statementOrdinary statementRejects input rejected

/-- Exact rejection of a complete raw Core block. -/
inductive CoreBlockRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (policy : CoreBlockTailPolicy) : Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace)) :
      CoreBlockRejects statementOrdinary statementRejects policy input input
  | itemsRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) input
        openingSpan afterOpening)
      (itemsRejected : CoreBlockItemsRejects statementOrdinary statementRejects
        afterOpening rejected) :
      CoreBlockRejects statementOrdinary statementRejects policy input rejected

end Solcore.Syntax.DeclarativeGrammar
