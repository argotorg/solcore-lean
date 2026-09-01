import Solcore.Syntax.DeclarativeYulBlockGrammar

/-!
Parser-independent ordinary rejection traces for braced inline-Yul blocks.

Successful prefixes use a broad ordinary statement relation.  A failed item
retains its exact rejected remainder, while the block loop records closing
brace priority, the active-window boundary, and strict statement progress.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary block success is the existing exact block grammar instantiated
with an ordinary statement relation. -/
abbrev YulBlockOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulBlockParses statementOrdinary

/-- Parser-independent value carrier for one parsed Yul block. -/
structure YulBlockValue where
  span : SourceSpan
  body : List Syntax.YulStmt
  deriving Repr

/-- Package the exact block grammar as a three-place outcome relation. -/
def YulBlockOutcomeParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (input : Remainder) (value : YulBlockValue)
    (output : Remainder) : Prop :=
  YulBlockOrdinaryParses statementOrdinary input value.span value.body output

/-- Exact rejection after a block opening brace has already been consumed. -/
inductive YulBlockItemsRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | missingClose {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (atEnd : input.endIndex ≤ input.cursor) :
      YulBlockItemsRejects statementOrdinary statementRejects input input
  | statementRejected {input rejected : Remainder}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (rejectedStatement : statementRejects input rejected) :
      YulBlockItemsRejects statementOrdinary statementRejects input rejected
  | laterRejected {input afterStatement rejected : Remainder}
      {statement : Syntax.YulStmt}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementOrdinary input statement afterStatement)
      (progress : input.cursor < afterStatement.cursor)
      (tailRejected : YulBlockItemsRejects statementOrdinary statementRejects
        afterStatement rejected) :
      YulBlockItemsRejects statementOrdinary statementRejects input rejected

/-- Exact rejection of a complete braced inline-Yul block. -/
inductive YulBlockRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace)) :
      YulBlockRejects statementOrdinary statementRejects input input
  | itemsRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) input
        openingSpan afterOpening)
      (itemsRejected : YulBlockItemsRejects statementOrdinary statementRejects
        afterOpening rejected) :
      YulBlockRejects statementOrdinary statementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
