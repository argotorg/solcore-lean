import Solcore.Syntax.DeclarativeConstructorSelectionOutcomeGrammar
import Solcore.Syntax.DeclarativeSelectorNameOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for export names. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact evidence for a token kind at the current export-name cursor. -/
def ExportNameTokenPresentAt (input : Remainder) (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := kind
  }

/-- Ordinary export-name success is the existing exact prioritized grammar. -/
abbrev ExportNameOrdinaryParses := ExportNameParses

/-- Exact first rejecting stage of one prioritized export-name attempt. -/
inductive ExportNameRejects : Remainder → Remainder → Prop where
  | operatorRejected {input rejected : Remainder}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star))
      (openingPresent : ExportNameTokenPresentAt input
        (.symbol .leftParen))
      (selectorRejected : SelectorNameRejects input rejected) :
      ExportNameRejects input rejected
  | identifierRejected {input rejected : Remainder}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star))
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (nameRejected : IdentifierRejects input rejected) :
      ExportNameRejects input rejected
  | constructorsRejected {input afterName rejected : Remainder}
      {name : Syntax.Identifier}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star))
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (nameParsed : IdentifierParses input name afterName)
      (openingPresent : ExportNameTokenPresentAt afterName
        (.symbol .leftParen))
      (selectionRejected : ConstructorSelectionRejects afterName rejected) :
      ExportNameRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
