import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeExportNameOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary export-selection success is the existing exact prioritized
grammar. -/
abbrev ExportSelectionOrdinaryParses := ExportSelectionParses

/-- A non-wildcard export selection rejects only in its braced name list. -/
inductive ExportSelectionRejects : Remainder → Remainder → Prop where
  | selectedRejected {input rejected : Remainder}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star))
      (itemsRejected : DelimitedListRejects .leftBrace .rightBrace true true
        ExportNameOrdinaryParses ExportNameRejects input rejected) :
      ExportSelectionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
