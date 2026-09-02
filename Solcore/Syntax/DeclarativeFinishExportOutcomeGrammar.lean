import Solcore.Syntax.DeclarativeGrammar

/-! Parser-independent broad ordinary outcomes for finishing an export. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary export finishing is the existing exact semicolon grammar. -/
abbrev FinishExportOrdinaryParses := FinishExportParses

/-- An export finish rejects exactly when its required semicolon is absent. -/
inductive FinishExportRejects : Remainder → Remainder → Prop where
  | semicolonMissing {input : Remainder}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon)) :
      FinishExportRejects input input

end Solcore.Syntax.DeclarativeGrammar
