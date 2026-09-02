import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for maximal export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary export-path success is the existing exact maximal path grammar. -/
abbrev ExportPathOrdinaryParses := ExportPathParses

/-- An export path can reject only at its required first checked identifier. -/
inductive ExportPathRejects : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (identifierRejected : IdentifierRejects input rejected) :
      ExportPathRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
