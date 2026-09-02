import Solcore.Syntax.DeclarativeSelectedAliasOutcomeGrammar
import Solcore.Syntax.DeclarativeSelectorNameOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for one selected import. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary selected-import success is the existing exact source/alias
grammar, including its AST span equation and final remainder. -/
abbrev SelectedImportOrdinaryParses := SelectedImportParses

/-- Exact first rejecting stage of one selected import. -/
inductive SelectedImportRejects : Remainder → Remainder → Prop where
  | sourceRejected {input rejected : Remainder}
      (sourceRejected : SelectorNameRejects input rejected) :
      SelectedImportRejects input rejected
  | aliasRejected {input afterSource rejected : Remainder}
      {source : Syntax.SelectorName}
      (sourceParsed : SelectorNameOrdinaryParses input source afterSource)
      (aliasRejected : SelectedAliasRejects afterSource rejected) :
      SelectedImportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
