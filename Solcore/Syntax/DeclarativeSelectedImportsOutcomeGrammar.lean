import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeSelectedImportOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary selected-import-list success is the existing exact nonempty,
allow-trailing braced-list grammar. -/
abbrev SelectedImportsOrdinaryParses := SelectedImportsParses

/-- Exact rejection of the required nonempty, allow-trailing braced list. -/
abbrev SelectedImportsRejects :=
  DelimitedListRejects .leftBrace .rightBrace false true
    SelectedImportOrdinaryParses SelectedImportRejects

end Solcore.Syntax.DeclarativeGrammar
