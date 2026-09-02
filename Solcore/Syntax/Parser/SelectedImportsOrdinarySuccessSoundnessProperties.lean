import Solcore.Syntax.DeclarativeSelectedImportsOutcomeGrammar
import Solcore.Syntax.Parser.SelectedImportsSoundnessProperties

/-! Broad ordinary-success soundness for selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-import-list success preserves the exact
nonempty allow-trailing list, source order, span, and final remainder. -/
theorem selectedImports_success_ordinaryOutcome_sound
    {input output : State}
    {selections : NonemptyDelimitedList SelectedImport}
    (result : ImportInternals.selectedImports input = .ok selections output) :
    DeclarativeGrammar.SelectedImportsOrdinaryParses
      input.declarativeRemainder selections output.declarativeRemainder :=
  selectedImports_success_sound result

end Solcore.Syntax.Parser
