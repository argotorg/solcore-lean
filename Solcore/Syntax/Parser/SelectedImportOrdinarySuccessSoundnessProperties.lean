import Solcore.Syntax.DeclarativeSelectedImportOutcomeGrammar
import Solcore.Syntax.Parser.SelectedImportSoundnessProperties

/-! Broad ordinary-success soundness for one selected import. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-import success preserves its exact source,
optional alias, AST span, and final remainder. -/
theorem selectedImport_success_ordinaryOutcome_sound
    {input output : State} {selection : SelectedImport}
    (result : selectedImport input = .ok selection output) :
    DeclarativeGrammar.SelectedImportOrdinaryParses
      input.declarativeRemainder selection output.declarativeRemainder :=
  selectedImport_success_sound result

end Solcore.Syntax.Parser
