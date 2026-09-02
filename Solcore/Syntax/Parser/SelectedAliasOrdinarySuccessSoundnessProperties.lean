import Solcore.Syntax.DeclarativeSelectedAliasOutcomeGrammar
import Solcore.Syntax.Parser.SelectedImportSoundnessProperties

/-! Broad ordinary-success soundness for optional selected-import aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-alias success follows the existing exact
prioritized alias grammar without a diagnostic-free premise. -/
theorem selectedAlias_success_ordinaryOutcome_sound
    {input output : State} {alias : Option Identifier}
    (result : ImportInternals.selectedAlias input = .ok alias output) :
    DeclarativeGrammar.SelectedAliasOrdinaryParses
      input.declarativeRemainder alias output.declarativeRemainder :=
  selectedAlias_success_sound result

end Solcore.Syntax.Parser
