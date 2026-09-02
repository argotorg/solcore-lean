import Solcore.Syntax.DeclarativeSelectedAliasOutcomeProperties
import Solcore.Syntax.Parser.SelectedAliasOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectedAliasOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for selected-import aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package selected-alias success and exact committed rejection. -/
theorem selectedAlias_ordinaryOutcome_sound :
    (∀ {input output : State} {alias : Option Identifier},
      ImportInternals.selectedAlias input = .ok alias output →
        DeclarativeGrammar.SelectedAliasOrdinaryParses
          input.declarativeRemainder alias output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.selectedAlias input = .reject failure rejected →
        DeclarativeGrammar.SelectedAliasRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨selectedAlias_success_ordinaryOutcome_sound,
    selectedAlias_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive selected-alias outcomes. -/
theorem selectedAlias_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.SelectedAliasOrdinaryParses
      DeclarativeGrammar.SelectedAliasRejects :=
  DeclarativeGrammar.selectedAliasDeterministicOutcomeSpec

end Solcore.Syntax.Parser
