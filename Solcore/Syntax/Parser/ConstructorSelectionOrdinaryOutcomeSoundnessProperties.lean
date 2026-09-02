import Solcore.Syntax.DeclarativeConstructorSelectionOutcomeProperties
import Solcore.Syntax.Parser.ConstructorSelectionOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ConstructorSelectionSoundnessProperties

/-! Complete executable broad ordinary outcomes for constructor selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export constructor-selection success as a broad ordinary outcome. -/
theorem constructorSelection_success_ordinaryOutcome_sound
    {input output : State} {selection : ConstructorSelection}
    (result : ExportInternals.constructorSelection input =
      .ok selection output) :
    DeclarativeGrammar.ConstructorSelectionOrdinaryParses
      input.declarativeRemainder selection output.declarativeRemainder :=
  constructorSelection_success_sound result

/-- Package constructor-selection success and exact prioritized rejection. -/
theorem constructorSelection_ordinaryOutcome_sound :
    (∀ {input output : State} {selection : ConstructorSelection},
      ExportInternals.constructorSelection input = .ok selection output →
        DeclarativeGrammar.ConstructorSelectionOrdinaryParses
          input.declarativeRemainder selection output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.constructorSelection input = .reject failure rejected →
        DeclarativeGrammar.ConstructorSelectionRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨constructorSelection_success_ordinaryOutcome_sound,
    constructorSelection_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive constructor-selection outcomes. -/
theorem constructorSelection_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ConstructorSelectionOrdinaryParses
      DeclarativeGrammar.ConstructorSelectionRejects :=
  DeclarativeGrammar.constructorSelectionDeterministicOutcomeSpec

end Solcore.Syntax.Parser
