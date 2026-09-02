import Solcore.Syntax.DeclarativeSelectorNameOutcomeProperties
import Solcore.Syntax.Parser.SelectorNameOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectorNameOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for selector names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package selector-name success and exact prioritized rejection. -/
theorem selectorName_ordinaryOutcome_sound (context : ParseContext) :
    (∀ {input output : State} {selector : SelectorName},
      selectorName context input = .ok selector output →
        DeclarativeGrammar.SelectorNameOrdinaryParses
          input.declarativeRemainder selector output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      selectorName context input = .reject failure rejected →
        DeclarativeGrammar.SelectorNameRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨selectorName_success_ordinaryOutcome_sound context,
    selectorName_reject_ordinaryOutcome_sound context⟩

/-- Re-export deterministic and exclusive selector-name outcomes. -/
theorem selectorName_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.SelectorNameOrdinaryParses
      DeclarativeGrammar.SelectorNameRejects :=
  DeclarativeGrammar.selectorNameDeterministicOutcomeSpec

end Solcore.Syntax.Parser
