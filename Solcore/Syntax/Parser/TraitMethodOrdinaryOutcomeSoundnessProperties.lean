import Solcore.Syntax.DeclarativeTraitMethodOutcomeProperties
import Solcore.Syntax.Parser.TraitMethodOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.TraitMethodOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

/-- Package executable trait-method success and exact rejection. -/
theorem traitMethod_ordinaryOutcome_sound :
    (∀ {input output : State} {method : TraitMethod},
      traitMethod input = .ok method output →
        DeclarativeGrammar.TraitMethodOrdinaryParses
          input.declarativeRemainder method output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      traitMethod input = .reject failure rejected →
        DeclarativeGrammar.TraitMethodRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨traitMethod_success_ordinaryOutcome_sound,
    traitMethod_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad trait-method outcomes. -/
theorem traitMethod_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TraitMethodOrdinaryParses
      DeclarativeGrammar.TraitMethodRejects :=
  DeclarativeGrammar.traitMethodDeterministicOutcomeSpec

end Solcore.Syntax.Parser.TraitInternals
