import Solcore.Syntax.DeclarativeTraitBodyOutcomeProperties
import Solcore.Syntax.Parser.TraitBodyOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.TraitBodyOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for trait bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

/-- Package executable trait-body success and exact rejection. -/
theorem traitBody_ordinaryOutcome_sound :
    (∀ {input output : State} {body : TraitBody},
      traitBody input = .ok body output →
        DeclarativeGrammar.TraitBodyOrdinaryOutcomeParses
          input.declarativeRemainder (body.span, body.methods)
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      traitBody input = .reject failure rejected →
        DeclarativeGrammar.TraitBodyRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨traitBody_success_ordinaryOutcome_sound,
    traitBody_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad trait-body outcomes. -/
theorem traitBody_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TraitBodyOrdinaryOutcomeParses
      DeclarativeGrammar.TraitBodyRejects :=
  DeclarativeGrammar.traitBodyDeterministicOutcomeSpec

end Solcore.Syntax.Parser.TraitInternals
