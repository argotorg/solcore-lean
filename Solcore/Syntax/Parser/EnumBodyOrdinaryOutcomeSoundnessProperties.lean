import Solcore.Syntax.DeclarativeEnumBodyOutcomeProperties
import Solcore.Syntax.Parser.EnumBodyOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.EnumBodyOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for canonical enum bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

/-- Package executable enum-body success and exact rejection. -/
theorem enumBody_ordinaryOutcome_sound :
    (∀ {input output : State} {body : EnumBody},
      enumBody input = .ok body output →
        DeclarativeGrammar.EnumBodyOrdinaryOutcomeParses
          input.declarativeRemainder (body.span, body.constructors)
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      enumBody input = .reject failure rejected →
        DeclarativeGrammar.EnumBodyRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨enumBody_success_ordinaryOutcome_sound,
    enumBody_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive enum-body ordinary outcomes. -/
theorem enumBody_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.EnumBodyOrdinaryOutcomeParses
      DeclarativeGrammar.EnumBodyRejects :=
  DeclarativeGrammar.enumBodyDeterministicOutcomeSpec

end Solcore.Syntax.Parser.EnumInternals
