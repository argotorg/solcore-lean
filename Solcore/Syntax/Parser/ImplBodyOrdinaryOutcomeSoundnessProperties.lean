import Solcore.Syntax.DeclarativeImplBodyOutcomeProperties
import Solcore.Syntax.Parser.ImplBodyOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImplBodyOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for implementation bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- Package executable implementation-body success and exact rejection. -/
theorem implBody_ordinaryOutcome_sound :
    (∀ {input output : State} {body : ImplBody},
      implBody input = .ok body output →
        DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
          input.declarativeRemainder (body.span, body.methods)
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      implBody input = .reject failure rejected →
        DeclarativeGrammar.ImplBodyRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨implBody_success_ordinaryOutcome_sound,
    implBody_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive implementation-body outcomes. -/
theorem implBody_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects :=
  DeclarativeGrammar.implBodyDeterministicOutcomeSpec

end Solcore.Syntax.Parser.ImplInternals
