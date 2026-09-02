import Solcore.Syntax.DeclarativeFallbackDeclarationOutcomeProperties
import Solcore.Syntax.Parser.FallbackDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.FallbackDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for canonical fallback declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable fallback-declaration success and rejection. -/
theorem fallbackDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : FallbackDecl},
      fallbackDecl input = .ok declaration output →
        DeclarativeGrammar.FallbackDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      fallbackDecl input = .reject failure rejected →
        DeclarativeGrammar.FallbackDeclRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨fallbackDecl_success_ordinaryOutcome_sound,
    fallbackDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export the parser-independent deterministic fallback contract. -/
theorem fallbackDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.FallbackDeclOrdinaryParses
      DeclarativeGrammar.FallbackDeclRejects :=
  DeclarativeGrammar.fallbackDeclDeterministicOutcomeSpec

end Solcore.Syntax.Parser
