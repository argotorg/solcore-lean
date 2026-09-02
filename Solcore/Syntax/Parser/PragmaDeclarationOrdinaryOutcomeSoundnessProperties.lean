import Solcore.Syntax.DeclarativePragmaOutcomeProperties
import Solcore.Syntax.Parser.PragmaDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.PragmaDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for pragma declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable pragma success and rejection. -/
theorem pragmaDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : PragmaDecl},
      pragmaDecl input = .ok declaration output →
        DeclarativeGrammar.PragmaDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      pragmaDecl input = .reject failure rejected →
        DeclarativeGrammar.PragmaDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨pragmaDecl_success_ordinaryOutcome_sound,
    pragmaDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive parser-independent pragma outcomes. -/
theorem pragmaDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PragmaDeclOrdinaryParses
      DeclarativeGrammar.PragmaDeclRejects :=
  DeclarativeGrammar.pragmaDeclDeterministicOutcomeSpec

end Solcore.Syntax.Parser
