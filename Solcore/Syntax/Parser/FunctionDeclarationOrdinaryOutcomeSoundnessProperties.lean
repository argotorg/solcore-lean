import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeProperties
import Solcore.Syntax.Parser.FunctionDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.FunctionDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for named-function declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable declaration success and rejection. -/
theorem functionDecl_ordinaryOutcome_sound
    (location : FunctionLocation) :
    (∀ {input output : State} {declaration : FunctionDecl},
      functionDecl location input = .ok declaration output →
        DeclarativeGrammar.FunctionDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      functionDecl location input = .reject failure rejected →
        DeclarativeGrammar.FunctionDeclRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨functionDecl_success_ordinaryOutcome_sound location,
    functionDecl_reject_ordinaryOutcome_sound location⟩

/-- Re-export the location-independent deterministic declaration contract. -/
theorem functionDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.FunctionDeclOrdinaryParses
      DeclarativeGrammar.FunctionDeclRejects :=
  DeclarativeGrammar.functionDeclDeterministicOutcomeSpec

end Solcore.Syntax.Parser
