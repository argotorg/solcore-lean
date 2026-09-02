import Solcore.Syntax.DeclarativeFunctionSignatureOutcomeProperties
import Solcore.Syntax.Parser.FunctionSignatureOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.FunctionSignatureOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for named-function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable signature success and rejection at one location. -/
theorem functionSignature_ordinaryOutcome_sound
    (location : FunctionLocation) :
    (∀ {input output : State} {signature : FunctionSignature},
      functionSignature location input = .ok signature output →
        DeclarativeGrammar.FunctionSignatureOrdinaryParses
          input.declarativeRemainder signature output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      functionSignature location input = .reject failure rejected →
        DeclarativeGrammar.FunctionSignatureRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨functionSignature_success_ordinaryOutcome_sound location,
    functionSignature_reject_ordinaryOutcome_sound location⟩

/-- Re-export the location-independent deterministic signature contract. -/
theorem functionSignature_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.FunctionSignatureOrdinaryParses
      DeclarativeGrammar.FunctionSignatureRejects :=
  DeclarativeGrammar.functionSignatureDeterministicOutcomeSpec

end Solcore.Syntax.Parser
