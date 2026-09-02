import Solcore.Syntax.DeclarativeFunctionSignatureExactnessProperties
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

/-- Re-export complete location-independent signature exactness. -/
theorem functionSignature_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FunctionSignatureOrdinaryParses
      DeclarativeGrammar.FunctionSignatureRejects :=
  DeclarativeGrammar.functionSignatureExactOutcomeSpec

/-- At any executable location, two successful signatures have the same AST
and final declarative remainder. -/
theorem functionSignature_success_result_unique
    (location : FunctionLocation)
    {input leftOutput rightOutput : State}
    {left right : FunctionSignature}
    (leftResult : functionSignature location input = .ok left leftOutput)
    (rightResult : functionSignature location input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionSignatureOrdinaryParses.result_unique
    (functionSignature_success_ordinaryOutcome_sound location leftResult)
    (functionSignature_success_ordinaryOutcome_sound location rightResult)

/-- At any executable location, two signature rejections have the same
declarative endpoint. -/
theorem functionSignature_reject_output_unique
    (location : FunctionLocation)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : functionSignature location input =
      .reject leftFailure leftOutput)
    (rightResult : functionSignature location input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionSignatureRejects.output_unique
    (functionSignature_reject_ordinaryOutcome_sound location leftResult)
    (functionSignature_reject_ordinaryOutcome_sound location rightResult)

end Solcore.Syntax.Parser
