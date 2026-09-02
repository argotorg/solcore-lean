import Solcore.Syntax.DeclarativeFunctionDeclarationExactnessProperties
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

/-- Re-export exact function-declaration outcomes from an exact isolated
`.allow` body. -/
theorem functionDecl_exactOutcomeSpec_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FunctionDeclOrdinaryParses
      DeclarativeGrammar.FunctionDeclRejects :=
  DeclarativeGrammar.functionDeclExactOutcomeSpecOfBody bodyOutcomes

/-- Fixed-fuel Core statement exactness discharges the executable function
declaration contract. -/
theorem functionDecl_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FunctionDeclOrdinaryParses
      DeclarativeGrammar.FunctionDeclRejects :=
  DeclarativeGrammar.functionDeclExactOutcomeSpecOfStatementFuel
    statementOutcomes

/-- With an exact isolated body, two executable function successes have the
same AST and final declarative remainder. -/
theorem functionDecl_success_result_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    (location : FunctionLocation)
    {input leftOutput rightOutput : State} {left right : FunctionDecl}
    (leftResult : functionDecl location input = .ok left leftOutput)
    (rightResult : functionDecl location input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionDeclOrdinaryParses.result_unique_of_exact_body
    bodyOutcomes (functionDecl_success_ordinaryOutcome_sound location leftResult)
    (functionDecl_success_ordinaryOutcome_sound location rightResult)

/-- With an exact isolated body, two executable function rejections have the
same declarative endpoint. -/
theorem functionDecl_reject_output_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    (location : FunctionLocation)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : functionDecl location input = .reject leftFailure leftOutput)
    (rightResult : functionDecl location input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionDeclRejects.output_unique_of_exact_body
    bodyOutcomes (functionDecl_reject_ordinaryOutcome_sound location leftResult)
    (functionDecl_reject_ordinaryOutcome_sound location rightResult)

end Solcore.Syntax.Parser
