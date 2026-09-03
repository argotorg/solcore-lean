import Solcore.Syntax.DeclarativeCoreDeclarationExactnessProperties
import Solcore.Syntax.Parser.ConstructorDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FallbackDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionDeclarationOrdinaryOutcomeSoundnessProperties

/-! Unconditional executable exactness for function and entry declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Named-function exactness requires no recursive body premise. -/
theorem functionDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FunctionDeclOrdinaryParses
      DeclarativeGrammar.FunctionDeclRejects :=
  DeclarativeGrammar.functionDeclExactOutcomeSpec

/-- Function successes at a fixed location agree on their AST and remainder. -/
theorem functionDecl_success_result_unique (location : FunctionLocation)
    {input leftOutput rightOutput : State} {left right : FunctionDecl}
    (leftResult : functionDecl location input = .ok left leftOutput)
    (rightResult : functionDecl location input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  functionDecl_exactOutcomeSpec.successResultUnique
    (functionDecl_success_ordinaryOutcome_sound location leftResult)
    (functionDecl_success_ordinaryOutcome_sound location rightResult)

/-- Function rejections at a fixed location agree on their declarative endpoint. -/
theorem functionDecl_reject_output_unique (location : FunctionLocation)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : functionDecl location input = .reject leftFailure leftOutput)
    (rightResult : functionDecl location input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  functionDecl_exactOutcomeSpec.rejectOutputUnique
    (functionDecl_reject_ordinaryOutcome_sound location leftResult)
    (functionDecl_reject_ordinaryOutcome_sound location rightResult)

/-- Constructor exactness requires no recursive body premise. -/
theorem constructorDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ConstructorDeclOrdinaryParses
      DeclarativeGrammar.ConstructorDeclRejects :=
  DeclarativeGrammar.constructorDeclExactOutcomeSpec

/-- Constructor successes agree on their complete AST and remainder. -/
theorem constructorDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : ConstructorDecl}
    (leftResult : constructorDecl input = .ok left leftOutput)
    (rightResult : constructorDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  constructorDecl_exactOutcomeSpec.successResultUnique
    (constructorDecl_success_ordinaryOutcome_sound leftResult)
    (constructorDecl_success_ordinaryOutcome_sound rightResult)

/-- Constructor rejections agree on their complete declarative endpoint. -/
theorem constructorDecl_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : constructorDecl input = .reject leftFailure leftOutput)
    (rightResult : constructorDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  constructorDecl_exactOutcomeSpec.rejectOutputUnique
    (constructorDecl_reject_ordinaryOutcome_sound leftResult)
    (constructorDecl_reject_ordinaryOutcome_sound rightResult)

/-- Fallback-declaration exactness requires no recursive body premise. -/
theorem fallbackDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FallbackDeclOrdinaryParses
      DeclarativeGrammar.FallbackDeclRejects :=
  DeclarativeGrammar.fallbackDeclExactOutcomeSpec

/-- Fallback successes agree on their complete AST and remainder. -/
theorem fallbackDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : FallbackDecl}
    (leftResult : fallbackDecl input = .ok left leftOutput)
    (rightResult : fallbackDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  fallbackDecl_exactOutcomeSpec.successResultUnique
    (fallbackDecl_success_ordinaryOutcome_sound leftResult)
    (fallbackDecl_success_ordinaryOutcome_sound rightResult)

/-- Fallback rejections agree on their complete declarative endpoint. -/
theorem fallbackDecl_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : fallbackDecl input = .reject leftFailure leftOutput)
    (rightResult : fallbackDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  fallbackDecl_exactOutcomeSpec.rejectOutputUnique
    (fallbackDecl_reject_ordinaryOutcome_sound leftResult)
    (fallbackDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
