import Solcore.Syntax.DeclarativeConstructorDeclarationExactnessProperties
import Solcore.Syntax.Parser.ConstructorDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ConstructorDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable ordinary outcomes for canonical constructors. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable constructor success and rejection. -/
theorem constructorDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ConstructorDecl},
      constructorDecl input = .ok declaration output →
        DeclarativeGrammar.ConstructorDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      constructorDecl input = .reject failure rejected →
        DeclarativeGrammar.ConstructorDeclRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨constructorDecl_success_ordinaryOutcome_sound,
    constructorDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export the parser-independent deterministic constructor contract. -/
theorem constructorDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ConstructorDeclOrdinaryParses
      DeclarativeGrammar.ConstructorDeclRejects :=
  DeclarativeGrammar.constructorDeclDeterministicOutcomeSpec

/-- Exact parameter and isolated-body contracts lift to the executable
constructor reflection boundary. -/
theorem constructorDecl_exactOutcomeSpec_of_children
    (parameterOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FunctionParametersOrdinaryParses
      DeclarativeGrammar.FunctionParametersRejects)
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .require)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ConstructorDeclOrdinaryParses
      DeclarativeGrammar.ConstructorDeclRejects :=
  DeclarativeGrammar.constructorDeclExactOutcomeSpecOfChildren
    parameterOutcomes bodyOutcomes

/-- Under exact child contracts, two executable successes have the same
constructor AST and final declarative remainder. -/
theorem constructorDecl_success_result_unique_of_children
    (parameterOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FunctionParametersOrdinaryParses
      DeclarativeGrammar.FunctionParametersRejects)
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .require))
    {input leftOutput rightOutput : State}
    {left right : ConstructorDecl}
    (leftResult : constructorDecl input = .ok left leftOutput)
    (rightResult : constructorDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ConstructorDeclOrdinaryParses.result_unique_of_exact_children
      parameterOutcomes bodyOutcomes
      (constructorDecl_success_ordinaryOutcome_sound leftResult)
      (constructorDecl_success_ordinaryOutcome_sound rightResult)

/-- Under exact child contracts, two executable rejections have the same
declarative endpoint. -/
theorem constructorDecl_reject_output_unique_of_children
    (parameterOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FunctionParametersOrdinaryParses
      DeclarativeGrammar.FunctionParametersRejects)
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .require))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : constructorDecl input = .reject leftFailure leftOutput)
    (rightResult : constructorDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ConstructorDeclRejects.output_unique_of_exact_children
      parameterOutcomes bodyOutcomes
      (constructorDecl_reject_ordinaryOutcome_sound leftResult)
      (constructorDecl_reject_ordinaryOutcome_sound rightResult)

/-- Exact function parameters leave only the isolated body contract as a
premise at the executable constructor boundary. -/
theorem constructorDecl_exactOutcomeSpec_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .require)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ConstructorDeclOrdinaryParses
      DeclarativeGrammar.ConstructorDeclRejects :=
  DeclarativeGrammar.constructorDeclExactOutcomeSpecOfBody bodyOutcomes

/-- With an exact isolated body, two executable successes have the same
constructor AST and final declarative remainder. -/
theorem constructorDecl_success_result_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .require))
    {input leftOutput rightOutput : State}
    {left right : ConstructorDecl}
    (leftResult : constructorDecl input = .ok left leftOutput)
    (rightResult : constructorDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ConstructorDeclOrdinaryParses.result_unique_of_exact_body
    bodyOutcomes (constructorDecl_success_ordinaryOutcome_sound leftResult)
    (constructorDecl_success_ordinaryOutcome_sound rightResult)

/-- With an exact isolated body, two executable rejections have the same
declarative endpoint. -/
theorem constructorDecl_reject_output_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .require))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : constructorDecl input = .reject leftFailure leftOutput)
    (rightResult : constructorDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ConstructorDeclRejects.output_unique_of_exact_body
    bodyOutcomes (constructorDecl_reject_ordinaryOutcome_sound leftResult)
    (constructorDecl_reject_ordinaryOutcome_sound rightResult)

/-- Fixed-fuel Core statement exactness discharges the complete executable
constructor contract. -/
theorem constructorDecl_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ConstructorDeclOrdinaryParses
      DeclarativeGrammar.ConstructorDeclRejects :=
  DeclarativeGrammar.constructorDeclExactOutcomeSpecOfStatementFuel
    statementOutcomes

end Solcore.Syntax.Parser
