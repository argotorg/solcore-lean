import Solcore.Syntax.DeclarativeFallbackDeclarationExactnessProperties
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

/-- Re-export exact fallback outcomes from an exact isolated `.require`
body. -/
theorem fallbackDecl_exactOutcomeSpec_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .require)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FallbackDeclOrdinaryParses
      DeclarativeGrammar.FallbackDeclRejects :=
  DeclarativeGrammar.fallbackDeclExactOutcomeSpecOfBody bodyOutcomes

/-- Fixed-fuel Core statement exactness discharges the executable fallback
contract. -/
theorem fallbackDecl_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FallbackDeclOrdinaryParses
      DeclarativeGrammar.FallbackDeclRejects :=
  DeclarativeGrammar.fallbackDeclExactOutcomeSpecOfStatementFuel
    statementOutcomes

/-- With an exact isolated body, two executable fallback successes have the
same AST and final declarative remainder. -/
theorem fallbackDecl_success_result_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .require))
    {input leftOutput rightOutput : State} {left right : FallbackDecl}
    (leftResult : fallbackDecl input = .ok left leftOutput)
    (rightResult : fallbackDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FallbackDeclOrdinaryParses.result_unique_of_exact_body
    bodyOutcomes (fallbackDecl_success_ordinaryOutcome_sound leftResult)
    (fallbackDecl_success_ordinaryOutcome_sound rightResult)

/-- With an exact isolated body, two executable fallback rejections have the
same declarative endpoint. -/
theorem fallbackDecl_reject_output_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .require))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : fallbackDecl input = .reject leftFailure leftOutput)
    (rightResult : fallbackDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FallbackDeclRejects.output_unique_of_exact_body
    bodyOutcomes (fallbackDecl_reject_ordinaryOutcome_sound leftResult)
    (fallbackDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
