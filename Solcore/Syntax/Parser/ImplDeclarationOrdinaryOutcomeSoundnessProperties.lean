import Solcore.Syntax.DeclarativeImplDeclarationExactnessProperties
import Solcore.Syntax.Parser.ImplBodyOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ImplDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImplDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable implementation success and exact six-stage rejection. -/
theorem implDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ImplDecl},
      implDecl input = .ok declaration output →
        DeclarativeGrammar.ImplDeclOrdinaryParses input.declarativeRemainder
          declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      implDecl input = .reject failure rejected →
        DeclarativeGrammar.ImplDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨implDecl_success_ordinaryOutcome_sound,
    implDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad implementation outcomes. -/
theorem implDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImplDeclOrdinaryParses
      DeclarativeGrammar.ImplDeclRejects :=
  DeclarativeGrammar.implDeclDeterministicOutcomeSpec

/-- Re-export exact implementation-declaration outcomes from exact complete
implementation-body outcomes. -/
theorem implDecl_exactOutcomeSpec_of_implBody
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplDeclOrdinaryParses
      DeclarativeGrammar.ImplDeclRejects :=
  DeclarativeGrammar.implDeclExactOutcomeSpecOfImplBody bodyOutcomes

/-- Re-export exact implementation-declaration outcomes from an exact
isolated method body. -/
theorem implDecl_exactOutcomeSpec_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplDeclOrdinaryParses
      DeclarativeGrammar.ImplDeclRejects :=
  DeclarativeGrammar.implDeclExactOutcomeSpecOfBody bodyOutcomes

/-- Fixed-fuel Core statement exactness discharges the executable
implementation-declaration contract. -/
theorem implDecl_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplDeclOrdinaryParses
      DeclarativeGrammar.ImplDeclRejects :=
  DeclarativeGrammar.implDeclExactOutcomeSpecOfStatementFuel
    statementOutcomes

/-- Exact complete implementation-body outcomes make two successful
executable implementation declarations agree. -/
theorem implDecl_success_result_unique_of_implBody
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects)
    {input leftOutput rightOutput : State} {left right : ImplDecl}
    (leftResult : implDecl input = .ok left leftOutput)
    (rightResult : implDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplDeclOrdinaryParses.result_unique_of_impl_body
    bodyOutcomes (implDecl_success_ordinaryOutcome_sound leftResult)
    (implDecl_success_ordinaryOutcome_sound rightResult)

/-- Exact complete implementation-body outcomes make two executable
implementation-declaration rejections agree. -/
theorem implDecl_reject_output_unique_of_implBody
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implDecl input = .reject leftFailure leftOutput)
    (rightResult : implDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplDeclRejects.output_unique_of_impl_body bodyOutcomes
    (implDecl_reject_ordinaryOutcome_sound leftResult)
    (implDecl_reject_ordinaryOutcome_sound rightResult)

/-- An exact isolated method body makes two successful executable
implementation declarations agree. -/
theorem implDecl_success_result_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State} {left right : ImplDecl}
    (leftResult : implDecl input = .ok left leftOutput)
    (rightResult : implDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implDecl_success_result_unique_of_implBody
    (DeclarativeGrammar.implBodyExactOutcomeSpecOfBody bodyOutcomes)
    leftResult rightResult

/-- An exact isolated method body makes two executable implementation
declaration rejections agree. -/
theorem implDecl_reject_output_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implDecl input = .reject leftFailure leftOutput)
    (rightResult : implDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implDecl_reject_output_unique_of_implBody
    (DeclarativeGrammar.implBodyExactOutcomeSpecOfBody bodyOutcomes)
    leftResult rightResult

/-- Fixed-fuel Core statement exactness makes two successful executable
implementation declarations agree. -/
theorem implDecl_success_result_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    {input leftOutput rightOutput : State} {left right : ImplDecl}
    (leftResult : implDecl input = .ok left leftOutput)
    (rightResult : implDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implDecl_success_result_unique_of_implBody
    (DeclarativeGrammar.implBodyExactOutcomeSpecOfStatementFuel
      statementOutcomes)
    leftResult rightResult

/-- Fixed-fuel Core statement exactness makes two executable implementation
declaration rejections agree. -/
theorem implDecl_reject_output_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implDecl input = .reject leftFailure leftOutput)
    (rightResult : implDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implDecl_reject_output_unique_of_implBody
    (DeclarativeGrammar.implBodyExactOutcomeSpecOfStatementFuel
      statementOutcomes)
    leftResult rightResult

end Solcore.Syntax.Parser
