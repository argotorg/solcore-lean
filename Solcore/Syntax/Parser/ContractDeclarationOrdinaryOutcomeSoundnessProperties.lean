import Solcore.Syntax.DeclarativeContractDeclarationExactnessProperties
import Solcore.Syntax.Parser.ContractDeclarationOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ContractDeclarationOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable contract-declaration success and exact four-stage
rejection. -/
theorem contractDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ContractDecl},
      contractDecl input = .ok declaration output →
        DeclarativeGrammar.ContractDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractDecl input = .reject failure rejected →
        DeclarativeGrammar.ContractDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨contractDecl_success_ordinaryOutcome_sound,
    contractDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad contract-declaration
outcomes. -/
theorem contractDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractDeclOrdinaryParses
      DeclarativeGrammar.ContractDeclRejects :=
  DeclarativeGrammar.contractDeclDeterministicOutcomeSpec

/-- An exact contract body lifts to exact complete declaration outcomes. -/
theorem contractDecl_exactOutcomeSpec_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractDeclOrdinaryParses
      DeclarativeGrammar.ContractDeclRejects :=
  DeclarativeGrammar.contractDeclExactOutcomeSpecOfBody bodyOutcomes

/-- Exact attribute-free member outcomes lift through the complete contract. -/
theorem contractDecl_exactOutcomeSpec_of_core
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractDeclOrdinaryParses
      DeclarativeGrammar.ContractDeclRejects :=
  DeclarativeGrammar.contractDeclExactOutcomeSpecOfCore coreOutcomes

/-- Fixed-fuel Core expression and statement exactness alone supplies exact
complete contract-declaration outcomes. -/
theorem contractDecl_exactOutcomeSpec_of_coreTermFuel
    (expressionOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractDeclOrdinaryParses
      DeclarativeGrammar.ContractDeclRejects :=
  DeclarativeGrammar.contractDeclExactOutcomeSpecOfCoreTermFuel
    expressionOutcomes statementOutcomes

/-- Under an exact body contract, two executable declarations have the same
AST and declarative remainder. -/
theorem contractDecl_success_result_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects)
    {input leftOutput rightOutput : State} {left right : ContractDecl}
    (leftResult : contractDecl input = .ok left leftOutput)
    (rightResult : contractDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (contractDecl_exactOutcomeSpec_of_body bodyOutcomes).successResultUnique
    (contractDecl_success_ordinaryOutcome_sound leftResult)
    (contractDecl_success_ordinaryOutcome_sound rightResult)

/-- Under an exact body contract, two declaration rejections have the same
declarative endpoint. -/
theorem contractDecl_reject_output_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : contractDecl input = .reject leftFailure leftOutput)
    (rightResult : contractDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (contractDecl_exactOutcomeSpec_of_body bodyOutcomes).rejectOutputUnique
    (contractDecl_reject_ordinaryOutcome_sound leftResult)
    (contractDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
