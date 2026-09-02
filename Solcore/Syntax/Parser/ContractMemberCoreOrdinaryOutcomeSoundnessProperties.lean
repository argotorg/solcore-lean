import Solcore.Syntax.DeclarativeContractMemberCoreExactnessProperties
import Solcore.Syntax.Parser.ContractMemberCoreOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberCoreOrdinarySuccessSoundnessProperties

/-! Complete broad executable outcomes for attribute-free contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Package unconditional executable success and exact selected-branch
rejection for attribute-free contract members. -/
theorem contractMemberCore_ordinaryOutcome_sound :
    (∀ {input output : State} {member : ContractMember},
      contractMemberCore input = .ok member output →
        DeclarativeGrammar.ContractMemberCoreOrdinaryParses
          input.declarativeRemainder member output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractMemberCore input = .reject failure rejected →
        DeclarativeGrammar.ContractMemberCoreRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨contractMemberCore_success_ordinaryOutcome_sound,
    contractMemberCore_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive attribute-free member outcomes. -/
theorem contractMemberCore_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects :=
  DeclarativeGrammar.contractMemberCoreDeterministicOutcomeSpec

/-- Exact public expressions, isolated bodies, and enums supply exact
attribute-free member outcomes. -/
theorem contractMemberCore_exactOutcomeSpec_of_leaves
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects)
    (allowBodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    (requireBodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .require))
    (enumOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.EnumDeclOrdinaryParses none)
      DeclarativeGrammar.EnumDeclRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects :=
  DeclarativeGrammar.contractMemberCoreExactOutcomeSpecOfLeaves
    expressionOutcomes allowBodyOutcomes requireBodyOutcomes enumOutcomes

/-- Fixed-fuel Core exactness leaves only enum exactness as a premise. -/
theorem contractMemberCore_exactOutcomeSpec_of_termFuel
    (expressionOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    (enumOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.EnumDeclOrdinaryParses none)
      DeclarativeGrammar.EnumDeclRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects :=
  DeclarativeGrammar.contractMemberCoreExactOutcomeSpecOfTermFuel
    expressionOutcomes statementOutcomes enumOutcomes

/-- Any exact core contract fixes two executable success ASTs and endpoints. -/
theorem contractMemberCore_success_result_unique
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects)
    {input leftOutput rightOutput : State} {left right : ContractMember}
    (leftResult : contractMemberCore input = .ok left leftOutput)
    (rightResult : contractMemberCore input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  coreOutcomes.successResultUnique
    (contractMemberCore_success_ordinaryOutcome_sound leftResult)
    (contractMemberCore_success_ordinaryOutcome_sound rightResult)

/-- Any exact core contract fixes two executable rejection endpoints. -/
theorem contractMemberCore_reject_output_unique
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : contractMemberCore input = .reject leftFailure leftOutput)
    (rightResult : contractMemberCore input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  coreOutcomes.rejectOutputUnique
    (contractMemberCore_reject_ordinaryOutcome_sound leftResult)
    (contractMemberCore_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ContractInternals
