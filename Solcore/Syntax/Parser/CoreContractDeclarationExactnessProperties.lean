import Solcore.Syntax.DeclarativeCoreDeclarationExactnessProperties
import Solcore.Syntax.Parser.ContractDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTermPublicExactnessProperties

/-! Unconditional executable exactness for complete contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

/-- Public Core-expression field initializers need no exactness premise. -/
theorem contractFieldPublic_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.ContractFieldOrdinaryParses
        DeclarativeGrammar.CoreExpressionOrdinaryParses)
      (DeclarativeGrammar.ContractFieldRejects
        DeclarativeGrammar.CoreExpressionOrdinaryParses
        DeclarativeGrammar.CoreExpressionPublicRejects) :=
  DeclarativeGrammar.contractFieldPublicExactOutcomeSpec

/-- Public field successes agree on their complete AST and remainder. -/
theorem contractFieldPublic_success_result_unique
    {input leftOutput rightOutput : State} {left right : ContractField}
    (leftResult : contractField expression input = .ok left leftOutput)
    (rightResult : contractField expression input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractField_success_result_unique expression
    DeclarativeGrammar.CoreExpressionOrdinaryParses
    DeclarativeGrammar.CoreExpressionPublicRejects
    DeclarativeGrammar.coreExpressionPublicExactOutcomeSpec
    expression_success_ordinary_sound leftResult rightResult

/-- Public field rejections agree on their complete declarative endpoint. -/
theorem contractFieldPublic_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractField expression input = .reject leftFailure leftOutput)
    (rightResult : contractField expression input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractField_reject_output_unique expression
    DeclarativeGrammar.CoreExpressionOrdinaryParses
    DeclarativeGrammar.CoreExpressionPublicRejects
    DeclarativeGrammar.coreExpressionPublicExactOutcomeSpec
    expression_success_ordinary_sound expression_reject_ordinary_sound
    leftResult rightResult

/-- Attribute-free contract-member exactness needs no child premises. -/
theorem contractMemberCore_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects :=
  DeclarativeGrammar.contractMemberCoreExactOutcomeSpec

/-- Core-member successes agree without a supplied exact-outcome contract. -/
theorem contractMemberCore_success_result_unique_unconditional
    {input leftOutput rightOutput : State} {left right : ContractMember}
    (leftResult : contractMemberCore input = .ok left leftOutput)
    (rightResult : contractMemberCore input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractMemberCore_success_result_unique contractMemberCore_exactOutcomeSpec
    leftResult rightResult

/-- Core-member rejections agree without a supplied exact-outcome contract. -/
theorem contractMemberCore_reject_output_unique_unconditional
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractMemberCore input = .reject leftFailure leftOutput)
    (rightResult : contractMemberCore input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractMemberCore_reject_output_unique contractMemberCore_exactOutcomeSpec
    leftResult rightResult

/-- Derive-aware member exactness needs no core-member premise. -/
theorem contractMemberWithAttribute_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects :=
  DeclarativeGrammar.contractMemberExactOutcomeSpec

/-- Derive-aware member successes agree on their complete AST and remainder. -/
theorem contractMemberWithAttribute_success_result_unique
    {input leftOutput rightOutput : State} {left right : ContractMember}
    (leftResult : contractMemberWithAttribute input = .ok left leftOutput)
    (rightResult : contractMemberWithAttribute input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractMemberWithAttribute_exactOutcomeSpec.successResultUnique
    (contractMemberWithAttribute_success_ordinaryOutcome_sound leftResult)
    (contractMemberWithAttribute_success_ordinaryOutcome_sound rightResult)

/-- Derive-aware member rejections agree on their declarative endpoint. -/
theorem contractMemberWithAttribute_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractMemberWithAttribute input =
      .reject leftFailure leftOutput)
    (rightResult : contractMemberWithAttribute input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractMemberWithAttribute_exactOutcomeSpec.rejectOutputUnique
    (contractMemberWithAttribute_reject_ordinaryOutcome_sound leftResult)
    (contractMemberWithAttribute_reject_ordinaryOutcome_sound rightResult)

/-- Recovery-aware contract-body exactness needs no member premise. -/
theorem contractBody_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects :=
  DeclarativeGrammar.contractBodyExactOutcomeSpec

/-- Contract-body successes agree on their parser value and final remainder. -/
theorem contractBody_success_result_unique
    {input leftOutput rightOutput : State} {left right : ContractBody}
    (leftResult : contractBody input = .ok left leftOutput)
    (rightResult : contractBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractBody_success_result_unique_of_member
    DeclarativeGrammar.contractMemberExactOutcomeSpec leftResult rightResult

/-- Contract-body rejections agree on their complete declarative endpoint. -/
theorem contractBody_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractBody input = .reject leftFailure leftOutput)
    (rightResult : contractBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractBody_exactOutcomeSpec.rejectOutputUnique
    (contractBody_reject_ordinaryOutcome_sound leftResult)
    (contractBody_reject_ordinaryOutcome_sound rightResult)

end ContractInternals

/-- Complete contract-declaration exactness needs no body premise. -/
theorem contractDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractDeclOrdinaryParses
      DeclarativeGrammar.ContractDeclRejects :=
  DeclarativeGrammar.contractDeclExactOutcomeSpec

/-- Complete contract successes agree on their complete AST and remainder. -/
theorem contractDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : ContractDecl}
    (leftResult : contractDecl input = .ok left leftOutput)
    (rightResult : contractDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractDecl_exactOutcomeSpec.successResultUnique
    (contractDecl_success_ordinaryOutcome_sound leftResult)
    (contractDecl_success_ordinaryOutcome_sound rightResult)

/-- Complete contract rejections agree on their complete declarative endpoint. -/
theorem contractDecl_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractDecl input = .reject leftFailure leftOutput)
    (rightResult : contractDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractDecl_exactOutcomeSpec.rejectOutputUnique
    (contractDecl_reject_ordinaryOutcome_sound leftResult)
    (contractDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
