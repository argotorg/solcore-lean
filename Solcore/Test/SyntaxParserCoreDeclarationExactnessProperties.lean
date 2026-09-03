import Solcore.Syntax.Parser.CoreDeclarationExactnessProperties

/-! External consumers for unconditional Core declaration exactness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreDeclarationExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeclarativeGrammar.functionDeclExactOutcomeSpec
example := @DeclarativeGrammar.constructorDeclExactOutcomeSpec
example := @DeclarativeGrammar.fallbackDeclExactOutcomeSpec
example := @DeclarativeGrammar.implMethodExactOutcomeSpec
example := @DeclarativeGrammar.implBodyExactOutcomeSpec
example := @DeclarativeGrammar.implDeclExactOutcomeSpec
example := @DeclarativeGrammar.contractFieldPublicExactOutcomeSpec
example := @DeclarativeGrammar.contractMemberCoreExactOutcomeSpec
example := @DeclarativeGrammar.contractMemberExactOutcomeSpec
example := @DeclarativeGrammar.contractBodyExactOutcomeSpec
example := @DeclarativeGrammar.contractDeclExactOutcomeSpec

example := @functionDecl_exactOutcomeSpec
example := @functionDecl_success_result_unique
example := @functionDecl_reject_output_unique
example := @constructorDecl_exactOutcomeSpec
example := @constructorDecl_success_result_unique
example := @constructorDecl_reject_output_unique
example := @fallbackDecl_exactOutcomeSpec
example := @fallbackDecl_success_result_unique
example := @fallbackDecl_reject_output_unique
example := @ImplInternals.implMethod_exactOutcomeSpec
example := @ImplInternals.implMethod_success_result_unique
example := @ImplInternals.implMethod_reject_output_unique
example := @ImplInternals.implBody_exactOutcomeSpec
example := @ImplInternals.implBody_success_result_unique
example := @ImplInternals.implBody_reject_output_unique
example := @implDecl_exactOutcomeSpec
example := @implDecl_success_result_unique
example := @implDecl_reject_output_unique
example := @ContractInternals.contractFieldPublic_exactOutcomeSpec
example := @ContractInternals.contractFieldPublic_success_result_unique
example := @ContractInternals.contractFieldPublic_reject_output_unique
example := @ContractInternals.contractMemberCore_exactOutcomeSpec
example := @ContractInternals.contractMemberCore_success_result_unique_unconditional
example := @ContractInternals.contractMemberCore_reject_output_unique_unconditional
example := @ContractInternals.contractMemberWithAttribute_exactOutcomeSpec
example := @ContractInternals.contractMemberWithAttribute_success_result_unique
example := @ContractInternals.contractMemberWithAttribute_reject_output_unique
example := @ContractInternals.contractBody_exactOutcomeSpec
example := @ContractInternals.contractBody_success_result_unique
example := @ContractInternals.contractBody_reject_output_unique
example := @contractDecl_exactOutcomeSpec
example := @contractDecl_success_result_unique
example := @contractDecl_reject_output_unique

example (location : FunctionLocation)
    {input leftOutput rightOutput : State} {left right : FunctionDecl}
    (leftResult : functionDecl location input = .ok left leftOutput)
    (rightResult : functionDecl location input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  functionDecl_success_result_unique location leftResult rightResult

example {input leftOutput rightOutput : State}
    {left right : ImplInternals.ImplBody}
    (leftResult : ImplInternals.implBody input = .ok left leftOutput)
    (rightResult : ImplInternals.implBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  ImplInternals.implBody_success_result_unique leftResult rightResult

example {input leftOutput rightOutput : State} {left right : ContractField}
    (leftResult : ContractInternals.contractField expression input =
      .ok left leftOutput)
    (rightResult : ContractInternals.contractField expression input =
      .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  ContractInternals.contractFieldPublic_success_result_unique
    leftResult rightResult

example {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractDecl input = .reject leftFailure leftOutput)
    (rightResult : contractDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractDecl_reject_output_unique leftResult rightResult

end Solcore.Test.SyntaxParserCoreDeclarationExactnessProperties
