import Solcore.Syntax.Parser.ContractDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberCoreOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinaryOutcomeSoundnessProperties

/-! Compile-time consumers for conditional exact contract declarations. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractDeclarationExactnessProperties

open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ContractMemberCoreOrdinaryParses.value_unique_of_exact_children
example := @ContractMemberCoreOrdinaryParses.result_unique_of_exact_children
example := @ContractMemberCoreRejects.output_unique_of_exact_children
example := @contractMemberCoreExactOutcomeSpecOfChildren
example := @contractMemberCoreExactOutcomeSpecOfLeaves
example := @contractMemberCoreExactOutcomeSpecOfTermFuel
example := @ContractMemberTailOrdinaryParses.result_unique_of_member
example := @ContractMemberTailRejects.output_unique_of_member
example := @contractMemberTailExactOutcomeSpecOfMember
example := @contractBodyExactOutcomeSpecOfMember
example := @contractBodyExactOutcomeSpecOfCore
example := @ContractDeclOrdinaryParses.value_unique_of_body
example := @ContractDeclOrdinaryParses.result_unique_of_body
example := @ContractDeclRejects.output_unique_of_body
example := @contractDeclExactOutcomeSpecOfBody
example := @contractDeclExactOutcomeSpecOfCore
example := @contractMemberCoreExactOutcomeSpecOfCoreTerms
example := @contractMemberCoreExactOutcomeSpecOfCoreTermFuel
example := @contractMemberExactOutcomeSpecOfCoreTermFuel
example := @contractBodyExactOutcomeSpecOfCoreTermFuel
example := @contractDeclExactOutcomeSpecOfCoreTermFuel

example := @ContractInternals.contractMemberCore_exactOutcomeSpec_of_leaves
example := @ContractInternals.contractMemberCore_exactOutcomeSpec_of_termFuel
example := @ContractInternals.contractMemberCore_success_result_unique
example := @ContractInternals.contractMemberCore_reject_output_unique
example := @ContractInternals.contractMemberWithAttribute_exactOutcomeSpec_of_core
example := @ContractInternals.contractBody_exactOutcomeSpec_of_member
example := @ContractInternals.contractBody_exactOutcomeSpec_of_core
example := @ContractInternals.contractBody_success_result_unique_of_member
example := @ContractInternals.contractBody_reject_output_unique_of_member
example := @contractDecl_exactOutcomeSpec_of_body
example := @contractDecl_exactOutcomeSpec_of_core
example := @contractDecl_success_result_unique_of_body
example := @contractDecl_reject_output_unique_of_body
example := @ContractInternals.contractMemberCore_exactOutcomeSpec_of_coreTermFuel
example := @ContractInternals.contractMemberWithAttribute_exactOutcomeSpec_of_coreTermFuel
example := @ContractInternals.contractBody_exactOutcomeSpec_of_coreTermFuel
example := @contractDecl_exactOutcomeSpec_of_coreTermFuel

end Solcore.Test.SyntaxParserContractDeclarationExactnessProperties
