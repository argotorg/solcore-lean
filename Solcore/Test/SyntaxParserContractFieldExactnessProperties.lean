import Solcore.Syntax.Parser.ContractFieldOrdinaryOutcomeSoundnessProperties

/-! Compile-time consumers for exact contract-field outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractFieldExactnessProperties

open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalContractFieldInitializerOrdinaryParses.value_unique
example := @OptionalContractFieldInitializerOrdinaryParses.result_unique
example := @OptionalContractFieldInitializerRejects.output_unique
example := @optionalContractFieldInitializerExactOutcomeSpec
example := @ContractFieldOrdinaryParses.value_unique
example := @ContractFieldOrdinaryParses.result_unique
example := @ContractFieldRejects.output_unique
example := @contractFieldExactOutcomeSpec

example := @ContractInternals.optionalFieldInitializer_exactOutcomeSpec
example := @ContractInternals.optionalFieldInitializer_success_result_unique
example := @ContractInternals.optionalFieldInitializer_reject_output_unique
example := @ContractInternals.contractField_exactOutcomeSpec
example := @ContractInternals.contractField_success_result_unique
example := @ContractInternals.contractField_reject_output_unique

end Solcore.Test.SyntaxParserContractFieldExactnessProperties
