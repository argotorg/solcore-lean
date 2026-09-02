import Solcore.Syntax.Parser.CoreBlockPublicIsolationOrdinaryOutcomeSoundnessProperties

/-! Compile-time consumers for conditional exact Core-block outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreBlockExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @CoreBlockItemsParses.result_unique
example := @CoreBlockOrdinaryParses.result_unique
example := @CoreBlockOrdinaryParses.value_unique
example := @CoreBlockItemsRejects.output_unique
example := @CoreBlockRejects.output_unique
example := @coreBlockExactOutcomeSpec
example := @coreBlockPublicExactOutcomeSpecOfStatementFuel
example := @IsolatedCoreBlockOrdinaryParses.value_unique
example := @IsolatedCoreBlockOrdinaryParses.result_unique
example := @IsolatedCoreBlockRejects.output_unique
example := @isolatedCoreBlockExactOutcomeSpec
example := @isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel
example := @block_exactOutcomeSpec_of_statementFuel
example := @block_success_result_unique_of_statementFuel
example := @block_reject_output_unique_of_statementFuel
example := @isolatedCoreBlockPublic_exactOutcomeSpec_of_statementFuel
example := @isolatedCoreBlockPublic_success_result_unique_of_statementFuel
example := @isolatedCoreBlockPublic_reject_output_unique_of_statementFuel

end Solcore.Test.SyntaxParserCoreBlockExactnessProperties
