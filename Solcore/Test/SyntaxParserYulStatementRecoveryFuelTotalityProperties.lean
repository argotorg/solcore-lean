import Solcore.Syntax.Parser.Yul.StatementRecoveryFuelTotalityProperties

/-! Compile-time consumers for Yul statement recovery totality. -/

namespace Solcore.Test.SyntaxParserYulStatementRecoveryFuelTotalityProperties

open Solcore.Syntax.Parser

example := @recoverYulStatementAux_exists_ok_of_remainingCount_lt
example := @recoverYulStatementAux_ordinary_of_remainingCount_lt
example := @recoverYulStatementAux_production_exists_ok
example := @recoverYulStatementAux_production_ordinary
example := @recoverYulStatementAux_production_invariantFreeOnValid
example := @recoverYulStatementAux_production_ne_invariant
example := @recoverYulStatementAux_ne_invariant_of_remainingCount_lt
example := @yulStatementLayer_ordinary_of_terminatedFuel
example := @yulStatementLayer_ne_invariant_of_terminatedFuel
example := @yulStatementLayer_cursor_lt_onSuccess_of_terminated
example := @yulStatementLayer_fuelTotalityContract

end Solcore.Test.SyntaxParserYulStatementRecoveryFuelTotalityProperties
