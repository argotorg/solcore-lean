import Solcore.Syntax.Parser.TermExpressionProperties

/-! External consumers for recursive canonical Core expression contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @TermInternals.CoreStatementFuelContract
example := @TermInternals.CoreStatementFuelContract.validFor
example := @TermInternals.CoreStatementFuelContract.preservesTokenWindow
example := @TermInternals.CoreStatementFuelContract.spanValid
example := @TermInternals.coreExpressionWithFuel_contract
example := @TermInternals.coreExpressionWithFuel_validFor
example := @TermInternals.coreExpressionWithFuel_preservesTokenWindow
example := @TermInternals.coreExpressionWithFuel_preservesTokensOnSuccess
example := @TermInternals.coreExpressionWithFuel_cursor_lt_onSuccess
example := @TermInternals.coreExpressionWithFuel_cursorMonotoneOnSuccess
example := @TermInternals.coreExpressionWithFuel_startsAtCurrentTokenOnSuccess
example := @expression_contract_of_coreStatement

end Tests
