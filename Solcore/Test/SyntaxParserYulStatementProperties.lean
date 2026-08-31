import Solcore.Syntax.Parser.Yul.StatementProperties

/-! External consumers for inline-Yul leaf-statement contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulBlockStatement_validFor
example := @yulBlockStatement_preservesTokensOnSuccess
example := @yulBlockStatement_cursorMonotoneOnSuccess
example := @yulBlockStatement_startsAtCurrentTokenOnSuccess
example := @yulStatementCore_contracts
example := @yulStatementCore_validFor
example := @yulStatementCore_preservesTokensOnSuccess
example := @yulStatementCore_cursorMonotoneOnSuccess
example := @yulStatementCore_startsAtCurrentTokenOnSuccess
example := yulLetInitializer_validFor
example := yulLetInitializer_preservesTokenWindow
example := yulLetInitializer_cursorMonotoneOnSuccess
example := yulLetStatement_validFor
example := yulLetStatement_preservesTokenWindow
example := yulLetStatement_preservesTokensOnSuccess
example := yulLetStatement_cursorMonotoneOnSuccess
example := yulLetStatement_startsAtCurrentTokenOnSuccess
example := yulAssignment_validFor
example := yulAssignment_preservesTokensOnSuccess
example := yulAssignment_cursorMonotoneOnSuccess
example := yulAssignment_startsAtCurrentTokenOnSuccess

example := yulExpressionStatement_validFor
example := yulExpressionStatement_preservesTokenWindow
example := yulExpressionStatement_preservesTokensOnSuccess
example := yulExpressionStatement_cursorMonotoneOnSuccess
example := yulExpressionStatement_startsAtCurrentTokenOnSuccess

example := yulReturnBuiltin_validFor
example := yulReturnBuiltin_preservesTokenWindow
example := yulReturnBuiltin_preservesTokensOnSuccess
example := yulReturnBuiltin_cursorMonotoneOnSuccess
example := yulReturnBuiltin_startsAtCurrentTokenOnSuccess

example := yulLeaveControl_validFor
example := yulBreakControl_validFor
example := yulContinueControl_validFor
example := @yulControlToken_preservesTokenWindow
example := @yulControlToken_preservesTokensOnSuccess
example := @yulControlToken_cursorMonotoneOnSuccess
example := @yulControlToken_startsAtCurrentTokenOnSuccess
example := @recognizedYulStatementOrFallback_validFor
example := @recognizedYulStatementOrFallback_preservesTokenWindow
example := @recognizedYulStatementOrFallback_preservesTokensOnSuccess
example := @recognizedYulStatementOrFallback_cursorMonotoneOnSuccess
example := @recognizedYulStatementOrFallback_startsAtCurrentTokenOnSuccess
example := @optionalYulSemicolon_validForAt
example := @optionalYulSemicolon_preservesTokenWindow
example := @optionalYulSemicolon_cursorMonotoneOnSuccess
example := @optionalYulSemicolon_value_eq
example := @yulStatementTerminated_validFor
example := @yulStatementTerminated_preservesTokensOnSuccess
example := @yulStatementTerminated_cursorMonotoneOnSuccess
example := @yulStatementTerminated_startsAtCurrentTokenOnSuccess
example := @finishRecoveredYulStatement_validFor
example := @recoverYulStatementAux_validFor
example := @recoverYulStatementAux_preservesTokenWindow
example := @recoverYulStatementAux_preservesTokensOnSuccess
example := @recoverYulStatementAux_cursorMonotoneOnSuccess
example := @yulStatementTerminated_preservesTokenWindow
example := @yulStatementLayer_validFor
example := @yulStatementLayer_preservesTokenWindow
example := @yulStatementLayer_preservesTokensOnSuccess
example := @yulStatementLayer_cursorMonotoneOnSuccess
example := @yulStatementLayer_startsAtCurrentTokenOnSuccess
example := @yulStatementWithFuel_preservesTokenWindow
example := @yulStatementWithFuel_validFor
example := @yulStatementWithFuel_cursorMonotoneOnSuccess
example := @yulStatementWithFuel_startsAtCurrentTokenOnSuccess

end Tests
