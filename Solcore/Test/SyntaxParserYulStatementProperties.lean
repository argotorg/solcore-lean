import Solcore.Syntax.Parser.Yul.StatementProperties

/-! External consumers for inline-Yul leaf-statement contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

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

example := yulLeaveControl_validFor
example := yulBreakControl_validFor
example := yulContinueControl_validFor
example := @yulControlToken_preservesTokenWindow
example := @yulControlToken_preservesTokensOnSuccess
example := @yulControlToken_cursorMonotoneOnSuccess
example := @yulControlToken_startsAtCurrentTokenOnSuccess

end Tests
