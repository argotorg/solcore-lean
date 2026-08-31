import Solcore.Syntax.Parser.Yul.StatementLeafStrictTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementLeafStrictTotalityProperties

open Solcore.Syntax.Parser

example := @yulLetStatement_cursor_lt_onSuccess
example := @yulAssignment_cursor_lt_onSuccess
example := @yulExpressionStatement_cursor_lt_onSuccess
example := @yulReturnBuiltin_cursor_lt_onSuccess
example := @yulControlToken_cursor_lt_onSuccess
example := @YulStatementTotalityContract.elementTotalityContract
example := @yulLetStatement_elementTotalityContract
example := @yulAssignment_elementTotalityContract
example := @yulExpressionStatement_elementTotalityContract
example := @yulReturnBuiltin_elementTotalityContract
example := @yulControlToken_elementTotalityContract
example := @yulLeaveControl_elementTotalityContract
example := @yulBreakControl_elementTotalityContract
example := @yulContinueControl_elementTotalityContract

end Solcore.Test.SyntaxParserYulStatementLeafStrictTotalityProperties
