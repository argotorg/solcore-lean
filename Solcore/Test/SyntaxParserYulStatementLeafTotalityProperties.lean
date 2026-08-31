import Solcore.Syntax.Parser.Yul.StatementLeafTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulStatementLeafTotalityProperties

open Solcore.Syntax.Parser

example := @yulLetInitializer_ordinary
example := @yulLetInitializer_ne_invariant
example := @yulLetStatement_ordinary
example := @yulLetStatement_ne_invariant
example := @yulAssignment_ordinary
example := @yulAssignment_ne_invariant
example := @yulExpressionStatement_ordinary
example := @yulExpressionStatement_ne_invariant
example := @yulReturnBuiltin_ordinary
example := @yulReturnBuiltin_ne_invariant
example := @yulControlToken_ordinary
example := @yulControlToken_ne_invariant
example := @YulStatementTotalityContract.ne_invariant
example := @yulLetStatement_totalityContract
example := @yulAssignment_totalityContract
example := @yulExpressionStatement_totalityContract
example := @yulReturnBuiltin_totalityContract
example := @yulControlToken_totalityContract

end Solcore.Test.SyntaxParserYulStatementLeafTotalityProperties
