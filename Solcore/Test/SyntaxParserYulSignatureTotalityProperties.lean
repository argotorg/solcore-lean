import Solcore.Syntax.Parser.Yul.SignatureTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulSignatureTotalityProperties

open Solcore.Syntax.Parser

example := @yulParameters_ordinary
example := @yulParameters_invariantFreeOnValid
example := @yulParameters_ne_invariant
example := @yulParameters_elementTotalityContract
example := @yulReturnClause_ordinary
example := @yulReturnClause_invariantFreeOnValid
example := @yulReturnClause_ne_invariant
example := @yulReturnClause_cursor_lt_onSuccess
example := @yulReturnClause_elementTotalityContract
example := @yulReturns_ordinary
example := @yulReturns_invariantFreeOnValid
example := @yulReturns_ne_invariant

end Solcore.Test.SyntaxParserYulSignatureTotalityProperties
