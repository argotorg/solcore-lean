import Solcore.Syntax.Parser.Yul.NamesTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulNamesTotalityProperties

open Solcore.Syntax.Parser

example := @yulNamesTail_ordinary_of_remainingCount_lt
example := @yulNames_invariantFreeOnValid
example := @yulNames_cursor_lt_onSuccess
example := @yulNames_elementTotalityContract

end Solcore.Test.SyntaxParserYulNamesTotalityProperties
