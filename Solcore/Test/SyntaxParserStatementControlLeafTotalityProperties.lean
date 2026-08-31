import Solcore.Syntax.Parser.Statement.ControlLeafTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementControlLeafTotalityProperties

open Solcore.Syntax.Parser

example := @ControlInternals.terminatedControl_invariantFreeOnValid
example := @breakStatement_invariantFreeOnValid
example := @continueStatement_invariantFreeOnValid
example := @breakStatement_totalityContract
example := @continueStatement_totalityContract

end Solcore.Test.SyntaxParserStatementControlLeafTotalityProperties
