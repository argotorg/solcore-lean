import Solcore.Syntax.Parser.TermStatementTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTermStatementTotalityProperties

open Solcore.Syntax.Parser.TermInternals

example := @recognizedStatementOrFallback_invariantFreeOnValid
example := @recognizedStatementOrFallback_ne_invariant
example := @StatementTotalityContract
example := @StatementTotalityContract.ne_invariant
example := @recognizedStatementOrFallback_totalityContract

end Solcore.Test.SyntaxParserTermStatementTotalityProperties
