import Solcore.Syntax.Parser.Statement.SimpleBranchTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementSimpleBranchTotalityProperties

open Solcore.Syntax.Parser

example := @StatementSimpleInternals.optionalLetType_invariantFreeOnValid
example := @StatementSimpleInternals.optionalLetInitializer_invariantFreeOnValid
example := @StatementSimpleInternals.optionalReturnValue_invariantFreeOnValid
example := @letStatement_invariantFreeOnValid
example := @returnStatement_invariantFreeOnValid
example := @letStatement_totalityContract
example := @returnStatement_totalityContract

end Solcore.Test.SyntaxParserStatementSimpleBranchTotalityProperties
