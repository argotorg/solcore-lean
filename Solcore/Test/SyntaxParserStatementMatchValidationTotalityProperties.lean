import Solcore.Syntax.Parser.Statement.MatchValidationTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementMatchValidationTotalityProperties

open Solcore.Syntax.Parser

example := @MatchInternals.validateMatchCaseArity_ordinary
example := @MatchInternals.validateMatchArities_ordinary
example := @MatchInternals.validateMatchArities_invariantFreeOnValid
example := @MatchInternals.validateMatchArities_ne_invariant

end Solcore.Test.SyntaxParserStatementMatchValidationTotalityProperties
