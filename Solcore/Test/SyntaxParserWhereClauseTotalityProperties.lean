import Solcore.Syntax.Parser.WhereClauseTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserWhereClauseTotalityProperties

open Solcore.Syntax.Parser

example := @whereClause_invariantFreeOnValid
example := @whereClause_ordinary
example := @whereClause_ne_invariant

end Solcore.Test.SyntaxParserWhereClauseTotalityProperties
