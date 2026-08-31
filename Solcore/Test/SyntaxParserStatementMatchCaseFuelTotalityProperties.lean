import Solcore.Syntax.Parser.Statement.MatchCaseFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementMatchCaseFuelTotalityProperties

open Solcore.Syntax.Parser

example := @MatchInternals.matchCase_ordinary_of_fuels
example := @MatchInternals.matchCase_ne_invariant_of_fuels
example := @MatchInternals.matchCase_cursor_lt_onSuccess
example := @MatchInternals.matchCase_fuelElementTotalityContract

end Solcore.Test.SyntaxParserStatementMatchCaseFuelTotalityProperties
