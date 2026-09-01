import Solcore.Syntax.Parser.TermRecursiveFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTermRecursiveFuelTotalityProperties

open Solcore.Syntax.Parser

example := @TermInternals.coreExpressionTotalityFuel
example := @TermInternals.corePatternTotalityFuel
example := @TermInternals.coreStatementTotalityFuel
example := @TermInternals.RecursiveFuelTotalityContract
example := @TermInternals.coreStatementWithFuel_cursor_lt_onSuccess
example := @TermInternals.coreRecursiveWithFuel_fuelTotalityContract

end Solcore.Test.SyntaxParserTermRecursiveFuelTotalityProperties
