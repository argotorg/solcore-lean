import Solcore.Syntax.Parser.Statement.MatchCasesFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementMatchCasesFuelTotalityProperties

open Solcore.Syntax.Parser

example := @MatchInternals.FuelCaseListTotalityContract.ne_invariant
example := @MatchInternals.matchCases_ordinary_of_fuels
example := @MatchInternals.matchCases_ne_invariant_of_fuels
example := @MatchInternals.matchCases_production_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementMatchCasesFuelTotalityProperties
