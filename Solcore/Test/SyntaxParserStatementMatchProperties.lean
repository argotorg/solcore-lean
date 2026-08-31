import Solcore.Syntax.Parser.Statement.MatchProperties

/-! External consumers for canonical Core match-component contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @MatchInternals.matchCase_validFor
example := @MatchInternals.matchCase_preservesTokenWindow
example := @MatchInternals.matchCase_preservesTokensOnSuccess
example := @MatchInternals.matchCase_cursorMonotoneOnSuccess
example := @MatchInternals.matchCase_startsAtCurrentTokenOnSuccess
example := @MatchInternals.matchCases_validFor
example := @MatchInternals.matchCases_preservesTokenWindow
example := @MatchInternals.matchCases_preservesTokensOnSuccess
example := @MatchInternals.matchCases_cursorMonotoneOnSuccess

end Tests
