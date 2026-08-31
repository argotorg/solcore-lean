import Solcore.Syntax.Parser.Statement.MatchScrutineeTotalityProperties

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
example := @MatchInternals.optionalDefaultBody_validFor
example := @MatchInternals.optionalDefaultBody_preservesTokenWindow
example := @MatchInternals.optionalDefaultBody_preservesTokensOnSuccess
example := @MatchInternals.optionalDefaultBody_cursorMonotoneOnSuccess
example := @MatchInternals.optionalDefaultBody_some_startsAfterKeyword
example := @MatchInternals.requireScrutinees_validFor
example := @MatchInternals.requireScrutinees_preservesTokenWindow
example := @MatchInternals.requireScrutinees_cursorMonotoneOnSuccess
example := @MatchInternals.requireScrutinees_ordinary
example := @MatchInternals.requireScrutinees_invariantFreeOnValid
example := @MatchInternals.requireScrutinees_ne_invariant
example := @matchStatement_validFor
example := @matchStatement_preservesTokenWindow
example := @matchStatement_preservesTokensOnSuccess
example := @matchStatement_cursorMonotoneOnSuccess
example := @matchStatement_cursor_lt_onSuccess
example := @matchStatement_startsAtCurrentTokenOnSuccess

end Tests
