import Solcore.Syntax.Parser.Statement.ControlProperties

/-! External consumers for canonical Core control-statement contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @ControlInternals.forItemsTail_validFor
example := @ControlInternals.forItemsTail_preservesTokenWindow
example := @ControlInternals.forItemsTail_cursorMonotoneOnSuccess
example := @ControlInternals.forItems_validFor
example := @ControlInternals.forItems_preservesTokenWindow
example := @ControlInternals.forItems_preservesTokensOnSuccess
example := @ControlInternals.forItems_cursorMonotoneOnSuccess
example := @forStatement_preservesTokenWindow
example := @forStatement_preservesTokensOnSuccess
example := @forStatement_cursorMonotoneOnSuccess
example := @forStatement_startsAtCurrentTokenOnSuccess
example := @forStatement_validFor
example := @blockStatement_validFor
example := @blockStatement_preservesTokenWindow
example := @blockStatement_preservesTokensOnSuccess
example := @blockStatement_cursorMonotoneOnSuccess
example := @blockStatement_startsAtCurrentTokenOnSuccess
example := @whileStatement_span_validOnSuccess
example := @whileStatement_validFor
example := @whileStatement_preservesTokenWindow
example := @whileStatement_preservesTokensOnSuccess
example := @whileStatement_cursorMonotoneOnSuccess
example := @whileStatement_startsAtCurrentTokenOnSuccess
example := @ControlInternals.optionalElseBody_validFor
example := @ControlInternals.optionalElseBody_preservesTokenWindow
example := @ControlInternals.optionalElseBody_preservesTokensOnSuccess
example := @ControlInternals.optionalElseBody_cursorMonotoneOnSuccess
example := @ControlInternals.optionalElseBody_some_startsAfterKeyword
example := @ifStatement_validFor
example := @ifStatement_preservesTokenWindow
example := @ifStatement_preservesTokensOnSuccess
example := @ifStatement_cursorMonotoneOnSuccess
example := @ifStatement_startsAtCurrentTokenOnSuccess
example := @assemblyStatement_validFor
example := @assemblyStatement_preservesTokenWindow
example := @assemblyStatement_preservesTokensOnSuccess
example := @assemblyStatement_cursorMonotoneOnSuccess
example := @assemblyStatement_startsAtCurrentTokenOnSuccess
example := @assemblyStatement_cursor_lt_onSuccess
example := @ControlInternals.terminatedControl_validFor
example := @ControlInternals.terminatedControl_preservesTokenWindow
example := @ControlInternals.terminatedControl_cursorMonotoneOnSuccess
example := @ControlInternals.terminatedControl_startsAtCurrentTokenOnSuccess
example := @breakStatement_validFor
example := @continueStatement_validFor
example := @breakStatement_preservesTokenWindow
example := @continueStatement_preservesTokenWindow
example := @breakStatement_cursorMonotoneOnSuccess
example := @continueStatement_cursorMonotoneOnSuccess
example := @breakStatement_startsAtCurrentTokenOnSuccess
example := @continueStatement_startsAtCurrentTokenOnSuccess

end Tests
