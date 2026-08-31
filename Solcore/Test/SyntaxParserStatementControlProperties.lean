import Solcore.Syntax.Parser.Statement.ControlProperties

/-! External consumers for canonical Core control-statement contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

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

end Tests
