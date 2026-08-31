import Solcore.Syntax.Parser.Expression.AtomProperties

/-! External consumers for canonical Core expression-atom contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @ExpressionAtomInternals.expressionName_validFor
example := @ExpressionAtomInternals.expressionName_preservesTokenWindow
example := @ExpressionAtomInternals.expressionName_preservesTokensOnSuccess
example := @ExpressionAtomInternals.expressionName_ok_state_shape
example := @ExpressionAtomInternals.expressionName_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.expressionName_cursor_lt_onSuccess
example := @ExpressionAtomInternals.expressionName_startsAtCurrentTokenOnSuccess

end Tests
