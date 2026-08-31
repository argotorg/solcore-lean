import Solcore.Syntax.Parser.ExpressionProperties

/-! External consumers for canonical Core expression-layer contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @ExpressionInternals.unaryOperators_validFor
example := @ExpressionInternals.unaryOperators_preservesTokenWindow
example := @ExpressionInternals.unaryOperators_preservesTokensOnSuccess
example := @ExpressionInternals.unaryOperators_cursorMonotoneOnSuccess
example := @ExpressionInternals.applyUnaryOperators_preservesBaseEnd
example := @ExpressionInternals.applyUnaryOperators_validFor
example := @ExpressionInternals.binaryAtPrecedence?_some_state_shape
example := @ExpressionInternals.binaryAtPrecedence?_validFor
example := @ExpressionInternals.consumeBinary_ok_state_shape
example := @ExpressionInternals.consumeBinary_reply_validFor
example := @ExpressionInternals.consumeBinary_preservesTokenWindow
example := @ExpressionInternals.consumeBinary_preservesTokensOnSuccess
example := @ExpressionInternals.consumeBinary_cursor_lt_onSuccess
example := @ExpressionInternals.consumeBinary_cursorMonotoneOnSuccess
example := @ExpressionInternals.binaryNode_validFor
example := @ExpressionInternals.binaryNode_startByte
example := @ExpressionInternals.binaryNode_endByte

end Tests
