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
example := @ExpressionInternals.leftAssociativeTail_preservesTokenWindow
example := @ExpressionInternals.leftAssociativeTail_preservesTokensOnSuccess
example := @ExpressionInternals.leftAssociativeTail_cursorMonotoneOnSuccess
example := @ExpressionInternals.leftAssociativeTail_preservesLeftStartOnSuccess
example := @ExpressionInternals.leftAssociativeTail_validFor
example := @ExpressionInternals.leftAssociative_preservesTokenWindow
example := @ExpressionInternals.leftAssociative_preservesTokensOnSuccess
example := @ExpressionInternals.leftAssociative_cursorMonotoneOnSuccess
example := @ExpressionInternals.leftAssociative_startsAtCurrentTokenOnSuccess
example := @ExpressionInternals.leftAssociative_validFor
example := @ExpressionInternals.nonAssociative_preservesTokenWindow
example := @ExpressionInternals.nonAssociative_preservesTokensOnSuccess
example := @ExpressionInternals.nonAssociative_cursorMonotoneOnSuccess
example := @ExpressionInternals.nonAssociative_startsAtCurrentTokenOnSuccess
example := @ExpressionInternals.nonAssociative_validFor
example := @ExpressionInternals.conditional_cursor_lt_onSuccess
example := @ExpressionInternals.expressionUnary_cursor_lt_onSuccess
example := @ExpressionInternals.leftAssociative_cursor_lt_onSuccess
example := @ExpressionInternals.nonAssociative_cursor_lt_onSuccess
example := @ExpressionInternals.ExpressionContract
example := @ExpressionInternals.ExpressionContract.preservesTokensOnSuccess
example := @ExpressionInternals.ExpressionContract.cursorMonotoneOnSuccess
example := @ExpressionInternals.ExpressionContract.unary
example := @ExpressionInternals.ExpressionContract.leftAssociative
example := @ExpressionInternals.ExpressionContract.nonAssociative
example := @ExpressionInternals.ExpressionContract.conditional
example := @ExpressionInternals.expressionLayer_contract
example := @ExpressionInternals.expressionLayer_validFor
example := @ExpressionInternals.expressionLayer_preservesTokenWindow
example := @ExpressionInternals.expressionLayer_preservesTokensOnSuccess
example := @ExpressionInternals.expressionLayer_cursor_lt_onSuccess
example := @ExpressionInternals.expressionLayer_cursorMonotoneOnSuccess
example := @ExpressionInternals.expressionLayer_startsAtCurrentTokenOnSuccess

end Tests
