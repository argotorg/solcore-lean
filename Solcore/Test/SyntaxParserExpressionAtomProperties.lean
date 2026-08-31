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
example := @ExpressionAtomInternals.literalExpression_validFor
example := @ExpressionAtomInternals.literalExpression_preservesTokenWindow
example := @ExpressionAtomInternals.literalExpression_preservesTokensOnSuccess
example := @ExpressionAtomInternals.literalExpression_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.literalExpression_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.identifierExpression_validFor
example := @ExpressionAtomInternals.identifierExpression_preservesTokenWindow
example := @ExpressionAtomInternals.identifierExpression_preservesTokensOnSuccess
example := @ExpressionAtomInternals.identifierExpression_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.identifierExpression_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.proxyExpression_validFor
example := @ExpressionAtomInternals.proxyExpression_preservesTokenWindow
example := @ExpressionAtomInternals.proxyExpression_preservesTokensOnSuccess
example := @ExpressionAtomInternals.proxyExpression_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.proxyExpression_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.dotConstructor_validFor
example := @ExpressionAtomInternals.dotConstructor_preservesTokenWindow
example := @ExpressionAtomInternals.dotConstructor_preservesTokensOnSuccess
example := @ExpressionAtomInternals.dotConstructor_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.dotConstructor_startsAtCurrentTokenOnSuccess

end Tests
