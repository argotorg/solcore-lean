import Solcore.Syntax.Parser.ExpressionProperties

/-! External consumers for canonical Core expression-layer contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @ExpressionInternals.unaryOperators_validFor
example := @ExpressionInternals.unaryOperators_preservesTokenWindow
example := @ExpressionInternals.unaryOperators_preservesTokensOnSuccess
example := @ExpressionInternals.unaryOperators_cursorMonotoneOnSuccess

end Tests
