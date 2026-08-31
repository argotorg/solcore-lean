import Solcore.Syntax.Parser.Yul.ExpressionProperties

/-! External compile consumers for inline-Yul expression-layer contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @optionalYulCallArguments_validFor
example := @rejectedMeta_validFor

example (nested : Parser YulExpr)
    (preserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulExpressionCore nested) :=
  yulExpressionCore_preservesTokensOnSuccess nested preserves

example (nested : Parser YulExpr) :
    Parser.CursorMonotoneOnSuccess (yulExpressionCore nested) :=
  yulExpressionCore_cursorMonotoneOnSuccess nested

example (nested : Parser YulExpr) {input next : State} {expression : YulExpr}
    (parsed : yulExpressionCore nested input = .ok expression next) :
    input.cursor < next.cursor :=
  yulExpressionCore_cursor_lt_onSuccess nested parsed

end Tests
