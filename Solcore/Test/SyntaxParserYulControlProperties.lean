import Solcore.Syntax.Parser.Yul.ControlProperties

/-! External compile consumers for inline-Yul `if` parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulIfStatement_validFor
example := @yulIfStatement_preservesTokensOnSuccess
example := @yulIfStatement_cursorMonotoneOnSuccess
example := @yulIfStatement_startsAtCurrentTokenOnSuccess

example (nested : Parser YulStmt)
    (expressionValid : yulExpression.ValidFor YulExpr.ValidFor)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess yulExpression (·.span))
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (yulIfStatement nested).ValidFor YulStmt.ValidFor :=
  yulIfStatement_validFor nested expressionValid expressionStarts
    expressionPreserves expressionMonotone nestedValid nestedPreserves

example (nested : Parser YulStmt)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulIfStatement nested) :=
  yulIfStatement_preservesTokensOnSuccess nested expressionPreserves
    nestedPreserves

example (nested : Parser YulStmt)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (yulIfStatement nested) :=
  yulIfStatement_cursorMonotoneOnSuccess nested expressionMonotone
    nestedPreserves

example (nested : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulIfStatement nested) (·.span) :=
  yulIfStatement_startsAtCurrentTokenOnSuccess nested

end Tests
