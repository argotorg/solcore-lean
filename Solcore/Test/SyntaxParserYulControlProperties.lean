import Solcore.Syntax.Parser.Yul.ControlSwitchProperties

/-! External compile consumers for inline-Yul `if` parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulIfStatement_validFor
example := @yulIfStatement_preservesTokensOnSuccess
example := @yulIfStatement_cursorMonotoneOnSuccess
example := @yulIfStatement_startsAtCurrentTokenOnSuccess
example := @yulForStatement_validFor
example := @yulForStatement_preservesTokensOnSuccess
example := @yulForStatement_cursorMonotoneOnSuccess
example := @yulForStatement_startsAtCurrentTokenOnSuccess
example := @yulFunctionStatement_validFor
example := @yulFunctionStatement_preservesTokensOnSuccess
example := @yulFunctionStatement_cursorMonotoneOnSuccess
example := @yulFunctionStatement_startsAtCurrentTokenOnSuccess
example := @yulCase_validFor
example := @yulCase_preservesTokensOnSuccess
example := @yulCase_cursorMonotoneOnSuccess
example := @yulCases_preservesTokensOnSuccess
example := @yulCases_cursorMonotoneOnSuccess
example := @yulCases_validFor
example := @yulCase_startsAtCurrentTokenOnSuccess
example := @yulCase_cursor_lt_onSuccess
example := @optionalYulDefault_validFor
example := @optionalYulDefault_preservesTokensOnSuccess
example := @optionalYulDefault_cursorMonotoneOnSuccess
example := @yulSwitchStatement_validFor
example := @yulSwitchStatement_preservesTokensOnSuccess
example := @yulSwitchStatement_cursorMonotoneOnSuccess
example := @yulSwitchStatement_startsAtCurrentTokenOnSuccess

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

example (nested : Parser YulStmt)
    (expressionValid : yulExpression.ValidFor YulExpr.ValidFor)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (yulForStatement nested).ValidFor YulStmt.ValidFor :=
  yulForStatement_validFor nested expressionValid expressionPreserves
    expressionMonotone nestedValid nestedPreserves

example (nested : Parser YulStmt)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulForStatement nested) :=
  yulForStatement_preservesTokensOnSuccess nested expressionPreserves
    nestedPreserves

example (nested : Parser YulStmt)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (yulForStatement nested) :=
  yulForStatement_cursorMonotoneOnSuccess nested expressionMonotone
    nestedPreserves

example (nested : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulForStatement nested) (·.span) :=
  yulForStatement_startsAtCurrentTokenOnSuccess nested

end Tests
