import Solcore.Syntax.Parser.Statement.ForItemFuelTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementForItemFuelTotalityProperties

open Solcore.Syntax.Parser

example := @StatementSimpleInternals.forLetItem_ordinary_of_expressionFuel
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_ordinary_of_expressionFuel
example := @StatementSimpleInternals.forLetItem_cursor_lt_onSuccess
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_cursor_lt_onSuccess
example := @forItem_ordinary_of_expressionFuel
example := @forItem_cursor_lt_onSuccess
example := @forItem_fuelElementTotalityContract

end Solcore.Test.SyntaxParserStatementForItemFuelTotalityProperties
