import Solcore.Syntax.Parser.Statement.SimpleProperties

/-! External consumers for canonical Core-statement leaf contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @StatementSimpleInternals.valueAssignOperator_ok_state_shape
example := @StatementSimpleInternals.valueAssignOperator_ok_validFor
example := @StatementSimpleInternals.valueAssignOperator_reject_state_shape
example := @StatementSimpleInternals.valueAssignOperator_reject_validFor
example := @StatementSimpleInternals.valueAssignOperator_validFor
example := @StatementSimpleInternals.valueAssignOperator_preservesTokenWindow
example :=
  @StatementSimpleInternals.valueAssignOperator_preservesTokensOnSuccess
example :=
  @StatementSimpleInternals.valueAssignOperator_cursorMonotoneOnSuccess
example :=
  @StatementSimpleInternals.valueAssignOperator_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.AssignmentTail.ValidFor
example := @StatementSimpleInternals.AssignmentTail.startSpan
example := @StatementSimpleInternals.assignmentTail_validFor
example := @StatementSimpleInternals.optionalAssignmentTail_validFor
example :=
  @StatementSimpleInternals.assignmentTail_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.assignmentTail_cursor_lt_onSuccess
example := @StatementSimpleInternals.assignmentTail_start_le_endOnSuccess
example :=
  @StatementSimpleInternals.optionalAssignmentTail_some_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.assignmentEnd_validFor
example := @StatementSimpleInternals.statementEnd_validFor
example := @StatementSimpleInternals.assignmentTail_preservesTokenWindow
example := @StatementSimpleInternals.assignmentTail_preservesTokensOnSuccess
example := @StatementSimpleInternals.assignmentTail_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.optionalAssignmentTail_preservesTokenWindow
example :=
  @StatementSimpleInternals.optionalAssignmentTail_preservesTokensOnSuccess
example :=
  @StatementSimpleInternals.optionalAssignmentTail_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.optionalSemicolon_validFor
example := @StatementSimpleInternals.optionalSemicolon_preservesTokenWindow
example := @StatementSimpleInternals.optionalSemicolon_preservesTokensOnSuccess
example := @StatementSimpleInternals.optionalSemicolon_cursorMonotoneOnSuccess
example :=
  @StatementSimpleInternals.optionalSemicolon_some_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.optionalReturnValue_validFor
example := @StatementSimpleInternals.optionalReturnValue_preservesTokenWindow
example :=
  @StatementSimpleInternals.optionalReturnValue_preservesTokensOnSuccess
example :=
  @StatementSimpleInternals.optionalReturnValue_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.optionalLetType_validFor
example := @StatementSimpleInternals.optionalLetType_preservesTokenWindow
example := @StatementSimpleInternals.optionalLetType_preservesTokensOnSuccess
example := @StatementSimpleInternals.optionalLetType_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.optionalLetInitializer_validFor
example :=
  @StatementSimpleInternals.optionalLetInitializer_preservesTokenWindow
example :=
  @StatementSimpleInternals.optionalLetInitializer_preservesTokensOnSuccess
example :=
  @StatementSimpleInternals.optionalLetInitializer_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.forLetItem_preservesTokenWindow
example := @StatementSimpleInternals.forLetItem_preservesTokensOnSuccess
example := @StatementSimpleInternals.forLetItem_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.forLetItem_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.forLetItem_validFor
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_preservesTokenWindow
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_preservesTokensOnSuccess
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_cursorMonotoneOnSuccess
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.forAssignmentOrExpression_validFor
example := @forItem_preservesTokenWindow
example := @forItem_preservesTokensOnSuccess
example := @forItem_cursorMonotoneOnSuccess
example := @forItem_startsAtCurrentTokenOnSuccess
example := @forItem_validFor
example := @letStatement_preservesTokenWindow
example := @letStatement_preservesTokensOnSuccess
example := @letStatement_cursorMonotoneOnSuccess
example := @letStatement_startsAtCurrentTokenOnSuccess
example := @letStatement_span_validOnSuccess
example := @letStatement_validFor
example := @returnStatement_preservesTokenWindow
example := @returnStatement_preservesTokensOnSuccess
example := @returnStatement_cursorMonotoneOnSuccess
example := @returnStatement_startsAtCurrentTokenOnSuccess
example := @returnStatement_span_validOnSuccess
example := @returnStatement_validFor
example := @assignmentOrExpressionStatement_preservesTokenWindow
example := @assignmentOrExpressionStatement_preservesTokensOnSuccess
example := @assignmentOrExpressionStatement_cursorMonotoneOnSuccess
example := @assignmentOrExpressionStatement_startsAtCurrentTokenOnSuccess
example := @assignmentOrExpressionStatement_span_validFor_onSuccess
example := @assignmentOrExpressionStatement_value_validFor_onSuccess
example := @assignmentOrExpressionStatement_validFor

end Tests
