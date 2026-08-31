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
example := @assignmentOrExpressionStatement_preservesTokenWindow
example := @assignmentOrExpressionStatement_preservesTokensOnSuccess
example := @assignmentOrExpressionStatement_cursorMonotoneOnSuccess
example := @assignmentOrExpressionStatement_startsAtCurrentTokenOnSuccess

end Tests
