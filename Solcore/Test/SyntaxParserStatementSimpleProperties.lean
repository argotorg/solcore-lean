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

end Tests
