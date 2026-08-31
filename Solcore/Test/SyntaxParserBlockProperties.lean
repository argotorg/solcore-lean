import Solcore.Syntax.Parser.Block

/-! External consumers for canonical Core-block progress contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @coreBlock_preservesTokensOnSuccess
example := @coreBlock_cursor_lt_onSuccess
example := @coreBlock_cursorMonotoneOnSuccess

example (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (coreBlock statement policy) :=
  coreBlock_preservesTokensOnSuccess statement policy statementShape

example (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    {input next : State} {body : Block}
    (result : coreBlock statement policy input = .ok body next) :
    next.tokens = input.tokens ∧ input.cursor < next.cursor :=
  ⟨coreBlock_preservesTokensOnSuccess statement policy statementShape
      input body next result,
    coreBlock_cursor_lt_onSuccess statement policy result⟩

end Tests
