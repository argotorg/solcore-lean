import Solcore.Syntax.Parser.Statement.Control
import Solcore.Syntax.StatementValidity

/-! Contracts for canonical Core control-statement parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A braced statement wrapper retains the block range and every body item. -/
theorem blockStatement_validFor
    (statement : Parser Statement)
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement) :
    (blockStatement statement).ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  unfold blockStatement
  apply Parser.bind_validFor_of_value
    (coreBlock_validFor
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      statement .require statementValid statementTokens
      (fun _ _ valid => valid.span_valid))
  intro body next nextValid bodyValid
  exact ⟨Statement.ValidFor.block bodyValid.1 bodyValid.2, nextValid, rfl⟩

/-- Braced statement wrappers preserve the complete token window. -/
theorem blockStatement_preservesTokenWindow
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (blockStatement statement) := by
  unfold blockStatement
  apply Parser.bind_preservesTokenWindow
    (coreBlock_preservesTokenWindow statement .require statementWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Braced statement wrappers retain the immutable token carrier on success. -/
theorem blockStatement_preservesTokensOnSuccess
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokensOnSuccess (blockStatement statement) :=
  (blockStatement_preservesTokenWindow statement
    statementWindow).preservesTokensOnSuccess

/-- A braced statement wrapper never rewinds the token cursor. -/
theorem blockStatement_cursorMonotoneOnSuccess
    (statement : Parser Statement) :
    Parser.CursorMonotoneOnSuccess (blockStatement statement) := by
  unfold blockStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A braced statement wrapper starts at its opening brace. -/
theorem blockStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) :
    Parser.StartsAtCurrentTokenOnSuccess
      (blockStatement statement) (·.span) := by
  unfold blockStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (coreBlock_startsAtCurrentTokenOnSuccess statement .require)
  intro body input wrapped final parsed
  cases parsed
  rfl

end Solcore.Syntax.Parser
