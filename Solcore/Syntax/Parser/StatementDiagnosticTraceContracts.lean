import Solcore.Syntax.DeclarativeCoreBlockTraceGrammar
import Solcore.Syntax.Parser.BlockDiagnosticTraceContracts

/-! Explicit abstract statement contracts for successful raw-block trace lifting.
They quantify arbitrary existing diagnostics and make no concrete Core claim. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful statement has an independent appended diagnostic suffix. -/
def StatementTraceSuccessSound (parser : Parser Statement)
    (statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input output : State} {statement : Statement}, parser input = .ok statement output →
    ∃ trace, statementTrace input.file.id input.window.endByte input.declarativeRemainder
      statement output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace

/-- Each independent successful statement executes with the same AST, remainder,
and complete appended suffix, regardless of the incoming diagnostic sequence. -/
def StatementTraceSuccessComplete (parser : Parser Statement)
    (statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic},
    statementTrace input.file.id input.window.endByte input.declarativeRemainder statement after trace →
      ∃ output, parser input = .ok statement output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace

/-- Successful statements retain the source and full diagnostic window.
Strict cursor progress is checked separately by the independent block grammar. -/
def StatementSuccessContext (parser : Parser Statement) : Prop :=
  ∀ {input output : State} {statement : Statement}, parser input = .ok statement output →
    output.file = input.file ∧ output.window = input.window

end Solcore.Syntax.Parser
