import Solcore.Syntax.DeclarativeCoreBlockRejectionTraceGrammar
import Solcore.Syntax.Parser.StatementDiagnosticTraceContracts

/-! Explicit statement rejection contracts for raw-block trace composition.
The final failure report remains separate from events already emitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every rejected statement supplies its exact uncommitted diagnostic and
the complete suffix appended after arbitrary incoming diagnostics. -/
def StatementTraceRejectSound (parser : Parser Statement)
    (statementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input rejected : State} {failure : Failure}, parser input = .reject failure rejected →
    ∃ trace, statementRejects input.file.id input.window.endByte input.declarativeRemainder
      rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace

/-- Every independent statement rejection executes at its exact remainder,
with the specified failure report and preceding events, for any prior state. -/
def StatementTraceRejectComplete (parser : Parser Statement)
    (statementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic},
    statementRejects input.file.id input.window.endByte input.declarativeRemainder
      after diagnostic trace →
      ∃ failure rejected, parser input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        rejected.diagnostics = input.diagnostics ++ trace

end Solcore.Syntax.Parser
