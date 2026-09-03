import Solcore.Syntax.DeclarativeIsolatedBlockTraceGrammar
import Solcore.Syntax.Parser.Block

/-! Explicit inner-parser contracts for diagnostic-trace lifting. These are
execution/grammar bridges, not independent syntax or concrete Core guarantees.
All states, including arbitrary existing diagnostics, are quantified. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every inner success has an independently described appended trace. -/
def BlockTraceSuccessSound (parser : Parser Block)
    (blockParses : SourceId → Nat → DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input output : State} {body : Block}, parser input = .ok body output →
    ∃ trace, blockParses input.file.id input.window.endByte
      input.declarativeRemainder body output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace

/-- Every inner ordinary rejection has an exact uncommitted report and a
preceding appended trace; no final report is implicitly added here. -/
def BlockTraceRejectSound (parser : Parser Block)
    (blockRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input rejected : State} {failure : Failure}, parser input = .reject failure rejected →
    ∃ trace, blockRejects input.file.id input.window.endByte
      input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace

/-- Independent inner success executes with the same AST and remainder and
appends its trace after any supplied prior diagnostics. -/
def BlockTraceSuccessComplete (parser : Parser Block)
    (blockParses : SourceId → Nat → DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {body : Block} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic},
    blockParses input.file.id input.window.endByte input.declarativeRemainder body after trace →
      ∃ output, parser input = .ok body output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace

/-- Independent inner rejection executes with the specified report, remainder,
and appended trace. Whole rejected-state or failure-record equality is not assumed. -/
def BlockTraceRejectComplete (parser : Parser Block)
    (blockRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic},
    blockRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace →
      ∃ failure rejected, parser input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        rejected.diagnostics = input.diagnostics ++ trace

end Solcore.Syntax.Parser
