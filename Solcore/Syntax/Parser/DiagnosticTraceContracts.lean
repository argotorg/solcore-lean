import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-! Generic execution contracts for complete appended diagnostic traces.
All incoming states and prior diagnostics are quantified. Source/full-window
preservation is separate; token-carrier preservation is not assumed here. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

def ParserTraceSuccessSound {α : Type} (parser : Parser α)
    (traceParses : SourceId → Nat → DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input output : State} {value : α}, parser input = .ok value output →
    ∃ trace, traceParses input.file.id input.window.endByte input.declarativeRemainder
      value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace

def ParserTraceSuccessComplete {α : Type} (parser : Parser α)
    (traceParses : SourceId → Nat → DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {value : α} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic},
    traceParses input.file.id input.window.endByte input.declarativeRemainder value after trace →
      ∃ output, parser input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace

def ParserSuccessContext {α : Type} (parser : Parser α) : Prop :=
  ∀ {input output : State} {value : α}, parser input = .ok value output →
    output.file = input.file ∧ output.window = input.window

def ParserTraceRejectSound {α : Type} (parser : Parser α)
    (traceRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input rejected : State} {failure : Failure}, parser input = .reject failure rejected →
    ∃ trace, traceRejects input.file.id input.window.endByte input.declarativeRemainder
      rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace

def ParserTraceRejectComplete {α : Type} (parser : Parser α)
    (traceRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic},
    traceRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace →
      ∃ failure rejected, parser input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        rejected.diagnostics = input.diagnostics ++ trace

end Solcore.Syntax.Parser
