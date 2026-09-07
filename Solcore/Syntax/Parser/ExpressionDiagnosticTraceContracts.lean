import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-! Explicit expression contracts for diagnostic-trace composition. They
quantify arbitrary incoming events and make no concrete Core-expression claim. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

def ExpressionTraceSuccessSound (parser : Parser Expr)
    (expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input output : State} {value : Expr}, parser input = .ok value output →
    ∃ trace, expressionTrace input.file.id input.window.endByte input.declarativeRemainder
      value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace

def ExpressionTraceSuccessComplete (parser : Parser Expr)
    (expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic},
    expressionTrace input.file.id input.window.endByte input.declarativeRemainder value after trace →
      ∃ output, parser input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace

/-- Successful expressions preserve the source and full active token/byte window. -/
def ExpressionSuccessContext (parser : Parser Expr) : Prop :=
  ∀ {input output : State} {value : Expr}, parser input = .ok value output →
    output.file = input.file ∧ output.window = input.window

def ExpressionTraceRejectSound (parser : Parser Expr)
    (expressionRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input rejected : State} {failure : Failure}, parser input = .reject failure rejected →
    ∃ trace, expressionRejects input.file.id input.window.endByte input.declarativeRemainder
      rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace

def ExpressionTraceRejectComplete (parser : Parser Expr)
    (expressionRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop) : Prop :=
  ∀ {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic},
    expressionRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace →
      ∃ failure rejected, parser input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        rejected.diagnostics = input.diagnostics ++ trace

end Solcore.Syntax.Parser
