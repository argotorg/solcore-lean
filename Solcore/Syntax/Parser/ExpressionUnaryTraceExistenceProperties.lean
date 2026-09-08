import Solcore.Syntax.Parser.ExpressionUnaryTraceProperties
import Solcore.Syntax.Parser.ExpressionUnaryUnrestrictedFuelContractProperties

/-! Bounded unary trace existence is separate from unary joint exactness.
Successful silent prefix scanning and a bounded postfix contract supply actual
ordinary execution; corresponding soundness supplies its independent trace. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {postfixTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound (expressionPostfix nested block) postfixTrace)
  (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects)
  (fuel : Nat) (contract : UnrestrictedFuelElementContract (expressionPostfix nested block) fuel)

include successSound rejectSound contract

theorem expressionUnary_exists_trace_outcome_of_unrestrictedPostfixFuel
    (input : State) (adequate : input.remainingCount < fuel) :
    (∃ value output trace,
      expressionUnary nested block input = .ok value output ∧
      ExpressionUnaryTraceParses postfixTrace input.file.id input.window.endByte
        input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionUnary nested block input = .reject failure rejected ∧
      ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionUnary_ordinary_of_unrestrictedPostfixFuel nested block fuel contract input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionUnary_trace_success_sound successSound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionUnary_reject_trace_sound rejectSound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionUnaryTrace_outcome_exists_of_unrestrictedPostfixFuel
    (source : SourceId) (endByte : Nat) (input : Remainder)
    (adequate : input.endIndex - input.cursor < fuel) :
    (∃ value after trace, ExpressionUnaryTraceParses postfixTrace source endByte input value after trace) ∨
    (∃ rejected report trace, ExpressionUnaryTraceRejects postfixRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  rcases expressionUnary_exists_trace_outcome_of_unrestrictedPostfixFuel successSound rejectSound fuel contract state adequate with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, rejection⟩

end Solcore.Syntax.Parser.ExpressionInternals
