import Solcore.Syntax.Parser.ExpressionPostfixLayerTraceProperties
import Solcore.Syntax.Parser.ExpressionPostfixUnrestrictedChildContractProperties

/-! Child-only bounded existence for the concrete selected/recovering
atom-plus-postfix layer. Ordinary execution constructs its atom contract;
soundness supplies the independent trace. Neither joint exactness nor child
completeness is used to stand in for outcome existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound nested nestedTrace)
  (rejectSound : ParserTraceRejectSound nested nestedRejects)
  (contextFrame : ParserSuccessContext nested)
  (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
  (blockRejectSound : ParserTraceRejectSound block blockRejects)
  (blockContext : ParserSuccessContext block)
  (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
    rejected.file = input.file ∧ rejected.window = input.window)
  (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
    rejected.file = input.file ∧ rejected.window = input.window)
  (nestedFuel bodyFuel : Nat)
  (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
  (bodyContract : UnrestrictedFuelElementContract block bodyFuel)

include successSound rejectSound contextFrame blockSuccessSound blockRejectSound blockContext
  nestedRejectFrame blockRejectFrame nestedContract bodyContract

theorem expressionPostfix_layer_exists_trace_outcome_of_unrestrictedChildFuels
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) :
    (∃ value output trace,
      expressionPostfix nested block input = .ok value output ∧
      ExpressionPostfixLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects
        input.file.id input.window.endByte input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionPostfix nested block input = .reject failure rejected ∧
      ExpressionPostfixLayerTraceRejects nestedTrace nestedRejects blockTrace blockRejects
        input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionPostfix_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract
      (fun result => congrArg TokenWindow.endIndex (nestedRejectFrame result).2)
      (fun result => congrArg TokenWindow.endIndex (blockRejectFrame result).2)
      input nestedAdequate bodyAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionPostfix_layer_trace_success_sound successSound rejectSound contextFrame
      blockSuccessSound blockRejectSound blockContext nestedRejectFrame blockRejectFrame result with
        ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionPostfix_layer_reject_trace_sound successSound rejectSound contextFrame
      blockSuccessSound blockRejectSound blockContext nestedRejectFrame blockRejectFrame result with
        ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionPostfixLayerTrace_outcome_exists_of_unrestrictedChildFuels
    (source : SourceId) (endByte : Nat) (input : Remainder)
    (nestedAdequate : input.endIndex - input.cursor < nestedFuel + 1)
    (bodyAdequate : input.endIndex - input.cursor < bodyFuel + 1) :
    (∃ value after trace, ExpressionPostfixLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects
      source endByte input value after trace) ∨
    (∃ rejected report trace, ExpressionPostfixLayerTraceRejects nestedTrace nestedRejects blockTrace blockRejects
      source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  rcases expressionPostfix_layer_exists_trace_outcome_of_unrestrictedChildFuels successSound rejectSound contextFrame
      blockSuccessSound blockRejectSound blockContext nestedRejectFrame blockRejectFrame nestedFuel bodyFuel
      nestedContract bodyContract state nestedAdequate bodyAdequate with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, rejection⟩

end Solcore.Syntax.Parser
