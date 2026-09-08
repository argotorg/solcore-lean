import Solcore.Syntax.Parser.ExpressionAtomLayerTraceProperties
import Solcore.Syntax.Parser.ExpressionAtomUnrestrictedFuelTotalityProperties

/-! Non-vacuous trace existence for a bounded atom layer follows ordinary
execution and soundness. The strict-progress/end-index child contract is explicit;
no independent exactness or completeness premise substitutes for totality. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionAtomCore_exists_trace_outcome_of_unrestrictedElementFuel
    (nestedFuel : Nat) (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
    (blockRejectSound : ParserTraceRejectSound block blockRejects)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value output trace,
      expressionAtomCore nested block input = .ok value output ∧
      ExpressionAtomDispatchTraceParses nestedTrace blockTrace input.file.id input.window.endByte
        input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionAtomCore nested block input = .reject failure rejected ∧
      ExpressionAtomDispatchTraceRejects nestedTrace nestedRejects blockRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionAtomCore_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract blockOrdinary input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionAtomCore_trace_success_sound successSound contextFrame blockSuccessSound result with
      ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionAtomCore_reject_trace_sound successSound rejectSound contextFrame blockRejectSound result with
      ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionAtom_layer_exists_trace_outcome_of_unrestrictedElementFuel
    (nestedFuel : Nat) (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
    (blockRejectSound : ParserTraceRejectSound block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value output trace,
      expressionAtom nested block input = .ok value output ∧
      ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects input.file.id input.window.endByte
        input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionAtom nested block input = .reject failure rejected ∧
      ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionAtom_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract blockOrdinary input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionAtom_layer_trace_success_sound successSound rejectSound contextFrame blockSuccessSound blockRejectSound
      nestedRejectFrame blockRejectFrame result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionAtom_layer_reject_trace_sound successSound rejectSound contextFrame blockRejectSound
      nestedRejectFrame blockRejectFrame result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionAtomLayerTrace_outcome_exists_of_unrestrictedElementFuel
    (nestedFuel : Nat) (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
    (blockRejectSound : ParserTraceRejectSound block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (source : SourceId) (endByte : Nat) (input : Remainder)
    (adequate : input.endIndex - input.cursor < nestedFuel + 1) :
    (∃ value output trace, ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects
      source endByte input value output trace) ∨
    (∃ rejected report trace, ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects
      source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  rcases expressionAtom_layer_exists_trace_outcome_of_unrestrictedElementFuel nestedFuel contract blockOrdinary
      successSound rejectSound contextFrame blockSuccessSound blockRejectSound nestedRejectFrame blockRejectFrame
      state adequate with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, rejection⟩

end Solcore.Syntax.Parser
