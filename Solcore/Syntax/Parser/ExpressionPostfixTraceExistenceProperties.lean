import Solcore.Syntax.Parser.ExpressionPostfixTraceSoundnessProperties
import Solcore.Syntax.Parser.ExpressionPostfixUnrestrictedFuelTotalityProperties

/-! Separate non-vacuous postfix outcomes follow bounded ordinary execution
and soundness. The atom contract remains explicit; joint exactness and child
completeness are neither assumed nor substituted for runtime totality. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {atomTrace nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {atomRejects nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (atomSound : ParserTraceSuccessSound (expressionAtom nested block) atomTrace)
  (atomRejectSound : ParserTraceRejectSound (expressionAtom nested block) atomRejects)
  (atomContext : ParserSuccessContext (expressionAtom nested block))
  (nestedSound : ParserTraceSuccessSound nested nestedTrace)
  (nestedRejectSound : ParserTraceRejectSound nested nestedRejects)
  (nestedContext : ParserSuccessContext nested)
  (atomFuel nestedFuel : Nat)
  (atomContract : UnrestrictedFuelElementContract (expressionAtom nested block) atomFuel)
  (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)

include atomSound atomRejectSound atomContext nestedSound nestedRejectSound nestedContext
  atomContract nestedContract

theorem expressionPostfix_exists_trace_outcome_of_unrestrictedElementFuels
    (input : State) (atomAdequate : input.remainingCount < atomFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) :
    (∃ value output trace,
      expressionPostfix nested block input = .ok value output ∧
      ExpressionPostfixTraceParses atomTrace nestedTrace input.file.id input.window.endByte
        input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionPostfix nested block input = .reject failure rejected ∧
      ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
        input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionPostfix_ordinary_of_unrestrictedElementFuels nested block atomFuel nestedFuel
      atomContract nestedContract input atomAdequate nestedAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionPostfix_trace_success_sound atomSound atomContext nestedSound nestedContext result with
      ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionPostfix_reject_trace_sound atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionPostfixTrace_outcome_exists_of_unrestrictedElementFuels
    (source : SourceId) (endByte : Nat) (input : Remainder)
    (atomAdequate : input.endIndex - input.cursor < atomFuel)
    (nestedAdequate : input.endIndex - input.cursor < nestedFuel + 1) :
    (∃ value after trace, ExpressionPostfixTraceParses atomTrace nestedTrace source endByte input value after trace) ∨
    (∃ rejected report trace, ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  rcases expressionPostfix_exists_trace_outcome_of_unrestrictedElementFuels atomSound atomRejectSound
      atomContext nestedSound nestedRejectSound nestedContext atomFuel nestedFuel atomContract nestedContract
      state atomAdequate nestedAdequate with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, rejection⟩

end Solcore.Syntax.Parser
