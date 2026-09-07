import Solcore.Syntax.Parser.TypeUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.TypeExprTraceSoundnessProperties

/-! Non-vacuous recursive trace existence, proved through actual execution.
Unrestricted production totality provides an ordinary reply, and soundness
provides its independent trace. Exactness alone is not an existence argument.
The arbitrary-remainder corollary stays in the parser layer: constructing a
state here does not add execution to the independent grammar definitions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

/-- Every state has an actual ordinary outcome and its exact diagnostic trace,
including states with arbitrary prior events or inconsistent carrier bounds. -/
theorem typeExpr_exists_trace_outcome (input : State) :
    (∃ value output trace,
      typeExpr input = .ok value output ∧
      TypeExprTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      typeExpr input = .reject failure rejected ∧
      TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases typeExpr_ordinary input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases typeExpr_trace_success_sound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases typeExpr_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

/-- Every independent remainder has a success or rejection derivation. This is
an execution-derived existence theorem, not a consequence of outcome uniqueness.
Neither byte/token provenance nor cursor/window consistency is assumed. -/
theorem typeExprTrace_outcome_exists (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, TypeExprTraceParses source endByte input value output trace) ∨
    (∃ rejected report trace, TypeExprTraceRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases typeExpr_exists_trace_outcome state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser
