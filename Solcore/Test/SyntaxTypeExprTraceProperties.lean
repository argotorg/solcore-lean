import Solcore.Syntax.DeclarativeTypeExprTraceStructuralProperties
import Solcore.Syntax.Parser.TypeExprTraceSoundnessProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Public recursive execution supplies its own child trace evidence. Arbitrary
prior events remain in order, and normalization retains the entire fresh suffix;
the final rejection report is separate from that suffix. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeExprTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem successful_type_keeps_ordinary_structure_and_protected_events
    {input output : State} {value : TypeExpr}
    (result : typeExpr input = .ok value output) (lexical : List LexicalDiagnostic) :
    ∃ trace,
      TypeExprTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧
      TypeExprParses input.declarativeRemainder value output.declarativeRemainder ∧
      output.tokens = input.tokens ∧ output.window.endIndex = input.window.endIndex ∧
      output.diagnostics = input.diagnostics ++ trace ∧
      filterParseDiagnostics input.file lexical output.diagnostics =
        filterParseDiagnostics input.file lexical input.diagnostics ++ trace := by
  rcases typeExpr_trace_success_sound result with ⟨trace, parsed, events⟩
  refine ⟨trace, parsed, parsed.ordinary, parsed.output_window.1,
    parsed.output_window.2, events, ?_⟩
  rw [events, filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics input.file lexical input.diagnostics ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters input.file lexical
      (parsed.cascadeFilters input.file.content (lexical.map (·.span))))

theorem rejected_type_keeps_report_separate_from_protected_events
    {input rejected : State} {failure : Failure}
    (result : typeExpr input = .reject failure rejected) (lexical : List LexicalDiagnostic) :
    ∃ trace,
      TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace ∧
      filterParseDiagnostics input.file lexical rejected.diagnostics =
        filterParseDiagnostics input.file lexical input.diagnostics ++ trace := by
  rcases typeExpr_reject_trace_sound result with ⟨trace, rejection, events⟩
  refine ⟨trace, rejection, events, ?_⟩
  rw [events, filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics input.file lexical input.diagnostics ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters input.file lexical
      (rejection.cascadeFilters input.file.content (lexical.map (·.span))))

end Solcore.Test.SyntaxTypeExprTraceProperties
