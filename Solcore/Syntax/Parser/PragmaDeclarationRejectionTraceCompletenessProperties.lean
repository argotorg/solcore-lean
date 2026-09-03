import Solcore.Syntax.Parser.PragmaDeclarationRejectionTraceProperties

/-! Complete independent pragma rejection, including every failure field. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- An independently derived rejecting trace fixes an existing execution's
endpoint, uncommitted report, and exact retained diagnostic sequence. -/
theorem pragmaDecl_reject_exact_of_trace
    {input output : State} {failure : Failure} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .reject failure output)
    (traced : DeclarativeGrammar.PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace) :
    output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaDecl_reject_trace_sound result with ⟨actualTrace, actual, diagnostics⟩
  rcases actual.result_unique traced with ⟨after, report, events⟩
  exact ⟨after, report, events ▸ diagnostics⟩

/-- Independent first-failure grammar and exact execution are equivalent.
No input-validity or empty-prior-diagnostics premise is required. -/
theorem pragmaDecl_trace_reject_iff
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace ↔
      ∃ failure output, pragmaDecl input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    cases result : pragmaDecl input with
    | ok declaration output =>
        exact False.elim (pragmaDecl_exactOutcomeSpec.successRejectDisjoint traced.ordinary
          ⟨declaration, output.declarativeRemainder,
            pragmaDecl_success_ordinaryOutcome_sound result⟩)
    | invariant error =>
        exact False.elim (pragmaDecl_ne_invariant input error result)
    | reject failure output =>
        exact ⟨failure, output, rfl, pragmaDecl_reject_exact_of_trace result traced⟩
  · rintro ⟨failure, output, result, after, report, diagnostics⟩
    rcases pragmaDecl_reject_trace_sound result with
      ⟨actualTrace, actual, actualDiagnostics⟩
    have events : actualTrace = trace :=
      List.append_cancel_left (actualDiagnostics.symm.trans diagnostics)
    simpa only [after, report, events] using actual

/-- Diagnostic projection is injective on failures, so the relation can fix
the complete uncommitted failure, not just its later diagnostic rendering. -/
theorem pragmaDecl_trace_reject_failure_iff
    {input : State} {failure : Failure} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaDeclTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace ↔
      ∃ output, pragmaDecl input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    rcases pragmaDecl_trace_reject_iff.mp traced with
      ⟨actual, output, result, after, report, diagnostics⟩
    have failureEq := Failure.toDiagnostic_injective report
    subst actual
    exact ⟨output, result, after, diagnostics⟩
  · rintro ⟨output, result, after, diagnostics⟩
    exact pragmaDecl_trace_reject_iff.mpr
      ⟨failure, output, result, after, rfl, diagnostics⟩

end Solcore.Syntax.Parser
