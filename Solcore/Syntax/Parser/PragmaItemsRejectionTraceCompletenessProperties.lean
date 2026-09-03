import Solcore.Syntax.Parser.PragmaItemsRejectionTraceProperties

/-! Complete rejecting pragma-item traces without state-validity assumptions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

/-- Fixed accumulated names do not alter the new trace or the uncommitted
report. Production-tail rejection is exactly the independent trace relation. -/
theorem pragmaItemsTail_production_trace_reject_iff
    (itemsRev : List Identifier) {input : State}
    {remainder : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTailTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace ↔
      ∃ failure output,
        pragmaItemsTail (input.remainingCount + 1) itemsRev input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        failure.toDiagnostic = diagnostic ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    cases result : pragmaItemsTail (input.remainingCount + 1) itemsRev input with
    | ok items output =>
        rcases traced with ⟨consumed, rejected, _, _⟩
        rcases pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev result with
          ⟨suffix, _, ordinary⟩
        exact False.elim (pragmaItemsTail_exactOutcomeSpec.successRejectDisjoint
          rejected.ordinary ⟨suffix, output.declarativeRemainder, ordinary⟩)
    | invariant error =>
        exact False.elim (pragmaItemsTail_production_ne_invariant itemsRev input error result)
    | reject failure output =>
        rcases pragmaItemsTail_reject_trace_sound (input.remainingCount + 1)
            itemsRev input failure output result with
          ⟨actualTrace, actual, diagnostics⟩
        rcases actual.result_unique traced with ⟨after, report, events⟩
        exact ⟨failure, output, rfl, after, report, events ▸ diagnostics⟩
  · rintro ⟨failure, output, result, after, report, diagnostics⟩
    rcases pragmaItemsTail_reject_trace_sound (input.remainingCount + 1)
        itemsRev input failure output result with
      ⟨actualTrace, actual, actualDiagnostics⟩
    have events : actualTrace = trace :=
      List.append_cancel_left (actualDiagnostics.symm.trans diagnostics)
    simpa only [after, report, events] using actual

/-- Complete item rejection fixes the endpoint, exact failure report, and
ordered committed events, independently of all pre-existing diagnostics. -/
theorem pragmaItems_trace_reject_iff
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder diagnostic trace ↔
      ∃ failure output, pragmaItems input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        failure.toDiagnostic = diagnostic ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    cases result : pragmaItems input with
    | ok items output =>
        rcases traced with ⟨consumed, rejected, _, _⟩
        exact False.elim (pragmaItems_exactOutcomeSpec.successRejectDisjoint
          rejected.ordinary ⟨items, output.declarativeRemainder,
            pragmaItems_success_ordinaryOutcome_sound result⟩)
    | invariant error =>
        exact False.elim (pragmaItems_ne_invariant input error result)
    | reject failure output =>
        rcases pragmaItems_reject_trace_sound result with
          ⟨actualTrace, actual, diagnostics⟩
        rcases actual.result_unique traced with ⟨after, report, events⟩
        exact ⟨failure, output, rfl, after, report, events ▸ diagnostics⟩
  · rintro ⟨failure, output, result, after, report, diagnostics⟩
    rcases pragmaItems_reject_trace_sound result with
      ⟨actualTrace, actual, actualDiagnostics⟩
    have events : actualTrace = trace :=
      List.append_cancel_left (actualDiagnostics.symm.trans diagnostics)
    simpa only [after, report, events] using actual

/-- Report conversion loses no information: tail traces fix every field of
the uncommitted failure itself, not only its eventual diagnostic projection. -/
theorem pragmaItemsTail_production_trace_reject_failure_iff
    (itemsRev : List Identifier) {input : State} {failure : Failure}
    {remainder : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTailTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace ↔
      ∃ output,
        pragmaItemsTail (input.remainingCount + 1) itemsRev input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    rcases (pragmaItemsTail_production_trace_reject_iff itemsRev).mp traced with
      ⟨actual, output, result, after, report, diagnostics⟩
    have failureEq := Failure.toDiagnostic_injective report
    subst actual
    exact ⟨output, result, after, diagnostics⟩
  · rintro ⟨output, result, after, diagnostics⟩
    exact (pragmaItemsTail_production_trace_reject_iff itemsRev).mpr
      ⟨failure, output, result, after, rfl, diagnostics⟩

/-- Independent complete item traces likewise fix the entire failure payload. -/
theorem pragmaItems_trace_reject_failure_iff
    {input : State} {failure : Failure} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder remainder failure.toDiagnostic trace ↔
      ∃ output, pragmaItems input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    rcases pragmaItems_trace_reject_iff.mp traced with
      ⟨actual, output, result, after, report, diagnostics⟩
    have failureEq := Failure.toDiagnostic_injective report
    subst actual
    exact ⟨output, result, after, diagnostics⟩
  · rintro ⟨output, result, after, diagnostics⟩
    exact pragmaItems_trace_reject_iff.mpr
      ⟨failure, output, result, after, rfl, diagnostics⟩

end Solcore.Syntax.Parser.PragmaInternals
