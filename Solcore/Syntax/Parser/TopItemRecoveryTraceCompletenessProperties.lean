import Solcore.Syntax.DeclarativeTopItemRecoveryTrace
import Solcore.Syntax.Parser.TopItemRecoveryTraceProperties

/-! Exact executable correspondence for independent top-item recovery traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Interpret span events at the fixed top-item recovery kind and site. -/
def topItemRecoveryDiagnostics (trace : List SourceSpan) : List ParseDiagnostic :=
  trace.map fun span => { span, kind := .recovered .topItem }

/-- No event span is lost when recovery events become diagnostics. -/
@[simp] theorem topItemRecoveryDiagnostics_spans (trace : List SourceSpan) :
    (topItemRecoveryDiagnostics trace).map ParseDiagnostic.span = trace := by
  simp [topItemRecoveryDiagnostics, List.map_map, Function.comp_def]

/-- The diagnostic interpretation preserves the complete event sequence. -/
theorem topItemRecoveryDiagnostics_injective :
    Function.Injective topItemRecoveryDiagnostics := by
  intro left right equal
  have spans := congrArg (List.map ParseDiagnostic.span) equal
  simpa only [topItemRecoveryDiagnostics_spans] using spans

/-- Independent recovery success is equivalent to execution with the same
AST, endpoint, and exact raw trace appended after prior diagnostics. -/
theorem recoverTopItem_trace_success_iff
    {input : State} {item : TopItem}
    {remainder : DeclarativeGrammar.Remainder} {trace : List SourceSpan} :
    DeclarativeGrammar.TopItemRecoveryTraceParses
      input.declarativeRemainder item remainder trace ↔
      ∃ output, recoverTopItem input = .ok item output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++
          topItemRecoveryDiagnostics trace := by
  rw [DeclarativeGrammar.topItemRecoveryTraceParses_iff]
  constructor
  · rintro ⟨parsed, rfl⟩
    simpa only [topItemRecoveryDiagnostics, List.map_cons, List.map_nil] using
      recoverTopItem_ordinary_success_iff_with_trace.mp parsed
  · rintro ⟨output, result, after, traceEq⟩
    refine ⟨recoverTopItem_ordinary_success_iff.mpr ⟨output, result, after⟩, ?_⟩
    have singleton := recoverTopItem_success_diagnostics_eq result
    have mapped : topItemRecoveryDiagnostics trace =
        topItemRecoveryDiagnostics [item.span] :=
      List.append_cancel_left (traceEq.symm.trans singleton)
    exact topItemRecoveryDiagnostics_injective mapped

/-- Independent recovery rejection is equivalent to the same rejected
endpoint and an empty appended trace, without fixing the failure payload. -/
theorem recoverTopItem_trace_reject_iff
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {trace : List SourceSpan} :
    DeclarativeGrammar.TopItemRecoveryTraceRejects
      input.declarativeRemainder remainder trace ↔
      ∃ failure output, recoverTopItem input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++
          topItemRecoveryDiagnostics trace := by
  rw [DeclarativeGrammar.topItemRecoveryTraceRejects_iff]
  constructor
  · rintro ⟨rejected, rfl⟩
    simpa only [topItemRecoveryDiagnostics, List.map_nil, List.append_nil] using
      recoverTopItem_ordinary_reject_iff_with_trace.mp rejected
  · rintro ⟨failure, output, result, after, traceEq⟩
    refine ⟨recoverTopItem_ordinary_reject_iff.mpr
      ⟨failure, output, result, after⟩, ?_⟩
    have unchanged := recoverTopItem_reject_diagnostics_eq result
    have appended : input.diagnostics ++ topItemRecoveryDiagnostics trace =
        input.diagnostics ++ topItemRecoveryDiagnostics [] := by
      simpa only [topItemRecoveryDiagnostics, List.map_nil, List.append_nil]
        using traceEq.symm.trans unchanged
    exact topItemRecoveryDiagnostics_injective (List.append_cancel_left appended)

end Solcore.Syntax.Parser.FileInternals
