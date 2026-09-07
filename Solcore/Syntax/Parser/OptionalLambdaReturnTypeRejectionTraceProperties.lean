import Solcore.Syntax.Parser.OptionalLambdaReturnTypeTraceProperties
import Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties

/-! A selected arrow propagates the actual type rejection unchanged. The
arrow-absent branch cannot reject, so there is no raw missing-arrow report. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {typeRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem optionalLambdaReturnType_reject_iff_type
    {input rejected : State} {failure : Failure} :
    optionalLambdaReturnType input = .reject failure rejected ↔
    isSymbol input .arrow = true ∧
      typeExpr { input with cursor := input.cursor + 1 } = .reject failure rejected := by
  by_cases present : isSymbol input .arrow = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with ⟨arrow, arrowResult⟩
    rw [optionalLambdaReturnType_eq_of_present (symbol_ok_tokenAt .arrow .typeExpr arrowResult).1]
    cases typeExpr { input with cursor := input.cursor + 1 } <;> simp [present]
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .arrow (Bool.eq_false_iff.mpr present)
    rw [optionalLambdaReturnType_eq_none_of_absent absent]
    simp [present]

theorem optionalLambdaReturnType_reject_trace_sound
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects) :
    ParserTraceRejectSound optionalLambdaReturnType
      (DeclarativeGrammar.OptionalLambdaReturnTypeTraceRejects typeRejects) := by
  intro input rejected failure result
  rcases optionalLambdaReturnType_reject_iff_type.mp result with ⟨present, typeResult⟩
  rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with ⟨arrow, arrowResult⟩
  rcases rejectSound typeResult with ⟨trace, rejection, events⟩
  exact ⟨trace, .typeRejected arrow.span
    (symbol_success_exactTokenParses .arrow .typeExpr arrowResult) rejection, events⟩

theorem optionalLambdaReturnType_trace_reject_complete
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects) :
    ParserTraceRejectComplete optionalLambdaReturnType
      (DeclarativeGrammar.OptionalLambdaReturnTypeTraceRejects typeRejects) := by
  intro input after diagnostic trace rejection
  cases rejection with
  | typeRejected span arrow type =>
      have selected := DelimitedTraceInternals.symbol_present .arrow arrow
      rcases arrow with ⟨token, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) type with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, optionalLambdaReturnType_reject_iff_type.mpr ⟨selected, result⟩,
        afterEq, reportEq, events⟩

theorem optionalLambdaReturnType_trace_reject_iff
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects)
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalLambdaReturnTypeTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, optionalLambdaReturnType input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalLambdaReturnType_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases optionalLambdaReturnType_reject_trace_sound rejectSound result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem optionalLambdaReturnType_trace_reject_failure_iff
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects)
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalLambdaReturnTypeTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, optionalLambdaReturnType input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [optionalLambdaReturnType_trace_reject_iff rejectSound rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
