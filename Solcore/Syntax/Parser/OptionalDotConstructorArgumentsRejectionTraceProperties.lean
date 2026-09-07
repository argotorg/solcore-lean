import Solcore.Syntax.DeclarativeDotConstructorRejectionTraceGrammar
import Solcore.Syntax.Parser.DelimitedNoTrailingRejectionTraceCorrespondenceProperties
import Solcore.Syntax.Parser.ExpressionNameRejectionTraceProperties
import Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts

/-! Exact optional-argument rejection under explicit child expression laws.
The left-parenthesis guard commits to the raw list result without changing its
failure, rejected state, or events; absent arguments cannot reject. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem optionalDotConstructorArguments_reject_iff_list
    {input rejected : State} {failure : Failure} :
    optionalDotConstructorArguments nested input = .reject failure rejected ↔
    isSymbol input .leftParen = true ∧
      delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input =
        .reject failure rejected := by
  cases guard : isSymbol input .leftParen with
  | false => simp [optionalDotConstructorArguments, getState, bind, guard, pure]
  | true =>
      cases result : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input <;>
        simp [optionalDotConstructorArguments, getState, bind, guard, pure, result]

theorem optionalDotConstructorArguments_reject_trace_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ParserTraceRejectSound (optionalDotConstructorArguments nested)
      (DeclarativeGrammar.OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  rcases optionalDotConstructorArguments_reject_iff_list.mp result with ⟨selected, raw⟩
  rcases delimitedNoTrailing_reject_trace_sound successSound rejectSound contextFrame
      .leftParen .rightParen true .expression .expression raw with ⟨trace, rejection, events⟩
  rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression selected with ⟨opening, openingResult⟩
  exact ⟨trace, .present opening.span (symbol_success_exactTokenParses .leftParen .expression openingResult).1
    rejection, events⟩

theorem optionalDotConstructorArguments_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ParserTraceRejectComplete (optionalDotConstructorArguments nested)
      (DeclarativeGrammar.OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects) := by
  intro input after diagnostic trace rejection
  cases rejection with
  | present span opening arguments =>
      have selected := DelimitedTraceInternals.symbol_present .leftParen (input := input)
        (after := { input.declarativeRemainder with cursor := input.cursor + 1 }) ⟨opening, rfl⟩
      rcases delimitedNoTrailing_trace_reject_complete successComplete rejectComplete contextFrame
          .leftParen .rightParen true .expression .expression arguments with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, optionalDotConstructorArguments_reject_iff_list.mpr ⟨selected, result⟩,
        afterEq, reportEq, events⟩

theorem optionalDotConstructorArguments_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, optionalDotConstructorArguments nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalDotConstructorArguments_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases optionalDotConstructorArguments_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem optionalDotConstructorArguments_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, optionalDotConstructorArguments nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [optionalDotConstructorArguments_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
