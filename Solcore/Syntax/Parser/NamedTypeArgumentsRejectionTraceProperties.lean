import Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceGrammar
import Solcore.Syntax.Parser.DelimitedTrailingRejectionTraceCorrespondenceProperties
import Solcore.Syntax.Parser.TypeNamedTotalityProperties

/-! Exact selected-angle rejection delegates to the concrete trailing-enabled
nonempty list. Neither the optional guard nor requireNonempty changes failure
state or diagnostics; successful raw lists cannot reach its defensive invariant. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseNamedTypeArguments_reject_iff_list
    {input rejected : State} {failure : Failure} :
    parseNamedTypeArguments nested input = .reject failure rejected ↔
    isSymbol input .less = true ∧
      delimited .less .greater false nested .typeExpr .typeExpr input = .reject failure rejected := by
  cases guard : isSymbol input .less with
  | false => simp [parseNamedTypeArguments, getState, bind, guard, pure]
  | true =>
      cases result : delimited .less .greater false nested .typeExpr .typeExpr input with
      | reject childFailure childRejected =>
          simp [parseNamedTypeArguments, getState, bind, guard, result]
      | invariant error =>
          simp [parseNamedTypeArguments, getState, bind, guard, result]
      | ok values afterValues =>
          rcases requireNonempty_ok_of_delimited_false_ok .less .greater nested
              .typeExpr .typeExpr result with ⟨nonempty, converted⟩
          simp [parseNamedTypeArguments, getState, bind, guard, result, converted, pure]

theorem parseNamedTypeArguments_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseNamedTypeArguments nested)
      (DeclarativeGrammar.NamedTypeArgumentsTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  rcases parseNamedTypeArguments_reject_iff_list.mp result with ⟨selected, raw⟩
  rcases delimited_reject_trace_sound successSound rejectSound contextFrame
      .less .greater false .typeExpr .typeExpr raw with ⟨trace, rejection, events⟩
  rcases symbol_eq_ok_of_isSymbol_eq_true .less .typeExpr selected with ⟨opening, openingResult⟩
  exact ⟨trace, .present opening.span (symbol_success_exactTokenParses .less .typeExpr openingResult).1
    rejection, events⟩

theorem parseNamedTypeArguments_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseNamedTypeArguments nested)
      (DeclarativeGrammar.NamedTypeArgumentsTraceRejects elementTrace elementRejects) := by
  intro input after diagnostic trace rejection
  cases rejection with
  | present span opening arguments =>
      have selected := DelimitedTraceInternals.symbol_present .less (input := input)
        (after := { input.declarativeRemainder with cursor := input.cursor + 1 }) ⟨opening, rfl⟩
      rcases delimited_trace_reject_complete successComplete rejectComplete contextFrame
          .less .greater false .typeExpr .typeExpr arguments with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, parseNamedTypeArguments_reject_iff_list.mpr ⟨selected, result⟩,
        afterEq, reportEq, events⟩

theorem parseNamedTypeArguments_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeArgumentsTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, parseNamedTypeArguments nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseNamedTypeArguments_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parseNamedTypeArguments_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parseNamedTypeArguments_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeArgumentsTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseNamedTypeArguments nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parseNamedTypeArguments_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
