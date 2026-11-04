import Solcore.Syntax.Internal.TypeTrace
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.TypeBasics
import Solcore.Syntax.Parser.Internal.FunctionReturnsTrace
import Solcore.Syntax.Internal.NameTrace
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties
import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Parser.Internal.DelimitedTrace
import Solcore.Syntax.Parser.Internal.TypeFormTotality
import Solcore.Syntax.Parser.PragmaItemsContextProperties
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.TypeTotality

/-!
Parser side of the identifier and type traces: soundness, completeness,
correspondence and existence for each type form, and for recursive
`typeExpr` at unrestricted fuel.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.ComptimeTypeRejectionTraceProperties
/-! Raw comptime rejection reflects exactly its first failing stage, retaining
the child's events without committing its terminal report. Only closing
rejection needs a child success frame for the report's source and EOF span. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem parseComptimeType_reject_trace_sound
    {nested : Parser TypeExpr}
    {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseComptimeType nested)
      (DeclarativeGrammar.ComptimeTypeTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  unfold parseComptimeType at result
  simp only [bind] at result
  cases markerResult : contextual .comptime .typeExpr input with
  | invariant error => simp [markerResult] at result
  | reject markerFailure markerRejected =>
      have shape := acceptToken_reject_state_shape (.contextual .comptime) .typeExpr
        (·.isContextual .comptime) markerResult
      subst markerRejected
      simp only [markerResult] at result
      cases result
      have reported := (contextual_reject_reports_iff .comptime .typeExpr).mpr ⟨failure, markerResult, rfl⟩
      exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  | ok marker afterMarker =>
      have markerParsed := contextual_success_exactTokenParses .comptime .typeExpr markerResult
      have shape := (contextual_ok_tokenAt .comptime .typeExpr markerResult).2
      subst afterMarker
      simp only [markerResult] at result
      cases openingResult : symbol .less .typeExpr { input with cursor := input.cursor + 1 } with
      | invariant error => simp [openingResult] at result
      | reject openingFailure openingRejected =>
          have shape := symbol_reject_state_eq .less .typeExpr openingResult
          subst openingRejected
          simp only [openingResult] at result
          cases result
          have reported := (symbol_reject_reports_iff .less .typeExpr).mpr ⟨failure, openingResult, rfl⟩
          exact ⟨[], .openingMissing marker.span markerParsed reported.1 reported.2,
            by simp only [List.append_nil]; rfl⟩
      | ok opening afterOpening =>
          have openingParsed := symbol_success_exactTokenParses .less .typeExpr openingResult
          have shape := (symbol_ok_tokenAt .less .typeExpr openingResult).2
          subst afterOpening
          simp only [openingResult] at result
          cases innerResult : nested { input with cursor := input.cursor + 1 + 1 } with
          | invariant error => simp [innerResult] at result
          | reject innerFailure innerRejected =>
              simp only [innerResult] at result
              cases result
              rcases rejectSound innerResult with ⟨trace, inner, events⟩
              exact ⟨trace, .innerRejected marker.span opening.span markerParsed openingParsed inner, events⟩
          | ok inner afterInner =>
              simp only [innerResult] at result
              rcases successSound innerResult with ⟨innerEvents, innerParsed, innerEq⟩
              have innerFrame := contextFrame innerResult
              cases closingResult : symbol .greater .typeExpr afterInner with
              | invariant error => simp [closingResult] at result
              | reject closingFailure closingRejected =>
                  have shape := symbol_reject_state_eq .greater .typeExpr closingResult
                  subst closingRejected
                  simp only [closingResult] at result
                  cases result
                  have reported := (symbol_reject_reports_iff .greater .typeExpr).mpr ⟨failure, closingResult, rfl⟩
                  refine ⟨innerEvents, .closingMissing marker.span opening.span markerParsed openingParsed
                    innerParsed reported.1 ?_, innerEq⟩
                  simpa only [innerFrame.1, innerFrame.2] using reported.2
              | ok closing final => simp [closingResult, pure] at result

theorem parseComptimeType_trace_reject_complete
    {nested : Parser TypeExpr}
    {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseComptimeType nested)
      (DeclarativeGrammar.ComptimeTypeTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (contextual_reject_reports_iff .comptime .typeExpr).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [parseComptimeType, bind, result], rfl, reportEq, by simp⟩
  | openingMissing markerSpan marker absent reported =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases (symbol_reject_reports_iff .less .typeExpr
          (input := { input with cursor := input.cursor + 1 })).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, { input with cursor := input.cursor + 1 },
        by simp only [parseComptimeType, bind, markerResult, result], rfl, reportEq,
        by simp only [List.append_nil]; rfl⟩
  | innerRejected markerSpan openingSpan marker opening inner =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 + 1 }) inner with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, by simp only [parseComptimeType, bind, markerResult, openingResult, result],
        afterEq, reportEq, events⟩
  | closingMissing markerSpan openingSpan marker opening inner absent reported =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 + 1 }) inner with
        ⟨afterInner, innerResult, afterEq, events⟩
      have frame := contextFrame innerResult
      have absentAtInner : DeclarativeGrammar.TokenKindAbsentAt afterInner.tokens afterInner.window.endIndex
          afterInner.cursor (.symbol .greater) := by simpa only [← afterEq, State.declarativeRemainder] using absent
      have reportAtInner : DeclarativeGrammar.RejectAtReports afterInner.file.id afterInner.window.endByte
          { head := .symbol .greater, tail := [] } .typeExpr afterInner.declarativeRemainder report := by
        simpa only [frame.1, frame.2, afterEq] using reported
      rcases (symbol_reject_reports_iff .greater .typeExpr).mp ⟨absentAtInner, reportAtInner⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, afterInner,
        by simp only [parseComptimeType, bind, markerResult, openingResult, innerResult, result],
        afterEq, reportEq, events⟩

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseComptimeType_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ComptimeTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parseComptimeType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseComptimeType_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parseComptimeType_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parseComptimeType_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ComptimeTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseComptimeType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parseComptimeType_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ComptimeTypeSuccessTraceProperties
/-! Actual raw comptime-type success retains the exact nested event suffix.
Neither success direction needs child context, validity, or carrier laws;
source/full-window preservation is proved separately from a child frame. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem comptime_bind_ok_parts {α β : Type} {first : Parser α} {next : α → Parser β}
    {input output : State} {value : β} (result : (first >>= next) input = .ok value output) :
    ∃ item after, first input = .ok item after ∧ next item after = .ok value output := by
  cases firstResult : first input <;> simp only [bind, firstResult] at result
  case ok item after => exact ⟨item, after, rfl, result⟩
  case reject => contradiction
  case invariant => contradiction

theorem parseComptimeType_success_iff_components {input output : State} {resultValue : TypeExpr} :
    parseComptimeType nested input = .ok resultValue output ↔
    ∃ marker afterMarker opening afterOpening inner afterInner closing,
      contextual .comptime .typeExpr input = .ok marker afterMarker ∧
      symbol .less .typeExpr afterMarker = .ok opening afterOpening ∧
      nested afterOpening = .ok inner afterInner ∧
      symbol .greater .typeExpr afterInner = .ok closing output ∧
      resultValue = DeclarativeGrammar.comptimeTypeTraceValue marker.span opening.span closing.span inner := by
  constructor
  · intro result
    unfold parseComptimeType at result
    rcases comptime_bind_ok_parts result with ⟨marker, afterMarker, markerResult, rest⟩
    rcases comptime_bind_ok_parts rest with ⟨opening, afterOpening, openingResult, rest⟩
    rcases comptime_bind_ok_parts rest with ⟨inner, afterInner, innerResult, rest⟩
    rcases comptime_bind_ok_parts rest with ⟨closing, afterClosing, closingResult, finished⟩
    cases finished
    exact ⟨marker, afterMarker, opening, afterOpening, inner, afterInner, closing,
      markerResult, openingResult, innerResult, closingResult, rfl⟩
  · rintro ⟨marker, afterMarker, opening, afterOpening, inner, afterInner, closing,
      markerResult, openingResult, innerResult, closingResult, rfl⟩
    simp only [parseComptimeType, bind, markerResult, openingResult, innerResult,
      closingResult, pure, DeclarativeGrammar.comptimeTypeTraceValue]

theorem parseComptimeType_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace) :
    ParserTraceSuccessSound (parseComptimeType nested) (DeclarativeGrammar.ComptimeTypeTraceParses elementTrace) := by
  intro input output resultValue result
  rcases parseComptimeType_success_iff_components.mp result with
    ⟨marker, afterMarker, opening, afterOpening, inner, afterInner, closing,
      markerResult, openingResult, innerResult, closingResult, rfl⟩
  have markerParsed := contextual_success_exactTokenParses .comptime .typeExpr markerResult
  have openingParsed := symbol_success_exactTokenParses .less .typeExpr openingResult
  have closingParsed := symbol_success_exactTokenParses .greater .typeExpr closingResult
  have markerState := (contextual_ok_tokenAt .comptime .typeExpr markerResult).2
  have openingState := (symbol_ok_tokenAt .less .typeExpr openingResult).2
  have closingState := (symbol_ok_tokenAt .greater .typeExpr closingResult).2
  subst afterMarker afterOpening output
  rcases successSound innerResult with ⟨trace, typed, events⟩
  exact ⟨trace, .parsed marker.span opening.span closing.span markerParsed openingParsed typed closingParsed, events⟩

theorem parseComptimeType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace) :
    ParserTraceSuccessComplete (parseComptimeType nested) (DeclarativeGrammar.ComptimeTypeTraceParses elementTrace) := by
  intro input resultValue after trace parsed
  cases parsed with
  | parsed markerSpan openingSpan closingSpan marker opening typed closing =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 + 1 }) typed with
        ⟨afterInner, innerResult, afterEq, events⟩
      have closingAtInner : DeclarativeGrammar.ExactTokenParses (.symbol .greater)
          afterInner.declarativeRemainder closingSpan after := by simpa only [afterEq] using closing
      have closingResult := symbol_eq_ok_of_exactTokenParses .greater .typeExpr closingAtInner
      exact ⟨{ afterInner with cursor := afterInner.cursor + 1 },
        parseComptimeType_success_iff_components.mpr
          ⟨_, _, _, _, _, _, _, markerResult, openingResult, innerResult, closingResult, rfl⟩,
        closingAtInner.2.symm, events⟩

theorem parseComptimeType_success_context
    (contextFrame : ParserSuccessContext nested) : ParserSuccessContext (parseComptimeType nested) := by
  intro input output resultValue result
  rcases parseComptimeType_success_iff_components.mp result with
    ⟨marker, afterMarker, opening, afterOpening, inner, afterInner, closing,
      markerResult, openingResult, innerResult, closingResult, _⟩
  have markerState := (contextual_ok_tokenAt .comptime .typeExpr markerResult).2
  have openingState := (symbol_ok_tokenAt .less .typeExpr openingResult).2
  have closingState := (symbol_ok_tokenAt .greater .typeExpr closingResult).2
  subst afterMarker afterOpening output
  have frame := contextFrame innerResult
  exact frame

theorem parseComptimeType_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    {input : State} {value : TypeExpr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ComptimeTypeTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parseComptimeType nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseComptimeType_trace_success_complete successComplete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parseComptimeType_trace_success_sound successSound result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionTypeSuccessTraceProperties
/-! Raw function success composes the actual keyword, parameters, and optional
returns. Child source/full-window preservation keeps trace coordinates aligned;
no child token-carrier or validity law is part of this exact runtime contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open TypeFunctionInternals

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem function_bind_ok_parts {α β : Type} {first : Parser α} {next : α → Parser β}
    {input output : State} {value : β} (result : (first >>= next) input = .ok value output) :
    ∃ item after, first input = .ok item after ∧ next item after = .ok value output := by
  cases firstResult : first input <;> simp only [bind, firstResult] at result
  case ok item after => exact ⟨item, after, rfl, result⟩
  case reject => contradiction
  case invariant => contradiction

theorem parseFunctionType_success_iff_components {input output : State} {value : TypeExpr} :
    parseFunctionType nested input = .ok value output ↔
    ∃ marker afterMarker parameters afterParameters returns,
      keyword .functionKw .typeExpr input = .ok marker afterMarker ∧
      delimited .leftParen .rightParen true nested .typeExpr .typeExpr afterMarker = .ok parameters afterParameters ∧
      parseFunctionReturns nested afterParameters = .ok returns output ∧
      value = DeclarativeGrammar.functionTypeTraceValue marker.span parameters returns := by
  constructor
  · intro result
    unfold parseFunctionType at result
    rcases function_bind_ok_parts result with ⟨marker, afterMarker, markerResult, rest⟩
    rcases function_bind_ok_parts rest with ⟨parameters, afterParameters, parametersResult, rest⟩
    rcases function_bind_ok_parts rest with ⟨returns, afterReturns, returnsResult, finished⟩
    cases finished
    exact ⟨marker, afterMarker, parameters, afterParameters, returns,
      markerResult, parametersResult, returnsResult, rfl⟩
  · rintro ⟨marker, afterMarker, parameters, afterParameters, returns,
      markerResult, parametersResult, returnsResult, rfl⟩
    simp only [parseFunctionType, bind, markerResult, parametersResult, returnsResult,
      pure, DeclarativeGrammar.functionTypeTraceValue]
    rfl

theorem parseFunctionType_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessSound (parseFunctionType nested) (DeclarativeGrammar.FunctionTypeTraceParses elementTrace) := by
  intro input output value result
  rcases parseFunctionType_success_iff_components.mp result with
    ⟨marker, afterMarker, parameters, afterParameters, returns,
      markerResult, parametersResult, returnsResult, rfl⟩
  have markerParsed := keyword_success_exactTokenParses .functionKw .typeExpr markerResult
  have markerState := (keyword_ok_tokenAt .functionKw .typeExpr markerResult).2
  subst afterMarker
  rcases delimited_trace_success_sound successSound contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr parametersResult with
    ⟨parameterEvents, parametersParsed, parameterEq⟩
  have frame := delimited_success_context contextFrame
    .leftParen .rightParen true .typeExpr .typeExpr parametersResult
  rcases parseFunctionReturns_trace_success_sound successSound contextFrame returnsResult with
    ⟨returnEvents, returnsParsed, returnEq⟩
  refine ⟨parameterEvents ++ returnEvents, .parsed marker.span markerParsed parametersParsed ?_, ?_⟩
  · simpa only [frame.1, frame.2] using returnsParsed
  · rw [returnEq, parameterEq]; exact List.append_assoc _ _ _

theorem parseFunctionType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessComplete (parseFunctionType nested) (DeclarativeGrammar.FunctionTypeTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed span marker parameters returns =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .functionKw .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases delimited_trace_success_complete successComplete contextFrame
          .leftParen .rightParen true .typeExpr .typeExpr
          (input := { input with cursor := input.cursor + 1 }) parameters with
        ⟨afterParameters, parametersResult, afterEq, parameterEvents⟩
      have frame := delimited_success_context contextFrame
        .leftParen .rightParen true .typeExpr .typeExpr parametersResult
      have returnsAtNext := returns
      rw [← afterEq, ← frame.1, ← frame.2] at returnsAtNext
      rcases parseFunctionReturns_trace_success_complete successComplete contextFrame returnsAtNext with
        ⟨output, returnsResult, finalEq, returnEvents⟩
      refine ⟨output, parseFunctionType_success_iff_components.mpr
        ⟨_, _, _, _, _, markerResult, parametersResult, returnsResult, rfl⟩, finalEq, ?_⟩
      rw [returnEvents, parameterEvents]; exact List.append_assoc _ _ _

theorem parseFunctionType_success_context
    (contextFrame : ParserSuccessContext nested) : ParserSuccessContext (parseFunctionType nested) := by
  intro input output value result
  rcases parseFunctionType_success_iff_components.mp result with
    ⟨marker, afterMarker, parameters, afterParameters, returns,
      markerResult, parametersResult, returnsResult, _⟩
  have markerState := (keyword_ok_tokenAt .functionKw .typeExpr markerResult).2
  subst afterMarker
  have first := delimited_success_context contextFrame
    .leftParen .rightParen true .typeExpr .typeExpr parametersResult
  have last := parseFunctionReturns_success_context contextFrame returnsResult
  exact ⟨last.1.trans first.1, last.2.trans first.2⟩

theorem parseFunctionType_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {value : TypeExpr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.FunctionTypeTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parseFunctionType nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseFunctionType_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parseFunctionType_trace_success_sound successSound contextFrame result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionTypeRejectionTraceProperties
/-! Exact raw function failures preserve the whole returned Failure and State.
Parameters run before returns; the final pure AST construction cannot reject.
Terminal reports remain separate from ordered child diagnostic events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open TypeFunctionInternals

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseFunctionType_reject_iff_components {input rejected : State} {failure : Failure} :
    parseFunctionType nested input = .reject failure rejected ↔
    keyword .functionKw .typeExpr input = .reject failure rejected ∨
    (∃ marker afterMarker, keyword .functionKw .typeExpr input = .ok marker afterMarker ∧
      delimited .leftParen .rightParen true nested .typeExpr .typeExpr afterMarker = .reject failure rejected) ∨
    (∃ marker afterMarker parameters afterParameters,
      keyword .functionKw .typeExpr input = .ok marker afterMarker ∧
      delimited .leftParen .rightParen true nested .typeExpr .typeExpr afterMarker = .ok parameters afterParameters ∧
      parseFunctionReturns nested afterParameters = .reject failure rejected) := by
  constructor
  · intro result
    unfold parseFunctionType at result
    cases markerResult : keyword .functionKw .typeExpr input with
    | invariant => simp only [bind, markerResult] at result; contradiction
    | reject markerFailure markerRejected =>
        simp only [bind, markerResult] at result
        cases result
        exact .inl rfl
    | ok marker afterMarker =>
        simp only [bind, markerResult] at result
        cases parametersResult : delimited .leftParen .rightParen true nested .typeExpr .typeExpr afterMarker with
        | invariant => simp only [parametersResult] at result; contradiction
        | reject parameterFailure parameterRejected =>
            simp only [parametersResult] at result
            cases result
            exact .inr (.inl ⟨_, _, rfl, parametersResult⟩)
        | ok parameters afterParameters =>
            simp only [parametersResult] at result
            cases returnsResult : parseFunctionReturns nested afterParameters with
            | invariant => simp only [returnsResult] at result; contradiction
            | ok => simp only [returnsResult, pure] at result; contradiction
            | reject returnFailure returnRejected =>
                simp only [returnsResult] at result
                cases result
                exact .inr (.inr ⟨_, _, _, _, rfl, parametersResult, returnsResult⟩)
  · rintro (markerResult | ⟨marker, afterMarker, markerResult, parametersResult⟩ |
      ⟨marker, afterMarker, parameters, afterParameters, markerResult, parametersResult, returnsResult⟩)
    · simp only [parseFunctionType, bind, markerResult]
    · simp only [parseFunctionType, bind, markerResult, parametersResult]
    · simp only [parseFunctionType, bind, markerResult, parametersResult, returnsResult]

theorem parseFunctionType_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseFunctionType nested)
      (DeclarativeGrammar.FunctionTypeTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  rcases parseFunctionType_reject_iff_components.mp result with markerResult |
      ⟨marker, afterMarker, markerResult, parametersResult⟩ |
      ⟨marker, afterMarker, parameters, afterParameters, markerResult, parametersResult, returnsResult⟩
  · have same := acceptToken_reject_state_shape (.keyword .functionKw) .typeExpr
      (· == .keyword .functionKw) markerResult
    subst rejected
    have reported := (keyword_reject_reports_iff .functionKw .typeExpr).mpr ⟨failure, markerResult, rfl⟩
    exact ⟨[], .markerMissing reported.1 reported.2, by simp only [List.append_nil]⟩
  · have markerParsed := keyword_success_exactTokenParses .functionKw .typeExpr markerResult
    have markerState := (keyword_ok_tokenAt .functionKw .typeExpr markerResult).2
    subst afterMarker
    rcases delimited_reject_trace_sound successSound rejectSound contextFrame
        .leftParen .rightParen true .typeExpr .typeExpr parametersResult with ⟨trace, rejected, events⟩
    exact ⟨trace, .parametersRejected marker.span markerParsed rejected, events⟩
  · have markerParsed := keyword_success_exactTokenParses .functionKw .typeExpr markerResult
    have markerState := (keyword_ok_tokenAt .functionKw .typeExpr markerResult).2
    subst afterMarker
    rcases delimited_trace_success_sound successSound contextFrame
        .leftParen .rightParen true .typeExpr .typeExpr parametersResult with
      ⟨parameterEvents, parametersParsed, parameterEq⟩
    have frame := delimited_success_context contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr parametersResult
    rcases parseFunctionReturns_reject_trace_sound successSound rejectSound contextFrame returnsResult with
      ⟨returnEvents, returnsRejected, returnEq⟩
    refine ⟨parameterEvents ++ returnEvents,
      .returnsRejected marker.span markerParsed parametersParsed ?_, ?_⟩
    · simpa only [frame.1, frame.2] using returnsRejected
    · rw [returnEq, parameterEq]; exact List.append_assoc _ _ _

theorem parseFunctionType_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseFunctionType nested)
      (DeclarativeGrammar.FunctionTypeTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (keyword_reject_reports_iff .functionKw .typeExpr).mp ⟨absent, reported⟩ with
        ⟨failure, markerResult, reportEq⟩
      exact ⟨failure, input, parseFunctionType_reject_iff_components.mpr (.inl markerResult),
        rfl, reportEq, by simp only [List.append_nil]⟩
  | parametersRejected span marker parameters =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .functionKw .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases delimited_trace_reject_complete successComplete rejectComplete contextFrame
          .leftParen .rightParen true .typeExpr .typeExpr
          (input := { input with cursor := input.cursor + 1 }) parameters with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, parseFunctionType_reject_iff_components.mpr
        (.inr (.inl ⟨_, _, markerResult, result⟩)), afterEq, reportEq, events⟩
  | returnsRejected span marker parameters returns =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .functionKw .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases delimited_trace_success_complete successComplete contextFrame
          .leftParen .rightParen true .typeExpr .typeExpr
          (input := { input with cursor := input.cursor + 1 }) parameters with
        ⟨afterParameters, parametersResult, afterEq, parameterEvents⟩
      have frame := delimited_success_context contextFrame
        .leftParen .rightParen true .typeExpr .typeExpr parametersResult
      have returnsAtNext := returns
      rw [← afterEq, ← frame.1, ← frame.2] at returnsAtNext
      rcases parseFunctionReturns_trace_reject_complete successComplete rejectComplete contextFrame returnsAtNext with
        ⟨failure, rejected, returnsResult, finalEq, reportEq, returnEvents⟩
      refine ⟨failure, rejected, parseFunctionType_reject_iff_components.mpr
        (.inr (.inr ⟨_, _, _, _, markerResult, parametersResult, returnsResult⟩)), finalEq, reportEq, ?_⟩
      rw [returnEvents, parameterEvents]; exact List.append_assoc _ _ _

theorem parseFunctionType_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.FunctionTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parseFunctionType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseFunctionType_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parseFunctionType_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parseFunctionType_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.FunctionTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseFunctionType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parseFunctionType_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.IdentifierTraceProperties
/-! Exact raw and checked identifier success, including complete diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem rawIdentifier_success_ordinary_iff (context : ParseContext)
    {input : State} {name : Identifier} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.IdentifierParses input.declarativeRemainder name remainder ↔
      ∃ output, rawIdentifier context input = .ok name output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (rawIdentifier context)
    DeclarativeGrammar.identifierExactOutcomeSpec
    (rawIdentifier_ne_invariant context input)
    (rawIdentifier_success_ordinaryOutcome_sound context)
    (rawIdentifier_reject_ordinaryOutcome_sound context)

private theorem identifier_success_ordinary_iff (context : ParseContext)
    {input : State} {name : Identifier} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.IdentifierParses input.declarativeRemainder name remainder ↔
      ∃ output, identifier context input = .ok name output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (identifier context)
    DeclarativeGrammar.identifierExactOutcomeSpec
    (identifier_ne_invariant context input)
    (identifier_success_sound context) (identifier_reject_sound context)

/-- Raw names consume their token without changing any earlier diagnostics. -/
theorem rawIdentifier_success_diagnostics_eq (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name output) :
    output.diagnostics = input.diagnostics := by
  rw [(rawIdentifier_ok_tokenAt context result).2]
  rfl

/-- Raw success has its exact AST, endpoint, and independent empty trace. -/
theorem rawIdentifier_success_trace_sound (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name output) :
    DeclarativeGrammar.RawIdentifierTraceParses input.declarativeRemainder name
        output.declarativeRemainder [] ∧
      output.diagnostics = input.diagnostics :=
  ⟨.parsed (rawIdentifier_success_ordinaryOutcome_sound context result),
    rawIdentifier_success_diagnostics_eq context result⟩

/-- Checked success selects exactly its spelling-dependent added events. -/
theorem identifier_success_diagnosticTrace (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output) :
    ∃ trace, DeclarativeGrammar.IdentifierDiagnosticTrace name trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  unfold identifier at result
  cases raw : rawIdentifier context input with
  | reject failure rejected => simp [raw] at result
  | invariant error => simp [raw] at result
  | ok parsed afterName =>
      have previous := rawIdentifier_success_diagnostics_eq context raw
      simp only [raw] at result
      by_cases hyphen : DeclarativeGrammar.IdentifierHyphenSpelling parsed.value
      · have contains :=
          (DeclarativeGrammar.identifierHyphenSpelling_iff_contains parsed.value).mp hyphen
        simp only [contains, if_true] at result
        cases result
        refine ⟨_, .hyphen hyphen, ?_⟩
        simpa only [State.diagnostics, State.emit, List.reverse_cons] using
          congrArg (fun diagnostics => diagnostics ++
            [{ span := name.span, kind := .invalidIdentifierHyphen name.value }]) previous
      · have absent : parsed.value.toList.contains '-' = false := by
          apply Bool.eq_false_iff.mpr
          intro contains
          exact hyphen
            ((DeclarativeGrammar.identifierHyphenSpelling_iff_contains parsed.value).mpr
              contains)
        simp only [absent, Bool.false_eq_true, if_false] at result
        cases result
        exact ⟨[], .clean hyphen, by simpa only [List.append_nil] using previous⟩

/-- The independently chosen spelling trace fixes the entire added suffix. -/
theorem identifier_success_diagnostics_eq_of_trace (context : ParseContext)
    {input output : State} {name : Identifier} {trace : List ParseDiagnostic}
    (result : identifier context input = .ok name output)
    (diagnostics : DeclarativeGrammar.IdentifierDiagnosticTrace name trace) :
    output.diagnostics = input.diagnostics ++ trace := by
  rcases identifier_success_diagnosticTrace context result with
    ⟨actual, actualTrace, actualEq⟩
  simpa only [actualTrace.trace_unique diagnostics] using actualEq

/-- Executable checked success derives the full independent traced grammar. -/
theorem identifier_success_trace_sound (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output) :
    ∃ trace, DeclarativeGrammar.IdentifierTraceParses input.declarativeRemainder name
        output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases identifier_success_diagnosticTrace context result with
    ⟨trace, diagnostics, diagnosticEq⟩
  exact ⟨trace, .parsed (identifier_success_sound context result) diagnostics,
    diagnosticEq⟩

/-- Raw token and trace derivation is equivalent to exact executable success. -/
theorem rawIdentifier_trace_success_iff (context : ParseContext)
    {input : State} {name : Identifier} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.RawIdentifierTraceParses input.declarativeRemainder name
        remainder trace ↔
      ∃ output, rawIdentifier context input = .ok name output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  rw [DeclarativeGrammar.rawIdentifierTraceParses_iff]
  constructor
  · rintro ⟨ordinary, rfl⟩
    rcases (rawIdentifier_success_ordinary_iff context).mp ordinary with
      ⟨output, result, after⟩
    exact ⟨output, result, after,
      by simpa only [List.append_nil] using rawIdentifier_success_diagnostics_eq context result⟩
  · rintro ⟨output, result, after, diagnosticEq⟩
    refine ⟨(rawIdentifier_success_ordinary_iff context).mpr ⟨output, result, after⟩, ?_⟩
    have unchanged := rawIdentifier_success_diagnostics_eq context result
    have empty : input.diagnostics ++ trace = input.diagnostics ++ [] := by
      simpa only [List.append_nil] using diagnosticEq.symm.trans unchanged
    exact List.append_cancel_left empty

/-- Checked token, spelling, and trace derivation is equivalent to execution
with the same full AST and remainder, preserving all earlier diagnostics. -/
theorem identifier_trace_success_iff (context : ParseContext)
    {input : State} {name : Identifier} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IdentifierTraceParses input.declarativeRemainder name
        remainder trace ↔
      ∃ output, identifier context input = .ok name output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  rw [DeclarativeGrammar.identifierTraceParses_iff]
  constructor
  · rintro ⟨ordinary, diagnostics⟩
    rcases (identifier_success_ordinary_iff context).mp ordinary with
      ⟨output, result, after⟩
    exact ⟨output, result, after,
      identifier_success_diagnostics_eq_of_trace context result diagnostics⟩
  · rintro ⟨output, result, after, diagnosticEq⟩
    refine ⟨(identifier_success_ordinary_iff context).mpr ⟨output, result, after⟩, ?_⟩
    rcases identifier_success_diagnosticTrace context result with
      ⟨actual, diagnostics, actualEq⟩
    have traceEq : actual = trace := List.append_cancel_left
      (actualEq.symm.trans diagnosticEq)
    simpa only [traceEq] using diagnostics

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.MappingTypeRejectionTraceSoundnessProperties
/-! Raw mapping rejection reflects exactly its first failing stage, retaining
earlier key/value diagnostics and never committing the unexpected report. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem parseMappingType_reject_trace_sound
    {nested : Parser TypeExpr}
    {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseMappingType nested)
      (DeclarativeGrammar.MappingTypeTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  unfold parseMappingType at result
  simp only [bind] at result
  cases markerResult : contextual .mapping .typeExpr input with
  | invariant error => simp [markerResult] at result
  | reject markerFailure markerRejected =>
      have shape := acceptToken_reject_state_shape (.contextual .mapping) .typeExpr
        (·.isContextual .mapping) markerResult
      subst markerRejected
      simp only [markerResult] at result
      cases result
      have reported := (contextual_reject_reports_iff .mapping .typeExpr).mpr ⟨failure, markerResult, rfl⟩
      exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  | ok marker afterMarker =>
      have markerParsed := contextual_success_exactTokenParses .mapping .typeExpr markerResult
      have shape := (contextual_ok_tokenAt .mapping .typeExpr markerResult).2
      subst afterMarker
      simp only [markerResult] at result
      cases openingResult : symbol .leftParen .typeExpr { input with cursor := input.cursor + 1 } with
      | invariant error => simp [openingResult] at result
      | reject openingFailure openingRejected =>
          have shape := symbol_reject_state_eq .leftParen .typeExpr openingResult
          subst openingRejected
          simp only [openingResult] at result
          cases result
          have reported := (symbol_reject_reports_iff .leftParen .typeExpr).mpr ⟨failure, openingResult, rfl⟩
          exact ⟨[], .openingMissing marker.span markerParsed reported.1 reported.2,
            by simp only [List.append_nil]; rfl⟩
      | ok opening afterOpening =>
          have openingParsed := symbol_success_exactTokenParses .leftParen .typeExpr openingResult
          have shape := (symbol_ok_tokenAt .leftParen .typeExpr openingResult).2
          subst afterOpening
          simp only [openingResult] at result
          cases keyResult : nested { input with cursor := input.cursor + 1 + 1 } with
          | invariant error => simp [keyResult] at result
          | reject keyFailure keyRejected =>
              simp only [keyResult] at result
              cases result
              rcases rejectSound keyResult with ⟨trace, key, events⟩
              exact ⟨trace, .keyRejected marker.span opening.span markerParsed openingParsed key, events⟩
          | ok key afterKey =>
              simp only [keyResult] at result
              rcases successSound keyResult with ⟨keyEvents, keyParsed, keyEq⟩
              have keyFrame := contextFrame keyResult
              cases arrowResult : symbol .fatArrow .typeExpr afterKey with
              | invariant error => simp [arrowResult] at result
              | reject arrowFailure arrowRejected =>
                  have shape := symbol_reject_state_eq .fatArrow .typeExpr arrowResult
                  subst arrowRejected
                  simp only [arrowResult] at result
                  cases result
                  have reported := (symbol_reject_reports_iff .fatArrow .typeExpr).mpr ⟨failure, arrowResult, rfl⟩
                  refine ⟨keyEvents, .arrowMissing marker.span opening.span markerParsed openingParsed
                    keyParsed reported.1 ?_, keyEq⟩
                  simpa only [keyFrame.1, keyFrame.2] using reported.2
              | ok arrow afterArrow =>
                  have arrowParsed := symbol_success_exactTokenParses .fatArrow .typeExpr arrowResult
                  have shape := (symbol_ok_tokenAt .fatArrow .typeExpr arrowResult).2
                  subst afterArrow
                  simp only [arrowResult] at result
                  cases valueResult : nested { afterKey with cursor := afterKey.cursor + 1 } with
                  | invariant error => simp [valueResult] at result
                  | reject valueFailure valueRejected =>
                      simp only [valueResult] at result
                      cases result
                      rcases rejectSound valueResult with ⟨valueEvents, valueRejected, valueEq⟩
                      refine ⟨keyEvents ++ valueEvents, .valueRejected marker.span opening.span arrow.span
                        markerParsed openingParsed keyParsed arrowParsed ?_, ?_⟩
                      · simpa only [keyFrame.1, keyFrame.2] using valueRejected
                      · rw [valueEq]
                        change afterKey.diagnostics ++ valueEvents = input.diagnostics ++ _
                        rw [keyEq]; exact List.append_assoc _ _ _
                  | ok value afterValue =>
                      simp only [valueResult] at result
                      rcases successSound valueResult with ⟨valueEvents, valueParsed, valueEq⟩
                      have valueFrame := contextFrame valueResult
                      cases closingResult : symbol .rightParen .typeExpr afterValue with
                      | invariant error => simp [closingResult] at result
                      | ok closing final => simp [closingResult, pure] at result
                      | reject closingFailure closingRejected =>
                          have shape := symbol_reject_state_eq .rightParen .typeExpr closingResult
                          subst closingRejected
                          simp only [closingResult] at result
                          cases result
                          have reported := (symbol_reject_reports_iff .rightParen .typeExpr).mpr
                            ⟨failure, closingResult, rfl⟩
                          refine ⟨keyEvents ++ valueEvents, .closingMissing (value := value) marker.span opening.span arrow.span
                            markerParsed openingParsed keyParsed arrowParsed ?_ reported.1 ?_, ?_⟩
                          · simpa only [keyFrame.1, keyFrame.2] using valueParsed
                          · simpa only [valueFrame.1, valueFrame.2, keyFrame.1, keyFrame.2] using reported.2
                          · rw [valueEq]
                            change afterKey.diagnostics ++ valueEvents = input.diagnostics ++ _
                            rw [keyEq]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.MappingTypeRejectionTraceCompletenessProperties
/-! Every independent raw mapping failure executes with its exact report and
prior-preserving key/value suffix. Child source/full-window preservation is
explicit, with no progress, valid-carrier, or rejected-state-frame premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem parseMappingType_trace_reject_complete
    {nested : Parser TypeExpr}
    {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseMappingType nested)
      (DeclarativeGrammar.MappingTypeTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (contextual_reject_reports_iff .mapping .typeExpr).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [parseMappingType, bind, result], rfl, reportEq, by simp⟩
  | openingMissing markerSpan marker absent reported =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases (symbol_reject_reports_iff .leftParen .typeExpr
          (input := { input with cursor := input.cursor + 1 })).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, { input with cursor := input.cursor + 1 },
        by simp only [parseMappingType, bind, markerResult, result], rfl, reportEq,
        by simp only [List.append_nil]; rfl⟩
  | keyRejected markerSpan openingSpan marker opening key =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 + 1 }) key with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, by simp only [parseMappingType, bind, markerResult, openingResult, result],
        afterEq, reportEq, events⟩
  | arrowMissing markerSpan openingSpan marker opening key absent reported =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 + 1 }) key with
        ⟨afterKey, keyResult, afterEq, events⟩
      have frame := contextFrame keyResult
      have absentAtKey : DeclarativeGrammar.TokenKindAbsentAt afterKey.tokens afterKey.window.endIndex
          afterKey.cursor (.symbol .fatArrow) := by simpa only [← afterEq, State.declarativeRemainder] using absent
      have reportAtKey : DeclarativeGrammar.RejectAtReports afterKey.file.id afterKey.window.endByte
          { head := .symbol .fatArrow, tail := [] } .typeExpr afterKey.declarativeRemainder report := by
        simpa only [frame.1, frame.2, afterEq] using reported
      rcases (symbol_reject_reports_iff .fatArrow .typeExpr).mp ⟨absentAtKey, reportAtKey⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, afterKey,
        by simp only [parseMappingType, bind, markerResult, openingResult, keyResult, result],
        afterEq, reportEq, events⟩
  | valueRejected markerSpan openingSpan arrowSpan marker opening key arrow value =>
      rename_i afterMarker afterOpening keyRem afterArrow keyValue keyEvents valueEvents
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 + 1 }) key with
        ⟨afterKey, keyResult, keyAfter, keyEq⟩
      have frame := contextFrame keyResult
      have arrowAtKey := arrow
      rw [← keyAfter] at arrowAtKey
      have arrowResult := symbol_eq_ok_of_exactTokenParses .fatArrow .typeExpr arrowAtKey
      have valueAtArrow : elementRejects afterKey.file.id afterKey.window.endByte
          ({ afterKey with cursor := afterKey.cursor + 1 } : State).declarativeRemainder after report valueEvents := by
        simpa only [frame.1, frame.2, arrow.2, ← keyAfter, State.declarativeRemainder] using value
      rcases rejectComplete (input := { afterKey with cursor := afterKey.cursor + 1 }) valueAtArrow with
        ⟨failure, rejected, result, afterEq, reportEq, valueEq⟩
      refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
      · simp only [parseMappingType, bind, markerResult, openingResult, keyResult, arrowResult, result]
      · rw [valueEq]
        change afterKey.diagnostics ++ valueEvents = input.diagnostics ++ _
        rw [keyEq]; exact List.append_assoc _ _ _
  | closingMissing markerSpan openingSpan arrowSpan marker opening key arrow value absent reported =>
      rename_i afterMarker afterOpening keyRem afterArrow keyValue valueValue keyEvents valueEvents
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 + 1 }) key with
        ⟨afterKey, keyResult, keyAfter, keyEq⟩
      have keyFrame := contextFrame keyResult
      have arrowAtKey := arrow
      rw [← keyAfter] at arrowAtKey
      have arrowResult := symbol_eq_ok_of_exactTokenParses .fatArrow .typeExpr arrowAtKey
      have valueAtArrow : elementTrace afterKey.file.id afterKey.window.endByte
          ({ afterKey with cursor := afterKey.cursor + 1 } : State).declarativeRemainder valueValue after valueEvents := by
        simpa only [keyFrame.1, keyFrame.2, arrow.2, ← keyAfter, State.declarativeRemainder] using value
      rcases successComplete (input := { afterKey with cursor := afterKey.cursor + 1 }) valueAtArrow with
        ⟨afterValue, valueResult, valueAfter, valueEq⟩
      have valueFrame := contextFrame valueResult
      have absentAtValue : DeclarativeGrammar.TokenKindAbsentAt afterValue.tokens afterValue.window.endIndex
          afterValue.cursor (.symbol .rightParen) := by
        simpa only [← valueAfter, State.declarativeRemainder] using absent
      have reportAtValue : DeclarativeGrammar.RejectAtReports afterValue.file.id afterValue.window.endByte
          { head := .symbol .rightParen, tail := [] } .typeExpr afterValue.declarativeRemainder report := by
        simpa only [valueFrame.1, valueFrame.2, keyFrame.1, keyFrame.2, valueAfter] using reported
      rcases (symbol_reject_reports_iff .rightParen .typeExpr).mp ⟨absentAtValue, reportAtValue⟩ with
        ⟨failure, result, reportEq⟩
      refine ⟨failure, afterValue, ?_, valueAfter, reportEq, ?_⟩
      · simp only [parseMappingType, bind, markerResult, openingResult, keyResult, arrowResult, valueResult, result]
      · rw [valueEq]
        change afterKey.diagnostics ++ valueEvents = input.diagnostics ++ _
        rw [keyEq]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.MappingTypeRejectionTraceCorrespondenceProperties
/-! Exact raw mapping rejection iff the independent first-failure trace,
including the complete uncommitted Failure and every prior event occurrence. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseMappingType_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.MappingTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parseMappingType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseMappingType_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parseMappingType_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parseMappingType_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.MappingTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseMappingType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parseMappingType_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.MappingTypeTraceProperties
/-! Raw mapping execution preserves every located AST component and the
ordered key/value event suffix. Contextual mapping remains an identifier
token, and no progress, validity, or token-carrier child law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem mapping_bind_ok_parts {α β : Type} {first : Parser α} {next : α → Parser β}
    {input output : State} {value : β} (result : (first >>= next) input = .ok value output) :
    ∃ item after, first input = .ok item after ∧ next item after = .ok value output := by
  cases firstResult : first input <;> simp only [bind, firstResult] at result
  case ok item after => exact ⟨item, after, rfl, result⟩
  case reject => contradiction
  case invariant => contradiction

theorem parseMappingType_success_iff_components {input output : State} {resultValue : TypeExpr} :
    parseMappingType nested input = .ok resultValue output ↔
    ∃ marker afterMarker opening afterOpening key afterKey arrow afterArrow value afterValue closing,
      contextual .mapping .typeExpr input = .ok marker afterMarker ∧
      symbol .leftParen .typeExpr afterMarker = .ok opening afterOpening ∧
      nested afterOpening = .ok key afterKey ∧
      symbol .fatArrow .typeExpr afterKey = .ok arrow afterArrow ∧
      nested afterArrow = .ok value afterValue ∧
      symbol .rightParen .typeExpr afterValue = .ok closing output ∧
      resultValue = DeclarativeGrammar.mappingTypeTraceValue marker.span opening.span closing.span key value := by
  constructor
  · intro result
    unfold parseMappingType at result
    rcases mapping_bind_ok_parts result with ⟨marker, afterMarker, markerResult, rest⟩
    rcases mapping_bind_ok_parts rest with ⟨opening, afterOpening, openingResult, rest⟩
    rcases mapping_bind_ok_parts rest with ⟨key, afterKey, keyResult, rest⟩
    rcases mapping_bind_ok_parts rest with ⟨arrow, afterArrow, arrowResult, rest⟩
    rcases mapping_bind_ok_parts rest with ⟨value, afterValue, valueResult, rest⟩
    rcases mapping_bind_ok_parts rest with ⟨closing, afterClosing, closingResult, finished⟩
    cases finished
    exact ⟨marker, afterMarker, opening, afterOpening, key, afterKey, arrow, afterArrow, value, afterValue,
      closing, markerResult, openingResult, keyResult, arrowResult, valueResult, closingResult, rfl⟩
  · rintro ⟨marker, afterMarker, opening, afterOpening, key, afterKey, arrow, afterArrow, value, afterValue,
      closing, markerResult, openingResult, keyResult, arrowResult, valueResult, closingResult, rfl⟩
    simp only [parseMappingType, bind, markerResult, openingResult, keyResult, arrowResult, valueResult,
      closingResult, pure, DeclarativeGrammar.mappingTypeTraceValue]

theorem parseMappingType_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessSound (parseMappingType nested) (DeclarativeGrammar.MappingTypeTraceParses elementTrace) := by
  intro input output resultValue result
  rcases parseMappingType_success_iff_components.mp result with
    ⟨marker, afterMarker, opening, afterOpening, key, afterKey, arrow, afterArrow, value, afterValue,
      closing, markerResult, openingResult, keyResult, arrowResult, valueResult, closingResult, rfl⟩
  have markerParsed := contextual_success_exactTokenParses .mapping .typeExpr markerResult
  have openingParsed := symbol_success_exactTokenParses .leftParen .typeExpr openingResult
  have arrowParsed := symbol_success_exactTokenParses .fatArrow .typeExpr arrowResult
  have closingParsed := symbol_success_exactTokenParses .rightParen .typeExpr closingResult
  have markerState := (contextual_ok_tokenAt .mapping .typeExpr markerResult).2
  have openingState := (symbol_ok_tokenAt .leftParen .typeExpr openingResult).2
  have arrowState := (symbol_ok_tokenAt .fatArrow .typeExpr arrowResult).2
  have closingState := (symbol_ok_tokenAt .rightParen .typeExpr closingResult).2
  subst afterMarker afterOpening afterArrow output
  rcases successSound keyResult with ⟨keyEvents, keyParsed, keyEq⟩
  have keyFrame := contextFrame keyResult
  rcases successSound valueResult with ⟨valueEvents, valueParsed, valueEq⟩
  refine ⟨keyEvents ++ valueEvents,
    .parsed marker.span opening.span arrow.span closing.span markerParsed openingParsed keyParsed
      arrowParsed (by simpa only [keyFrame.1, keyFrame.2] using valueParsed) closingParsed, ?_⟩
  change afterValue.diagnostics = input.diagnostics ++ (keyEvents ++ valueEvents)
  change afterValue.diagnostics = afterKey.diagnostics ++ valueEvents at valueEq
  change afterKey.diagnostics = input.diagnostics ++ keyEvents at keyEq
  rw [valueEq, keyEq]
  exact List.append_assoc _ _ _

theorem parseMappingType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessComplete (parseMappingType nested) (DeclarativeGrammar.MappingTypeTraceParses elementTrace) := by
  intro input resultValue after trace parsed
  cases parsed with
  | parsed markerSpan openingSpan arrowSpan closingSpan marker opening key arrow value closing =>
      rename_i afterMarker afterOpening afterKey afterArrow afterValue keyValue valueValue keyEvents valueEvents
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 2 }) key with
        ⟨afterKeyState, keyResult, afterKeyEq, keyEq⟩
      have keyFrame := contextFrame keyResult
      have arrowAtKey : DeclarativeGrammar.ExactTokenParses (.symbol .fatArrow)
          afterKeyState.declarativeRemainder arrowSpan afterArrow := by simpa only [afterKeyEq] using arrow
      have arrowResult := symbol_eq_ok_of_exactTokenParses .fatArrow .typeExpr arrowAtKey
      have valueAtArrow : elementTrace afterKeyState.file.id afterKeyState.window.endByte
          ({ afterKeyState with cursor := afterKeyState.cursor + 1 } : State).declarativeRemainder
          valueValue afterValue valueEvents := by
        rw [arrow.2] at value
        simpa only [keyFrame.1, keyFrame.2, State.declarativeRemainder, ← afterKeyEq] using value
      rcases successComplete (input := { afterKeyState with cursor := afterKeyState.cursor + 1 }) valueAtArrow with
        ⟨afterValueState, valueResult, afterValueEq, valueEq⟩
      have closingAtValue : DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
          afterValueState.declarativeRemainder closingSpan after := by simpa only [afterValueEq] using closing
      have closingResult := symbol_eq_ok_of_exactTokenParses .rightParen .typeExpr closingAtValue
      refine ⟨{ afterValueState with cursor := afterValueState.cursor + 1 },
        parseMappingType_success_iff_components.mpr ⟨_, _, _, _, _, _, _, _, _, _, _,
          markerResult, openingResult, keyResult, arrowResult, valueResult, closingResult, rfl⟩,
        closingAtValue.2.symm, ?_⟩
      change afterValueState.diagnostics = input.diagnostics ++ (keyEvents ++ valueEvents)
      change afterValueState.diagnostics = afterKeyState.diagnostics ++ valueEvents at valueEq
      change afterKeyState.diagnostics = input.diagnostics ++ keyEvents at keyEq
      rw [valueEq, keyEq]
      exact List.append_assoc _ _ _

theorem parseMappingType_success_context
    (contextFrame : ParserSuccessContext nested) : ParserSuccessContext (parseMappingType nested) := by
  intro input output resultValue result
  rcases parseMappingType_success_iff_components.mp result with
    ⟨marker, afterMarker, opening, afterOpening, key, afterKey, arrow, afterArrow, value, afterValue,
      closing, markerResult, openingResult, keyResult, arrowResult, valueResult, closingResult, _⟩
  have markerState := (contextual_ok_tokenAt .mapping .typeExpr markerResult).2
  have openingState := (symbol_ok_tokenAt .leftParen .typeExpr openingResult).2
  have arrowState := (symbol_ok_tokenAt .fatArrow .typeExpr arrowResult).2
  have closingState := (symbol_ok_tokenAt .rightParen .typeExpr closingResult).2
  subst afterMarker afterOpening afterArrow output
  have keyFrame := contextFrame keyResult
  have valueFrame := contextFrame valueResult
  exact ⟨valueFrame.1.trans keyFrame.1, valueFrame.2.trans keyFrame.2⟩

theorem parseMappingType_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {value : TypeExpr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.MappingTypeTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parseMappingType nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseMappingType_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parseMappingType_trace_success_sound successSound contextFrame result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedTypeArgumentsRejectionTraceProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedTypeArgumentsTracePrimitiveProperties
/-! The optional angle marker and nonempty-carrier conversion are silent.
Their exact state behavior does not require any recursive child contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem requireNonempty_success_iff_toList {α : Type} (phase : ParserPhase)
    {values : DelimitedList α} {arguments : NonemptyDelimitedList α} {input output : State} :
    requireNonempty values phase input = .ok arguments output ↔
      values = { span := arguments.span, elements := arguments.elements.toList } ∧ output = input := by
  constructor
  · intro result
    unfold requireNonempty at result
    cases elements : values.elements with
    | nil => rw [elements] at result; contradiction
    | cons head tail =>
        rw [elements] at result
        cases result
        refine ⟨?_, rfl⟩
        cases values
        simp_all only [NonemptyList.toList]
  · rintro ⟨rfl, rfl⟩
    cases arguments with
    | mk span elements => cases elements; rfl

theorem requireNonempty_eq_ok_of_toList {α : Type} (phase : ParserPhase)
    (arguments : NonemptyDelimitedList α) (input : State) :
    requireNonempty { span := arguments.span, elements := arguments.elements.toList } phase input =
      .ok arguments input :=
  (requireNonempty_success_iff_toList phase).mpr ⟨rfl, rfl⟩

/-- The independent false-empty-policy structure rules out the defensive
nonempty-conversion invariant, with no validity or diagnostic assumptions. -/
theorem requireNonempty_ne_invariant_of_trace {α : Type}
    {opening closing : Symbol}
    {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {before after : DeclarativeGrammar.Remainder}
    {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.TrailingDelimitedListTraceParses opening closing false elementTrace
      source endByte before values after trace) (phase : ParserPhase) (input : State)
    (error : ParserInvariantError) : requireNonempty values phase input ≠ .invariant error := by
  have nonempty := parsed.nonempty_elements
  unfold requireNonempty
  cases elements : values.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => intro failed; cases failed

theorem parseNamedTypeArguments_eq_none_of_absent (nested : Parser TypeExpr)
    {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .less)) :
    parseNamedTypeArguments nested input = .ok none input := by
  simp only [parseNamedTypeArguments, getState, bind,
    DelimitedTraceInternals.symbol_absent .less absent, Bool.false_eq_true, if_false, pure]

theorem parseNamedTypeArguments_eq_of_present (nested : Parser TypeExpr)
    {input : State} {span : SourceSpan}
    (opening : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .less }) :
    parseNamedTypeArguments nested input =
      match delimited .less .greater false nested .typeExpr .typeExpr input with
      | .ok values next =>
          match requireNonempty values .typeExpr next with
          | .ok arguments output => .ok (some arguments) output
          | .reject failure rejected => .reject failure rejected
          | .invariant error => .invariant error
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  have present := DelimitedTraceInternals.symbol_present .less
    (input := input) (after := { input.declarativeRemainder with cursor := input.cursor + 1 }) ⟨opening, rfl⟩
  simp only [parseNamedTypeArguments, getState, bind, present, if_true, pure]
  cases delimited .less .greater false nested .typeExpr .typeExpr input with
  | reject => rfl
  | invariant => rfl
  | ok values next =>
      simp only
      cases requireNonempty values .typeExpr next <;> rfl

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedTypeArgumentsTraceProperties
/-! Exact optional nonempty named-type arguments. Recursive success and the
source/full-window frame are explicit; neither silent children nor valid or
token-preserving input is assumed by these execution contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem parseNamedTypeArguments_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessSound (parseNamedTypeArguments nested)
      (DeclarativeGrammar.NamedTypeArgumentsTraceParses elementTrace) := by
  intro input output arguments result
  by_cases present : isSymbol input .less = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .less .typeExpr present with ⟨token, tokenResult⟩
    rw [parseNamedTypeArguments_eq_of_present nested
      (symbol_ok_tokenAt .less .typeExpr tokenResult).1] at result
    cases argsResult : delimited .less .greater false nested .typeExpr .typeExpr input with
    | invariant error => simp [argsResult] at result
    | reject failure rejected => simp [argsResult] at result
    | ok values next =>
        simp only [argsResult] at result
        cases converted : requireNonempty values .typeExpr next with
        | invariant error => simp [converted] at result
        | reject failure rejected => simp [converted] at result
        | ok nonempty final =>
            simp only [converted] at result
            cases result
            have shape := (requireNonempty_success_iff_toList .typeExpr).mp converted
            rw [shape.2]
            rcases delimited_trace_success_sound successSound contextFrame
                .less .greater false .typeExpr .typeExpr argsResult with ⟨trace, parsed, diagnostics⟩
            exact ⟨trace, .present (by simpa only [shape.1] using parsed), diagnostics⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .less (Bool.eq_false_iff.mpr present)
    rw [parseNamedTypeArguments_eq_none_of_absent nested absent] at result
    cases result
    exact ⟨[], .absent absent, by simp only [List.append_nil]⟩

theorem parseNamedTypeArguments_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessComplete (parseNamedTypeArguments nested)
      (DeclarativeGrammar.NamedTypeArgumentsTraceParses elementTrace) := by
  intro input arguments after trace parsed
  cases parsed with
  | absent absent =>
      exact ⟨input, parseNamedTypeArguments_eq_none_of_absent nested absent, rfl,
        by simp only [List.append_nil]⟩
  | present parsed =>
      rcases (DeclarativeGrammar.NamedTypeArgumentsTraceParses.present parsed).present_token with
        ⟨span, opening⟩
      rcases delimited_trace_success_complete successComplete contextFrame
          .less .greater false .typeExpr .typeExpr parsed with ⟨output, result, afterEq, diagnostics⟩
      refine ⟨output, ?_, afterEq, diagnostics⟩
      rw [parseNamedTypeArguments_eq_of_present nested opening, result]
      simp only [requireNonempty_eq_ok_of_toList]

theorem parseNamedTypeArguments_success_context
    (contextFrame : ParserSuccessContext nested) :
    ParserSuccessContext (parseNamedTypeArguments nested) := by
  intro input output arguments result
  by_cases present : isSymbol input .less = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .less .typeExpr present with ⟨token, tokenResult⟩
    rw [parseNamedTypeArguments_eq_of_present nested
      (symbol_ok_tokenAt .less .typeExpr tokenResult).1] at result
    cases argsResult : delimited .less .greater false nested .typeExpr .typeExpr input with
    | invariant error => simp [argsResult] at result
    | reject failure rejected => simp [argsResult] at result
    | ok values next =>
        simp only [argsResult] at result
        cases converted : requireNonempty values .typeExpr next with
        | invariant error => simp [converted] at result
        | reject failure rejected => simp [converted] at result
        | ok nonempty final =>
            simp only [converted] at result
            cases result
            have shape := (requireNonempty_success_iff_toList .typeExpr).mp converted
            rw [shape.2]
            exact delimited_success_context contextFrame .less .greater false .typeExpr .typeExpr argsResult
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .less (Bool.eq_false_iff.mpr present)
    rw [parseNamedTypeArguments_eq_none_of_absent nested absent] at result
    cases result
    exact ⟨rfl, rfl⟩

theorem parseNamedTypeArguments_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {arguments : Option (NonemptyDelimitedList TypeExpr)}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeArgumentsTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder arguments after trace ↔
    ∃ output, parseNamedTypeArguments nested input = .ok arguments output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseNamedTypeArguments_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parseNamedTypeArguments_trace_success_sound successSound contextFrame result with
      ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedTypeFinishingTraceProperties
/-! Finishing a named type always succeeds, retaining every State field except
the exact spelling-dependent appended events. Qualified `mapping` is not the
bare spelling, and optional generic arguments determine the report's span. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem mapping_guard_iff (name : QualifiedName) :
    (name.value.components.tail.isEmpty && name.value.components.head.value == "mapping") = true ↔
      DeclarativeGrammar.UnqualifiedMappingSpelling name := by
  simp [DeclarativeGrammar.UnqualifiedMappingSpelling]

theorem makeNamedType_eq_traceValue (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    makeNamedType name arguments = DeclarativeGrammar.namedTypeTraceValue name arguments := by
  cases arguments <;> rfl

theorem finishNamedType_eq_ok_of_trace (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input : State)
    {trace : List ParseDiagnostic}
    (events : DeclarativeGrammar.NamedTypeFinishingTrace name arguments trace) :
    finishNamedType name arguments input =
      .ok (DeclarativeGrammar.namedTypeTraceValue name arguments)
        { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases events with
  | canonicalRequired spelling =>
      have selected := (mapping_guard_iff name).mpr spelling
      simp only [finishNamedType, selected, if_true, emitDiagnostic, modifyState, bind,
        pure, State.emit, makeNamedType_eq_traceValue]
      rfl
  | ordinary spelling =>
      have absent : (name.value.components.tail.isEmpty && name.value.components.head.value == "mapping") = false := by
        apply Bool.eq_false_iff.mpr
        intro selected
        exact spelling ((mapping_guard_iff name).mp selected)
      simp only [finishNamedType, absent, Bool.false_eq_true, if_false, bind, pure,
        makeNamedType_eq_traceValue]
      rfl

theorem finishNamedType_success_trace_sound (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr))
    {input output : State} {value : TypeExpr}
    (result : finishNamedType name arguments input = .ok value output) :
    ∃ trace, DeclarativeGrammar.NamedTypeFinishingTrace name arguments trace ∧
      value = DeclarativeGrammar.namedTypeTraceValue name arguments ∧
      output = { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases DeclarativeGrammar.namedTypeFinishingTrace_exists name arguments with ⟨trace, events⟩
  have expected := finishNamedType_eq_ok_of_trace name arguments input events
  rw [result] at expected
  exact ⟨trace, events, (Reply.ok.inj expected).1, (Reply.ok.inj expected).2⟩

theorem finishNamedType_success_context (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    ParserSuccessContext (finishNamedType name arguments) := by
  intro input output value result
  rcases finishNamedType_success_trace_sound name arguments result with ⟨trace, _, _, same⟩
  rw [same]
  exact ⟨rfl, rfl⟩

theorem finishNamedType_trace_success_iff (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) {input : State}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeFinishingTrace name arguments trace ↔
    ∃ output, finishNamedType name arguments input =
        .ok (DeclarativeGrammar.namedTypeTraceValue name arguments) output ∧
      output.declarativeRemainder = input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro events
    refine ⟨_, finishNamedType_eq_ok_of_trace name arguments input events, rfl, ?_⟩
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]
  · rintro ⟨output, result, _, diagnostics⟩
    rcases finishNamedType_success_trace_sound name arguments result with ⟨actual, events, _, same⟩
    rw [same] at diagnostics
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse] at diagnostics
    have traceEq := List.append_cancel_left diagnostics
    simpa only [traceEq] using events

theorem finishNamedType_ne_reject (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input rejected : State) (failure : Failure) :
    finishNamedType name arguments input ≠ .reject failure rejected := by
  rcases DeclarativeGrammar.namedTypeFinishingTrace_exists name arguments with ⟨trace, events⟩
  rw [finishNamedType_eq_ok_of_trace name arguments input events]
  intro impossible
  contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ProxyTypeRejectionTraceProperties
/-! Exact raw proxy-type rejection uses only nested rejection contracts.
The marker contributes no event, and nested failures preserve their complete
Failure and returned State without requiring successful context or token laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {typeRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseProxyType_reject_iff_components {input rejected : State} {failure : Failure} :
    parseProxyType nested input = .reject failure rejected ↔
    symbol .at .typeExpr input = .reject failure rejected ∨
      ∃ marker afterMarker, symbol .at .typeExpr input = .ok marker afterMarker ∧
        nested afterMarker = .reject failure rejected := by
  constructor
  · intro result
    unfold parseProxyType at result
    cases markerResult : symbol .at .typeExpr input with
    | invariant => simp only [markerResult] at result; contradiction
    | reject markerFailure markerRejected =>
        simp only [markerResult] at result
        cases result
        exact .inl rfl
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases typeResult : nested afterMarker with
        | invariant => simp only [typeResult] at result; contradiction
        | ok => simp only [typeResult] at result; contradiction
        | reject typeFailure innerRejected =>
            simp only [typeResult] at result
            cases result
            exact .inr ⟨marker, afterMarker, rfl, typeResult⟩
  · rintro (markerResult | ⟨marker, afterMarker, markerResult, typeResult⟩)
    · simp only [parseProxyType, markerResult]
    · simp only [parseProxyType, markerResult, typeResult]

theorem parseProxyType_reject_trace_sound
    (rejectSound : ParserTraceRejectSound nested typeRejects) :
    ParserTraceRejectSound (parseProxyType nested) (DeclarativeGrammar.ProxyTypeTraceRejects typeRejects) := by
  intro input rejected failure result
  rcases parseProxyType_reject_iff_components.mp result with markerResult |
      ⟨marker, afterMarker, markerResult, typeResult⟩
  · have same := symbol_reject_state_eq .at .typeExpr markerResult
    subst rejected
    have reported := (symbol_reject_reports_iff .at .typeExpr).mpr ⟨failure, markerResult, rfl⟩
    exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  · have markerParsed := symbol_success_exactTokenParses .at .typeExpr markerResult
    have markerState := (symbol_ok_tokenAt .at .typeExpr markerResult).2
    subst afterMarker
    rcases rejectSound typeResult with ⟨trace, typed, events⟩
    exact ⟨trace, .innerRejected marker.span markerParsed typed, events⟩

theorem parseProxyType_trace_reject_complete
    (rejectComplete : ParserTraceRejectComplete nested typeRejects) :
    ParserTraceRejectComplete (parseProxyType nested) (DeclarativeGrammar.ProxyTypeTraceRejects typeRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (symbol_reject_reports_iff .at .typeExpr).mp ⟨absent, reported⟩ with
        ⟨failure, markerResult, reportEq⟩
      exact ⟨failure, input, parseProxyType_reject_iff_components.mpr (.inl markerResult),
        rfl, reportEq, by simp⟩
  | innerRejected markerSpan marker typed =>
      have markerResult := symbol_eq_ok_of_exactTokenParses .at .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) typed with
        ⟨failure, rejected, typeResult, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, parseProxyType_reject_iff_components.mpr
        (.inr ⟨_, _, markerResult, typeResult⟩), afterEq, reportEq, events⟩

theorem parseProxyType_trace_reject_iff
    (rejectSound : ParserTraceRejectSound nested typeRejects)
    (rejectComplete : ParserTraceRejectComplete nested typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ProxyTypeTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parseProxyType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseProxyType_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parseProxyType_reject_trace_sound rejectSound result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parseProxyType_trace_reject_failure_iff
    (rejectSound : ParserTraceRejectSound nested typeRejects)
    (rejectComplete : ParserTraceRejectComplete nested typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ProxyTypeTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseProxyType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parseProxyType_trace_reject_iff rejectSound rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ProxyTypeSuccessTraceProperties
/-! Actual raw proxy-type execution preserves exactly the nested events.
Success soundness/completeness need only the corresponding nested contract.
Source/full-window preservation remains a separate context contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {typeTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem parseProxyType_success_iff_components {input output : State} {value : TypeExpr} :
    parseProxyType nested input = .ok value output ↔
    ∃ marker afterMarker type,
      symbol .at .typeExpr input = .ok marker afterMarker ∧
      nested afterMarker = .ok type output ∧
      value = { span := SourceSpan.cover marker.span type.span, value := .proxy marker.span type } := by
  constructor
  · intro result
    unfold parseProxyType at result
    cases markerResult : symbol .at .typeExpr input with
    | reject => simp only [markerResult] at result; contradiction
    | invariant => simp only [markerResult] at result; contradiction
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases typeResult : nested afterMarker with
        | reject => simp only [typeResult] at result; contradiction
        | invariant => simp only [typeResult] at result; contradiction
        | ok type next =>
            simp only [typeResult] at result
            cases result
            exact ⟨marker, afterMarker, type, rfl, typeResult, rfl⟩
  · rintro ⟨marker, afterMarker, type, markerResult, typeResult, rfl⟩
    simp only [parseProxyType, markerResult, typeResult]

theorem parseProxyType_trace_success_sound
    (successSound : ParserTraceSuccessSound nested typeTrace) :
    ParserTraceSuccessSound (parseProxyType nested) (DeclarativeGrammar.ProxyTypeTraceParses typeTrace) := by
  intro input output value result
  rcases parseProxyType_success_iff_components.mp result with
    ⟨marker, afterMarker, type, markerResult, typeResult, rfl⟩
  have markerParsed := symbol_success_exactTokenParses .at .typeExpr markerResult
  have markerState := (symbol_ok_tokenAt .at .typeExpr markerResult).2
  subst afterMarker
  rcases successSound typeResult with ⟨trace, typed, events⟩
  exact ⟨trace, .parsed marker.span markerParsed typed, events⟩

theorem parseProxyType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested typeTrace) :
    ParserTraceSuccessComplete (parseProxyType nested) (DeclarativeGrammar.ProxyTypeTraceParses typeTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed markerSpan marker typed =>
      have markerResult := symbol_eq_ok_of_exactTokenParses .at .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) typed with
        ⟨output, typeResult, afterEq, events⟩
      exact ⟨output, parseProxyType_success_iff_components.mpr
        ⟨_, _, _, markerResult, typeResult, rfl⟩, afterEq, events⟩

theorem parseProxyType_success_context (contextFrame : ParserSuccessContext nested) :
    ParserSuccessContext (parseProxyType nested) := by
  intro input output value result
  rcases parseProxyType_success_iff_components.mp result with
    ⟨marker, afterMarker, type, markerResult, typeResult, _⟩
  have frame := contextFrame typeResult
  rw [(symbol_ok_tokenAt .at .typeExpr markerResult).2] at frame
  exact frame

theorem parseProxyType_trace_success_iff
    (successSound : ParserTraceSuccessSound nested typeTrace)
    (successComplete : ParserTraceSuccessComplete nested typeTrace)
    {input : State} {value : TypeExpr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ProxyTypeTraceParses typeTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parseProxyType nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseProxyType_trace_success_complete successComplete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parseProxyType_trace_success_sound successSound result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans diagnostics)
    simpa only [afterEq, same] using parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.QualifiedNameTraceSoundnessProperties
/-! Unconditional exact checked-name traces and unchanged diagnostic context. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

theorem qualifiedNameTail_success_trace_sound
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input name output,
      qualifiedNameTail context phase first fuel last tailRev input = .ok name output →
      ∃ components trace,
        name = DeclarativeGrammar.qualifiedNameFromSuffix first last tailRev.reverse components ∧
        DeclarativeGrammar.DottedIdentifierTailTraceParses input.file.id input.window.endByte
          input.declarativeRemainder components output.declarativeRemainder trace ∧
        output.diagnostics = input.diagnostics ++ trace ∧
        output.file = input.file ∧ output.window = input.window := by
  intro fuel
  induction fuel with
  | zero => intro last tailRev input name output result; simp [qualifiedNameTail] at result
  | succ fuel ih =>
      intro last tailRev input name output result
      unfold qualifiedNameTail at result
      split at result
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            have dotParsed := symbol_success_exactTokenParses .dot context dotResult
            have dotState := (symbol_ok_tokenAt .dot context dotResult).2
            subst afterDot
            simp only [dotResult] at result
            cases childResult : identifier context { input with cursor := input.cursor + 1 } with
            | invariant error => simp [childResult] at result
            | reject failure rejected => simp [childResult] at result
            | ok component next =>
                simp only [childResult] at result
                rcases identifier_success_trace_sound context childResult with ⟨headTrace, child, childEq⟩
                have frame := identifier_success_context_eq context childResult
                rcases ih component (component :: tailRev) next name output result with
                  ⟨components, tailTrace, nameEq, tail, events, fileEq, windowEq⟩
                refine ⟨component :: components, headTrace ++ tailTrace, ?_,
                  .next dot.span dotParsed child ?_, ?_, fileEq.trans frame.1, windowEq.trans frame.2⟩
                · simpa only [DeclarativeGrammar.qualifiedNameFromSuffix, DeclarativeGrammar.finalIdentifier,
                    List.reverse_cons, List.append_assoc, List.singleton_append] using nameEq
                · simpa only [frame.1, frame.2] using tail
                · rw [events, childEq]; exact List.append_assoc _ _ _
      · rename_i noDot
        have stopped := symbolAbsentAt_of_isSymbol_eq_false .dot (Bool.eq_false_iff.mpr noDot)
        unfold finishQualifiedName at result
        cases result
        exact ⟨[], [], by simp [DeclarativeGrammar.qualifiedNameFromSuffix, DeclarativeGrammar.finalIdentifier],
          .done stopped, by simp, rfl, rfl⟩

theorem qualifiedNameTail_success_context (context : ParseContext) (phase : ParserPhase)
    (first last : Identifier) (fuel : Nat) (tailRev : List Identifier)
    {input output : State} {name : QualifiedName}
    (result : qualifiedNameTail context phase first fuel last tailRev input = .ok name output) :
    output.file = input.file ∧ output.window = input.window := by
  rcases qualifiedNameTail_success_trace_sound context phase first fuel last tailRev input name output result with
    ⟨_, _, _, _, _, frame⟩
  exact frame

end QualifiedNameInternals

theorem qualifiedName_trace_success_sound (context : ParseContext) (phase : ParserPhase) :
    ParserTraceSuccessSound (qualifiedName context phase) DeclarativeGrammar.QualifiedNameTraceParses := by
  intro input output name result
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first next =>
      simp only [firstResult] at result
      rcases identifier_success_trace_sound context firstResult with ⟨firstTrace, head, firstEq⟩
      have frame := identifier_success_context_eq context firstResult
      rcases QualifiedNameInternals.qualifiedNameTail_success_trace_sound context phase first
          (next.remainingCount + 1) first [] next name output result with
        ⟨components, tailTrace, nameEq, tail, events, _⟩
      refine ⟨firstTrace ++ tailTrace, ?_, ?_⟩
      · rw [nameEq]
        exact .parsed head (by simpa only [frame.1, frame.2] using tail)
      · rw [events, firstEq]; exact List.append_assoc _ _ _

theorem qualifiedName_success_context (context : ParseContext) (phase : ParserPhase) :
    ParserSuccessContext (qualifiedName context phase) := by
  intro input output name result
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first next =>
      simp only [firstResult] at result
      have firstFrame := identifier_success_context_eq context firstResult
      have tailFrame := QualifiedNameInternals.qualifiedNameTail_success_context context phase
        first first (next.remainingCount + 1) [] result
      exact ⟨tailFrame.1.trans firstFrame.1, tailFrame.2.trans firstFrame.2⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.QualifiedNameRejectionTraceSoundnessProperties
/-! Every rejected qualified name retains the precise missing-name report
without committing it, after all previously emitted checked-name events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

theorem qualifiedNameTail_reject_trace_sound
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input failure rejected,
      qualifiedNameTail context phase first fuel last tailRev input = .reject failure rejected →
      ∃ trace, DeclarativeGrammar.DottedIdentifierTailTraceRejects context
        input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro last tailRev input failure rejected result; simp [qualifiedNameTail] at result
  | succ fuel ih =>
      intro last tailRev input failure rejected result
      unfold qualifiedNameTail at result
      split at result
      · rename_i present
        rcases symbol_eq_ok_of_isSymbol_eq_true .dot context present with ⟨dot, dotResult⟩
        have dotParsed := symbol_success_exactTokenParses .dot context dotResult
        simp only [dotResult] at result
        cases childResult : identifier context { input with cursor := input.cursor + 1 } with
        | invariant error => simp [childResult] at result
        | reject childFailure childRejected =>
            simp only [childResult] at result
            cases result
            have unchanged := identifier_reject_state_eq context childResult
            subst rejected
            rcases (identifier_reject_reports_iff context).mpr ⟨_, childResult, rfl⟩ with
              ⟨absent, reported⟩
            exact ⟨[], .componentRejected dot.span dotParsed absent reported,
              by simp only [List.append_nil]; rfl⟩
        | ok component next =>
            simp only [childResult] at result
            rcases identifier_success_trace_sound context childResult with ⟨headTrace, name, headEvents⟩
            have frame := identifier_success_context_eq context childResult
            rcases ih component (component :: tailRev) next failure rejected result with
              ⟨tailTrace, tail, events⟩
            refine ⟨headTrace ++ tailTrace, .laterRejected dot.span dotParsed name ?_, ?_⟩
            · simpa only [frame.1, frame.2] using tail
            · rw [events, headEvents]; exact List.append_assoc _ _ _
      · unfold finishQualifiedName at result
        contradiction

end QualifiedNameInternals

theorem qualifiedName_reject_trace_sound (context : ParseContext) (phase : ParserPhase) :
    ParserTraceRejectSound (qualifiedName context phase)
      (DeclarativeGrammar.QualifiedNameTraceRejects context) := by
  intro input rejected failure result
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      have unchanged := identifier_reject_state_eq context firstResult
      subst rejected
      rcases (identifier_reject_reports_iff context).mpr ⟨_, firstResult, rfl⟩ with
        ⟨absent, reported⟩
      exact ⟨[], .firstRejected absent reported, by simp⟩
  | ok first next =>
      simp only [firstResult] at result
      rcases identifier_success_trace_sound context firstResult with ⟨firstTrace, head, firstEvents⟩
      have frame := identifier_success_context_eq context firstResult
      rcases QualifiedNameInternals.qualifiedNameTail_reject_trace_sound context phase first
          (next.remainingCount + 1) first [] next failure rejected result with
        ⟨tailTrace, tail, events⟩
      refine ⟨firstTrace ++ tailTrace, .tailRejected head ?_, ?_⟩
      · simpa only [frame.1, frame.2] using tail
      · rw [events, firstEvents]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.QualifiedNameRejectionTraceCompletenessProperties
/-! Independent missing-name traces execute with sufficient raw-tail fuel
and with the public parser's actual post-first-name production fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

open DelimitedTraceInternals

theorem qualifiedNameTail_trace_reject_complete
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.DottedIdentifierTailTraceRejects context
      input.file.id input.window.endByte input.declarativeRemainder after report trace)
    (adequate : input.remainingCount < fuel) :
    ∃ failure rejected, qualifiedNameTail context phase first fuel last tailRev input =
      .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      failure.toDiagnostic = report ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing last tailRev input after report trace with
  | zero => omega
  | succ fuel ih =>
      cases rejection with
      | componentRejected dotSpan dot absent reported =>
          have dotResult := symbol_eq_ok_of_exactTokenParses .dot context dot
          have present := symbol_present .dot dot
          rcases dot with ⟨dotToken, rfl⟩
          rcases (identifier_reject_reports_iff context
              (input := { input with cursor := input.cursor + 1 })).mp ⟨absent, reported⟩ with
            ⟨failure, childResult, reportEq⟩
          exact ⟨failure, { input with cursor := input.cursor + 1 },
            by simp only [qualifiedNameTail, present, if_true, dotResult, childResult],
            rfl, reportEq, by simp only [List.append_nil]; rfl⟩
      | laterRejected dotSpan dot name tail =>
          rename_i afterDot afterComponent component headTrace tailTrace
          have dotResult := symbol_eq_ok_of_exactTokenParses .dot context dot
          have present := symbol_present .dot dot
          rcases dot with ⟨dotToken, rfl⟩
          rcases (identifier_trace_success_iff context
              (input := { input with cursor := input.cursor + 1 })).mp name with
            ⟨next, childResult, afterEq, headEvents⟩
          have frame := identifier_success_context_eq context childResult
          have tailAtNext : DeclarativeGrammar.DottedIdentifierTailTraceRejects context
              next.file.id next.window.endByte next.declarativeRemainder after report tailTrace := by
            simpa only [frame.1, frame.2, afterEq] using tail
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := dotToken.1
            have nextCursor := (DeclarativeGrammar.identifierTraceParses_iff.mp name).1.2.2.2
            change afterComponent.cursor = input.cursor + 1 + 1 at nextCursor
            have cursorEq : next.cursor = afterComponent.cursor := congrArg DeclarativeGrammar.Remainder.cursor afterEq
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          rcases ih component (component :: tailRev) tailAtNext nextAdequate with
            ⟨failure, rejected, result, finalEq, reportEq, events⟩
          refine ⟨failure, rejected, ?_, finalEq, reportEq, ?_⟩
          · simpa only [qualifiedNameTail, present, if_true, dotResult, childResult] using result
          · rw [events, headEvents]; exact List.append_assoc _ _ _

theorem qualifiedNameTail_production_trace_reject_complete
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier) (tailRev : List Identifier)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.DottedIdentifierTailTraceRejects context
      input.file.id input.window.endByte input.declarativeRemainder after report trace) :
    ∃ failure rejected, qualifiedNameTail context phase first (input.remainingCount + 1) last tailRev input =
      .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      failure.toDiagnostic = report ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  qualifiedNameTail_trace_reject_complete context phase first last (input.remainingCount + 1)
    tailRev rejection (by omega)

end QualifiedNameInternals

theorem qualifiedName_trace_reject_complete (context : ParseContext) (phase : ParserPhase) :
    ParserTraceRejectComplete (qualifiedName context phase)
      (DeclarativeGrammar.QualifiedNameTraceRejects context) := by
  intro input after report trace rejection
  cases rejection with
  | firstRejected absent reported =>
      rcases (identifier_reject_reports_iff context).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [qualifiedName, result], rfl, reportEq, by simp⟩
  | tailRejected head tail =>
      rcases (identifier_trace_success_iff context).mp head with ⟨next, firstResult, afterEq, firstEvents⟩
      have frame := identifier_success_context_eq context firstResult
      have tailAtNext := tail
      rw [← afterEq, ← frame.1, ← frame.2] at tailAtNext
      rcases QualifiedNameInternals.qualifiedNameTail_production_trace_reject_complete context phase
          _ _ [] tailAtNext with ⟨failure, rejected, result, finalEq, reportEq, events⟩
      refine ⟨failure, rejected, ?_, finalEq, reportEq, ?_⟩
      · simpa only [qualifiedName, firstResult] using result
      · rw [events, firstEvents]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.QualifiedNameRejectionTraceCorrespondenceProperties
/-! Exact rejection correspondence, including full uncommitted Failure data,
arbitrary earlier events, raw reverse prefixes, and actual production fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

theorem qualifiedNameTail_trace_reject_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier) {input : State}
    (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DottedIdentifierTailTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, qualifiedNameTail context phase first fuel last tailRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact qualifiedNameTail_trace_reject_complete context phase first last fuel tailRev rejection adequate
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases qualifiedNameTail_reject_trace_sound context phase first fuel last tailRev input failure rejected result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem qualifiedNameTail_trace_reject_failure_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier) {input : State}
    (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DottedIdentifierTailTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, qualifiedNameTail context phase first fuel last tailRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [qualifiedNameTail_trace_reject_iff context phase first last fuel tailRev adequate]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem qualifiedNameTail_production_trace_reject_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (tailRev : List Identifier) {input : State}
    {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DottedIdentifierTailTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected,
      qualifiedNameTail context phase first (input.remainingCount + 1) last tailRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  qualifiedNameTail_trace_reject_iff context phase first last (input.remainingCount + 1) tailRev (by omega)

theorem qualifiedNameTail_production_trace_reject_failure_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (tailRev : List Identifier) {input : State}
    {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DottedIdentifierTailTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected,
      qualifiedNameTail context phase first (input.remainingCount + 1) last tailRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  qualifiedNameTail_trace_reject_failure_iff context phase first last (input.remainingCount + 1) tailRev (by omega)

end QualifiedNameInternals

theorem qualifiedName_trace_reject_iff (context : ParseContext) (phase : ParserPhase)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.QualifiedNameTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, qualifiedName context phase input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact qualifiedName_trace_reject_complete context phase
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases qualifiedName_reject_trace_sound context phase result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem qualifiedName_trace_reject_failure_iff (context : ParseContext) (phase : ParserPhase)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.QualifiedNameTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, qualifiedName context phase input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [qualifiedName_trace_reject_iff context phase]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.QualifiedNameRejectionTraceStateProperties
/-! Concrete checked qualified-name rejection fixes the complete state while
keeping the reported Failure uncommitted, even for arbitrary input carriers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

theorem qualifiedNameTail_reject_context
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input failure rejected,
      qualifiedNameTail context phase first fuel last tailRev input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window := by
  intro fuel
  induction fuel with
  | zero => intro last tailRev input failure rejected result; simp [qualifiedNameTail] at result
  | succ fuel ih =>
      intro last tailRev input failure rejected result
      unfold qualifiedNameTail at result
      split at result
      · rename_i present
        rcases symbol_eq_ok_of_isSymbol_eq_true .dot context present with ⟨dot, dotResult⟩
        simp only [dotResult] at result
        cases childResult : identifier context { input with cursor := input.cursor + 1 } with
        | invariant error => simp [childResult] at result
        | reject childFailure childRejected =>
            simp only [childResult] at result
            cases result
            rw [identifier_reject_state_eq context childResult]
            exact ⟨rfl, rfl⟩
        | ok component next =>
            simp only [childResult] at result
            have frame := identifier_success_context_eq context childResult
            have later := ih component (component :: tailRev) next failure rejected result
            exact ⟨later.1.trans frame.1, later.2.trans frame.2⟩
      · unfold finishQualifiedName at result
        contradiction

end QualifiedNameInternals

theorem qualifiedName_reject_context (context : ParseContext) (phase : ParserPhase)
    {input rejected : State} {failure : Failure}
    (result : qualifiedName context phase input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      rw [identifier_reject_state_eq context firstResult]
      exact ⟨rfl, rfl⟩
  | ok first next =>
      simp only [firstResult] at result
      have firstFrame := identifier_success_context_eq context firstResult
      have tailFrame := QualifiedNameInternals.qualifiedNameTail_reject_context context phase first
        (next.remainingCount + 1) first [] next failure rejected result
      exact ⟨tailFrame.1.trans firstFrame.1, tailFrame.2.trans firstFrame.2⟩

theorem qualifiedName_reject_state_eq_of_trace (context : ParseContext) (phase : ParserPhase)
    {input rejected : State} {failure : Failure} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (result : qualifiedName context phase input = .reject failure rejected)
    (rejection : DeclarativeGrammar.QualifiedNameTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    rejected = { input with
      cursor := after.cursor
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases qualifiedName_reject_trace_sound context phase result with ⟨actualTrace, actual, actualEq⟩
  have same := actual.result_unique rejection
  have tokensEq : rejected.tokens = input.tokens := actual.output_window.1
  have cursorEq : rejected.cursor = after.cursor := congrArg DeclarativeGrammar.Remainder.cursor same.1
  have frame := qualifiedName_reject_context context phase result
  have events := congrArg List.reverse actualEq
  have diagnosticsEq : rejected.diagnosticsRev = trace.reverse ++ input.diagnosticsRev := by
    simpa only [same.2.2, State.diagnostics, List.reverse_append, List.reverse_reverse] using events
  cases input
  cases rejected
  simp_all only [State.declarativeRemainder]

theorem qualifiedName_eq_reject_of_trace (context : ParseContext) (phase : ParserPhase)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.QualifiedNameTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    qualifiedName context phase input = .reject failure { input with
      cursor := after.cursor
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases (qualifiedName_trace_reject_failure_iff context phase).mp rejection with ⟨rejected, result, _, _⟩
  exact qualifiedName_reject_state_eq_of_trace context phase result rejection ▸ result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.QualifiedNameTraceCompletenessProperties
/-! Checked qualified names execute every independent trace at production fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

open DelimitedTraceInternals

theorem qualifiedNameTail_trace_success_complete
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier)
    {input : State} {components : List Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.DottedIdentifierTailTraceParses input.file.id input.window.endByte
      input.declarativeRemainder components after trace)
    (adequate : input.remainingCount < fuel) :
    ∃ output, qualifiedNameTail context phase first fuel last tailRev input = .ok
        (DeclarativeGrammar.qualifiedNameFromSuffix first last tailRev.reverse components) output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing last tailRev input components after trace with
  | zero => omega
  | succ fuel ih =>
      cases parsed with
      | done stopped =>
          exact ⟨input, by simp only [qualifiedNameTail, symbol_absent .dot stopped,
            Bool.false_eq_true, if_false, finishQualifiedName, DeclarativeGrammar.qualifiedNameFromSuffix,
            DeclarativeGrammar.finalIdentifier, List.append_nil], rfl, by simp⟩
      | next dotSpan dot name tail =>
          rename_i afterDot afterComponent component components headTrace tailTrace
          have dotResult := symbol_eq_ok_of_exactTokenParses .dot context dot
          have dotPresent := symbol_present .dot dot
          rcases dot with ⟨dotToken, rfl⟩
          rcases (identifier_trace_success_iff context
              (input := { input with cursor := input.cursor + 1 })).mp name with
            ⟨next, childResult, afterEq, childEvents⟩
          have frame := identifier_success_context_eq context childResult
          have tailAtNext : DeclarativeGrammar.DottedIdentifierTailTraceParses next.file.id next.window.endByte
              next.declarativeRemainder components after tailTrace := by
            simpa only [frame.1, frame.2, afterEq] using tail
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := dotToken.1
            have nextCursor := (DeclarativeGrammar.identifierTraceParses_iff.mp name).1.2.2.2
            change afterComponent.cursor = input.cursor + 1 + 1 at nextCursor
            have cursorEq : next.cursor = afterComponent.cursor := congrArg DeclarativeGrammar.Remainder.cursor afterEq
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          rcases ih component (component :: tailRev) tailAtNext nextAdequate with
            ⟨output, result, finalEq, events⟩
          refine ⟨output, ?_, finalEq, ?_⟩
          · simp only [qualifiedNameTail, dotPresent, if_true, dotResult, childResult]
            simpa only [DeclarativeGrammar.qualifiedNameFromSuffix, DeclarativeGrammar.finalIdentifier,
              List.reverse_cons, List.append_assoc, List.singleton_append] using result
          · rw [events, childEvents]; exact List.append_assoc _ _ _

theorem qualifiedNameTail_production_trace_success_complete
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier) (tailRev : List Identifier)
    {input : State} {components : List Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.DottedIdentifierTailTraceParses input.file.id input.window.endByte
      input.declarativeRemainder components after trace) :
    ∃ output, qualifiedNameTail context phase first (input.remainingCount + 1) last tailRev input = .ok
        (DeclarativeGrammar.qualifiedNameFromSuffix first last tailRev.reverse components) output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  qualifiedNameTail_trace_success_complete context phase first last (input.remainingCount + 1)
    tailRev parsed (by omega)

end QualifiedNameInternals

theorem qualifiedName_trace_success_complete (context : ParseContext) (phase : ParserPhase) :
    ParserTraceSuccessComplete (qualifiedName context phase) DeclarativeGrammar.QualifiedNameTraceParses := by
  intro input name after trace parsed
  cases parsed with
  | parsed head tail =>
      rcases (identifier_trace_success_iff context).mp head with ⟨next, firstResult, afterEq, firstEvents⟩
      have frame := identifier_success_context_eq context firstResult
      have tailAtNext := tail
      rw [← afterEq, ← frame.1, ← frame.2] at tailAtNext
      rcases QualifiedNameInternals.qualifiedNameTail_production_trace_success_complete context phase
          _ _ [] tailAtNext with ⟨output, result, finalEq, events⟩
      refine ⟨output, ?_, finalEq, ?_⟩
      · simpa only [qualifiedName, firstResult, DeclarativeGrammar.tracedQualifiedName,
          List.reverse_nil] using result
      · rw [events, firstEvents]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.QualifiedNameTraceCorrespondenceProperties
/-! Exact AST, remainder, and prior-preserving traces, including arbitrary
tail accumulators and the concrete public parser's complete output state. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

theorem qualifiedNameTail_trace_success_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier) {input : State}
    (adequate : input.remainingCount < fuel) {name : QualifiedName}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ components,
      name = DeclarativeGrammar.qualifiedNameFromSuffix first last tailRev.reverse components ∧
      DeclarativeGrammar.DottedIdentifierTailTraceParses input.file.id input.window.endByte
        input.declarativeRemainder components after trace) ↔
    ∃ output, qualifiedNameTail context phase first fuel last tailRev input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨components, rfl, parsed⟩
    exact qualifiedNameTail_trace_success_complete context phase first last fuel tailRev parsed adequate
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases qualifiedNameTail_success_trace_sound context phase first fuel last tailRev input name output result with
      ⟨components, actualTrace, valueEq, parsed, actualEq, _⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    exact ⟨components, valueEq, by simpa only [afterEq, events] using parsed⟩

theorem qualifiedNameTail_production_trace_success_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (tailRev : List Identifier) {input : State} {name : QualifiedName}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ components,
      name = DeclarativeGrammar.qualifiedNameFromSuffix first last tailRev.reverse components ∧
      DeclarativeGrammar.DottedIdentifierTailTraceParses input.file.id input.window.endByte
        input.declarativeRemainder components after trace) ↔
    ∃ output, qualifiedNameTail context phase first (input.remainingCount + 1) last tailRev input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  qualifiedNameTail_trace_success_iff context phase first last (input.remainingCount + 1) tailRev (by omega)

end QualifiedNameInternals

theorem qualifiedName_trace_success_iff (context : ParseContext) (phase : ParserPhase)
    {input : State} {name : QualifiedName} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.QualifiedNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace ↔
    ∃ output, qualifiedName context phase input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact qualifiedName_trace_success_complete context phase
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases qualifiedName_trace_success_sound context phase result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

/-- Narrow exact traces strengthen ordinary AST/remainder laws to complete
state equality, without changing any generic ordinary-success contract. -/
theorem qualifiedName_success_state_eq_of_trace (context : ParseContext) (phase : ParserPhase)
    {input output : State} {name : QualifiedName} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (result : qualifiedName context phase input = .ok name output)
    (parsed : DeclarativeGrammar.QualifiedNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace) :
    output = { input with
      cursor := after.cursor
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases qualifiedName_trace_success_sound context phase result with ⟨actualTrace, actual, actualEq⟩
  have same := actual.result_unique parsed
  have tokensEq : output.tokens = input.tokens := actual.output_window.1
  have cursorEq : output.cursor = after.cursor := congrArg DeclarativeGrammar.Remainder.cursor same.2.1
  have frame := qualifiedName_success_context context phase result
  have events := congrArg List.reverse actualEq
  have diagnosticsEq : output.diagnosticsRev = trace.reverse ++ input.diagnosticsRev := by
    simpa only [same.2.2, State.diagnostics, List.reverse_append, List.reverse_reverse] using events
  cases input
  cases output
  simp_all only [State.declarativeRemainder]

theorem qualifiedName_eq_ok_of_trace (context : ParseContext) (phase : ParserPhase)
    {input : State} {name : QualifiedName} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.QualifiedNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace) :
    qualifiedName context phase input = .ok name { input with
      cursor := after.cursor
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases qualifiedName_trace_success_complete context phase parsed with ⟨output, result, _, _⟩
  exact qualifiedName_success_state_eq_of_trace context phase result parsed ▸ result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedTypeRejectionTraceProperties
/-! Exact raw named-type rejection composes qualified-name and argument
failures. Finishing always succeeds, so no finishing event precedes rejection.
Only the recursive child contracts needed by optional arguments are required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseNamedType_reject_iff_components
    {input rejected : State} {failure : Failure} :
    parseNamedType nested input = .reject failure rejected ↔
      qualifiedName .typeExpr .typeExpr input = .reject failure rejected ∨
      ∃ name afterName, qualifiedName .typeExpr .typeExpr input = .ok name afterName ∧
        parseNamedTypeArguments nested afterName = .reject failure rejected := by
  cases nameResult : qualifiedName .typeExpr .typeExpr input with
  | invariant error => simp [parseNamedType, bind, nameResult]
  | reject nameFailure nameRejected => simp [parseNamedType, bind, nameResult]
  | ok name afterName =>
      cases argsResult : parseNamedTypeArguments nested afterName with
      | invariant error => simp [parseNamedType, bind, nameResult, argsResult]
      | reject argsFailure argsRejected =>
          simp [parseNamedType, bind, nameResult, argsResult]
          constructor
          · rintro ⟨rfl, rfl⟩
            exact ⟨name, afterName, ⟨rfl, rfl⟩, argsResult⟩
          · rintro ⟨otherName, otherState, ⟨rfl, rfl⟩, same⟩
            rw [argsResult] at same
            exact Reply.reject.inj same
      | ok arguments afterArguments =>
          simp only [parseNamedType, bind, nameResult, argsResult]
          constructor
          · intro impossible
            exact False.elim (finishNamedType_ne_reject name arguments afterArguments rejected failure impossible)
          · rintro (impossible | ⟨otherName, otherState, nameEq, argsEq⟩)
            · contradiction
            · cases nameEq
              rw [argsResult] at argsEq
              contradiction

theorem parseNamedType_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseNamedType nested)
      (DeclarativeGrammar.NamedTypeTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  rcases parseNamedType_reject_iff_components.mp result with nameRejected | ⟨name, afterName, nameResult, argsResult⟩
  · rcases qualifiedName_reject_trace_sound .typeExpr .typeExpr nameRejected with ⟨trace, name, events⟩
    exact ⟨trace, .nameRejected name, events⟩
  · rcases qualifiedName_trace_success_sound .typeExpr .typeExpr nameResult with ⟨nameEvents, nameParsed, nameEq⟩
    have frame := qualifiedName_success_context .typeExpr .typeExpr nameResult
    rcases parseNamedTypeArguments_reject_trace_sound successSound rejectSound contextFrame argsResult with
      ⟨argumentEvents, arguments, argumentEq⟩
    refine ⟨nameEvents ++ argumentEvents, .argumentsRejected nameParsed ?_, ?_⟩
    · simpa only [frame.1, frame.2] using arguments
    · rw [argumentEq, nameEq]; exact List.append_assoc _ _ _

theorem parseNamedType_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseNamedType nested)
      (DeclarativeGrammar.NamedTypeTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | nameRejected name =>
      rcases qualifiedName_trace_reject_complete .typeExpr .typeExpr name with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, parseNamedType_reject_iff_components.mpr (.inl result), afterEq, reportEq, events⟩
  | argumentsRejected name arguments =>
      rcases qualifiedName_trace_success_complete .typeExpr .typeExpr name with
        ⟨afterName, nameResult, afterEq, nameEvents⟩
      have frame := qualifiedName_success_context .typeExpr .typeExpr nameResult
      have argsAtNext := arguments
      rw [← afterEq, ← frame.1, ← frame.2] at argsAtNext
      rcases parseNamedTypeArguments_trace_reject_complete successComplete rejectComplete contextFrame argsAtNext with
        ⟨failure, rejected, result, finalEq, reportEq, events⟩
      refine ⟨failure, rejected, parseNamedType_reject_iff_components.mpr (.inr ⟨_, afterName, nameResult, result⟩),
        finalEq, reportEq, ?_⟩
      rw [events, nameEvents]; exact List.append_assoc _ _ _

theorem parseNamedType_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parseNamedType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseNamedType_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parseNamedType_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parseNamedType_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseNamedType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parseNamedType_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedTypeTraceProperties
/-! Raw named-type execution retains exact AST, remainder, and three ordered
diagnostic suffixes. Recursive argument children need only explicit success
and source/full-window contracts. Type-dispatch priority is not assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem named_bind_ok_parts {α β : Type} {first : Parser α} {next : α → Parser β}
    {input output : State} {value : β} (result : (first >>= next) input = .ok value output) :
    ∃ item after, first input = .ok item after ∧ next item after = .ok value output := by
  cases firstResult : first input <;> simp only [bind, firstResult] at result
  case ok item after => exact ⟨item, after, rfl, result⟩
  case reject => contradiction
  case invariant => contradiction

theorem parseNamedType_success_iff_components {input output : State} {value : TypeExpr} :
    parseNamedType nested input = .ok value output ↔
    ∃ name afterName arguments afterArguments,
      qualifiedName .typeExpr .typeExpr input = .ok name afterName ∧
      parseNamedTypeArguments nested afterName = .ok arguments afterArguments ∧
      finishNamedType name arguments afterArguments = .ok value output := by
  constructor
  · intro result
    unfold parseNamedType at result
    rcases named_bind_ok_parts result with ⟨name, afterName, nameResult, rest⟩
    rcases named_bind_ok_parts rest with ⟨arguments, afterArguments, argumentsResult, finished⟩
    exact ⟨name, afterName, arguments, afterArguments, nameResult, argumentsResult, finished⟩
  · rintro ⟨name, afterName, arguments, afterArguments, nameResult, argumentsResult, finished⟩
    simpa only [parseNamedType, bind, nameResult, argumentsResult] using finished

theorem parseNamedType_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessSound (parseNamedType nested) (DeclarativeGrammar.NamedTypeTraceParses elementTrace) := by
  intro input output value result
  rcases parseNamedType_success_iff_components.mp result with
    ⟨name, afterName, arguments, afterArguments, nameResult, argumentsResult, finishedResult⟩
  rcases qualifiedName_trace_success_sound .typeExpr .typeExpr nameResult with ⟨nameEvents, nameParsed, nameEq⟩
  have nameFrame := qualifiedName_success_context .typeExpr .typeExpr nameResult
  rcases parseNamedTypeArguments_trace_success_sound successSound contextFrame argumentsResult with
    ⟨argumentEvents, argumentsParsed, argumentsEq⟩
  rcases finishNamedType_success_trace_sound name arguments finishedResult with
    ⟨finishingEvents, finished, valueEq, stateEq⟩
  refine ⟨nameEvents ++ argumentEvents ++ finishingEvents, ?_, ?_⟩
  · rw [valueEq, stateEq]
    exact .parsed nameParsed (by simpa only [nameFrame.1, nameFrame.2, State.declarativeRemainder]
      using argumentsParsed) finished
  · rw [stateEq]
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]
    change afterArguments.diagnostics ++ finishingEvents = input.diagnostics ++ _
    rw [argumentsEq, nameEq]
    simp only [List.append_assoc]

theorem parseNamedType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessComplete (parseNamedType nested) (DeclarativeGrammar.NamedTypeTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed nameParsed argumentsParsed finished =>
      rename_i afterName name arguments nameEvents argumentEvents finishingEvents
      rcases qualifiedName_trace_success_complete .typeExpr .typeExpr nameParsed with
        ⟨next, nameResult, afterEq, nameEq⟩
      have frame := qualifiedName_success_context .typeExpr .typeExpr nameResult
      have argumentsAtNext : DeclarativeGrammar.NamedTypeArgumentsTraceParses elementTrace
          next.file.id next.window.endByte next.declarativeRemainder arguments after argumentEvents := by
        simpa only [frame.1, frame.2, afterEq] using argumentsParsed
      rcases parseNamedTypeArguments_trace_success_complete successComplete contextFrame argumentsAtNext with
        ⟨afterArguments, argumentsResult, finalEq, argumentsEq⟩
      rcases (finishNamedType_trace_success_iff name arguments (input := afterArguments)).mp finished with
        ⟨output, finishedResult, outputEq, eventsEq⟩
      refine ⟨output, parseNamedType_success_iff_components.mpr
        ⟨name, next, arguments, afterArguments, nameResult, argumentsResult, finishedResult⟩,
        outputEq.trans finalEq, ?_⟩
      rw [eventsEq, argumentsEq, nameEq]
      simp only [List.append_assoc]

theorem parseNamedType_success_context
    (contextFrame : ParserSuccessContext nested) : ParserSuccessContext (parseNamedType nested) := by
  intro input output value result
  rcases parseNamedType_success_iff_components.mp result with
    ⟨name, afterName, arguments, afterArguments, nameResult, argumentsResult, finishedResult⟩
  have first := qualifiedName_success_context .typeExpr .typeExpr nameResult
  have middle := parseNamedTypeArguments_success_context contextFrame argumentsResult
  have last := finishNamedType_success_context name arguments finishedResult
  exact ⟨last.1.trans (middle.1.trans first.1), last.2.trans (middle.2.trans first.2)⟩

theorem parseNamedType_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {value : TypeExpr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parseNamedType nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseNamedType_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parseNamedType_trace_success_sound successSound contextFrame result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SourceFrameProperties
/-! Source-file preservation for all ordinary replies, independently of input
validity, diagnostic events, and token/window preservation. Invariants carry
no state and therefore impose no source obligation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace Reply

def PreservesFile {α : Type} (reply : Reply α) (input : State) : Prop :=
  match reply with
  | .ok _ next | .reject _ next => next.file = input.file
  | .invariant _ => True

theorem PreservesFile.trans {α : Type} {reply : Reply α} {middle input : State}
    (preserved : reply.PreservesFile middle) (fileEq : middle.file = input.file) :
    reply.PreservesFile input := by
  cases reply with
  | ok value next => exact Eq.trans preserved fileEq
  | reject failure next => exact Eq.trans preserved fileEq
  | invariant error => trivial

end Reply

namespace Parser

def PreservesFile {α : Type} (parser : Parser α) : Prop :=
  ∀ input, (parser input).PreservesFile input

theorem PreservesFile.file_eq_of_ok {α : Type} {parser : Parser α}
    (preserved : PreservesFile parser) {input output : State} {value : α}
    (result : parser input = .ok value output) : output.file = input.file := by
  have frame := preserved input
  rwa [result] at frame

theorem PreservesFile.file_eq_of_reject {α : Type} {parser : Parser α}
    (preserved : PreservesFile parser) {input rejected : State} {failure : Failure}
    (result : parser input = .reject failure rejected) : rejected.file = input.file := by
  have frame := preserved input
  rwa [result] at frame

theorem pure_preservesFile {α : Type} (value : α) : PreservesFile (pure value : Parser α) :=
  fun _ => rfl

theorem bind_preservesFile {α β : Type} {first : Parser α} {next : α → Parser β}
    (firstFile : PreservesFile first) (nextFile : ∀ value, PreservesFile (next value)) :
    PreservesFile (first >>= next) := by
  intro input
  change (match first input with
    | .ok value middle => next value middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error).PreservesFile input
  cases firstResult : first input with
  | ok value middle =>
      exact (nextFile value middle).trans (firstFile.file_eq_of_ok firstResult)
  | reject failure rejected => exact firstFile.file_eq_of_reject firstResult
  | invariant error => trivial

end Parser

theorem getState_preservesFile : Parser.PreservesFile getState := fun _ => rfl

theorem modifyState_preservesFile (update : State → State)
    (fileEq : ∀ input, (update input).file = input.file) :
    Parser.PreservesFile (modifyState update) := fileEq

theorem emitDiagnostic_preservesFile (diagnostic : ParseDiagnostic) :
    Parser.PreservesFile (emitDiagnostic diagnostic) := fun _ => rfl

theorem rejectAt_preservesFile {α : Type} (input : State)
    (expected : NonemptyList ParseExpectation) (context : ParseContext) :
    (rejectAt (α := α) input expected context).PreservesFile input := rfl

theorem acceptToken_preservesFile (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) : Parser.PreservesFile (acceptToken expected context accepts) := by
  intro input
  unfold acceptToken
  cases input.peek? with
  | none => rfl
  | some token => simp only; split <;> rfl

theorem keyword_preservesFile (value : HardKeyword) (context : ParseContext) :
    Parser.PreservesFile (keyword value context) :=
  acceptToken_preservesFile (.keyword value) context (· == .keyword value)

theorem symbol_preservesFile (value : Symbol) (context : ParseContext) :
    Parser.PreservesFile (symbol value context) :=
  acceptToken_preservesFile (.symbol value) context (· == .symbol value)

theorem contextual_preservesFile (value : ContextualKeyword) (context : ParseContext) :
    Parser.PreservesFile (contextual value context) :=
  acceptToken_preservesFile (.contextual value) context (·.isContextual value)

theorem rawIdentifier_preservesFile (context : ParseContext) :
    Parser.PreservesFile (rawIdentifier context) := by
  intro input
  unfold rawIdentifier
  cases input.peek? with
  | none => rfl
  | some token => cases token with
    | mk span kind => cases kind <;> rfl

theorem identifier_preservesFile (context : ParseContext) :
    Parser.PreservesFile (identifier context) := by
  intro input
  cases result : identifier context input with
  | ok name output => exact (identifier_success_context_eq context result).1
  | reject failure rejected => rw [identifier_reject_state_eq context result]; rfl
  | invariant error => trivial

theorem qualifiedName_preservesFile (context : ParseContext) (phase : ParserPhase) :
    Parser.PreservesFile (qualifiedName context phase) := by
  intro input
  cases result : qualifiedName context phase input with
  | ok name output => exact (qualifiedName_success_context context phase result).1
  | reject failure rejected => exact (qualifiedName_reject_context context phase result).1
  | invariant error => trivial

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedSourceFrameProperties
/-! Every ordinary delimiter outcome retains its input file when its child
does. No token/window, progress, adequacy, or validity assumption is needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem closeDelimited_preservesFile {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext) (elementsRev : List α) :
    Parser.PreservesFile (closeDelimited opening closing context elementsRev) := by
  intro input
  unfold closeDelimited
  cases result : symbol closing context input with
  | ok token next => exact (symbol_preservesFile closing context).file_eq_of_ok result
  | reject failure rejected => exact (symbol_preservesFile closing context).file_eq_of_reject result
  | invariant error => trivial

theorem afterDelimitedElement_preservesFile {α : Type}
    (element : Parser α) (childFile : Parser.PreservesFile element)
    (closing : Symbol) (allowTrailing : Bool) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev,
      Parser.PreservesFile (afterDelimitedElement element closing allowTrailing context phase opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input; trivial
  | succ fuel ih =>
      intro elementsRev input
      unfold afterDelimitedElement
      split
      · cases commaResult : symbol .comma context input with
        | invariant error => trivial
        | reject failure rejected => exact (symbol_preservesFile .comma context).file_eq_of_reject commaResult
        | ok comma afterComma =>
            have commaFile := (symbol_preservesFile .comma context).file_eq_of_ok commaResult
            simp only
            split
            · exact (closeDelimited_preservesFile opening closing context elementsRev afterComma).trans commaFile
            · cases elementResult : element afterComma with
              | invariant error => trivial
              | reject failure rejected => exact Eq.trans (childFile.file_eq_of_reject elementResult) commaFile
              | ok value next =>
                  simp only
                  split
                  · exact (ih (value :: elementsRev) next).trans
                      (Eq.trans (childFile.file_eq_of_ok elementResult) commaFile)
                  · trivial
      · split
        · exact closeDelimited_preservesFile opening closing context elementsRev input
        · exact rejectAt_preservesFile input _ context

theorem delimitedWithPolicy_preservesFile {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) (childFile : Parser.PreservesFile element) :
    Parser.PreservesFile (delimitedWithPolicy opening closing allowEmpty allowTrailing element context phase) := by
  intro input
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | invariant error => trivial
  | reject failure rejected => exact (symbol_preservesFile opening context).file_eq_of_reject openingResult
  | ok openingToken afterOpening =>
      have openingFile := (symbol_preservesFile opening context).file_eq_of_ok openingResult
      simp only
      split
      · exact (closeDelimited_preservesFile openingToken closing context [] afterOpening).trans openingFile
      · cases elementResult : element afterOpening with
        | invariant error => trivial
        | reject failure rejected => exact Eq.trans (childFile.file_eq_of_reject elementResult) openingFile
        | ok value next =>
            simp only
            split
            · exact (afterDelimitedElement_preservesFile element childFile closing allowTrailing context phase
                openingToken (afterOpening.remainingCount + 1) [value] next).trans
                (Eq.trans (childFile.file_eq_of_ok elementResult) openingFile)
            · trivial

theorem delimited_preservesFile {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) (childFile : Parser.PreservesFile element) :
    Parser.PreservesFile (delimited opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_preservesFile opening closing allowEmpty true element context phase childFile

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TupleTypeRejectionTraceProperties
/-! Raw tuple failure is the exact failure of its trailing-enabled list. Mapping
the successful AST never commits a report or changes the rejected state. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {typeTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseTupleType_reject_iff_list {input rejected : State} {failure : Failure} :
    parseTupleType nested input = .reject failure rejected ↔
    delimited .leftParen .rightParen true nested .typeExpr .typeExpr input =
      .reject failure rejected := by
  cases result : delimited .leftParen .rightParen true nested .typeExpr .typeExpr input <;>
    simp [parseTupleType, bind, pure, result]

theorem parseTupleType_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested typeTrace)
    (rejectSound : ParserTraceRejectSound nested typeRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseTupleType nested)
      (DeclarativeGrammar.TupleTypeTraceRejects typeTrace typeRejects) := by
  intro input rejected failure result
  exact delimited_reject_trace_sound successSound rejectSound contextFrame
    .leftParen .rightParen true .typeExpr .typeExpr (parseTupleType_reject_iff_list.mp result)

theorem parseTupleType_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested typeTrace)
    (rejectComplete : ParserTraceRejectComplete nested typeRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseTupleType nested)
      (DeclarativeGrammar.TupleTypeTraceRejects typeTrace typeRejects) := by
  intro input after report trace rejection
  rcases delimited_trace_reject_complete successComplete rejectComplete contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr rejection with
    ⟨failure, rejected, result, afterEq, reportEq, events⟩
  exact ⟨failure, rejected, parseTupleType_reject_iff_list.mpr result, afterEq, reportEq, events⟩

theorem parseTupleType_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested typeTrace)
    (rejectSound : ParserTraceRejectSound nested typeRejects)
    (successComplete : ParserTraceSuccessComplete nested typeTrace)
    (rejectComplete : ParserTraceRejectComplete nested typeRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TupleTypeTraceRejects typeTrace typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parseTupleType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  simpa only [parseTupleType_reject_iff_list] using
    delimited_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr

theorem parseTupleType_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested typeTrace)
    (rejectSound : ParserTraceRejectSound nested typeRejects)
    (successComplete : ParserTraceSuccessComplete nested typeTrace)
    (rejectComplete : ParserTraceRejectComplete nested typeRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TupleTypeTraceRejects typeTrace typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseTupleType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  simpa only [parseTupleType_reject_iff_list] using
    delimited_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TupleTypeSuccessTraceProperties
/-! Actual tuple types preserve the full list span and every ordered child event.
Empty and singleton lists remain tuple types. Only nested success contracts and
the successful source/full-window frame are needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {typeTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem parseTupleType_success_iff_list {input output : State} {value : TypeExpr} :
    parseTupleType nested input = .ok value output ↔
    ∃ values, delimited .leftParen .rightParen true nested .typeExpr .typeExpr input =
      .ok values output ∧ value = DeclarativeGrammar.tupleTypeTraceValue values := by
  constructor
  · intro result
    cases listResult : delimited .leftParen .rightParen true nested .typeExpr .typeExpr input with
    | reject => simp [parseTupleType, bind, listResult] at result
    | invariant => simp [parseTupleType, bind, listResult] at result
    | ok values next =>
        simp only [parseTupleType, bind, listResult, pure] at result
        cases result
        exact ⟨values, rfl, rfl⟩
  · rintro ⟨values, result, rfl⟩
    simp only [parseTupleType, bind, result, pure, DeclarativeGrammar.tupleTypeTraceValue]

theorem parseTupleType_trace_success_sound
    (successSound : ParserTraceSuccessSound nested typeTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessSound (parseTupleType nested)
      (DeclarativeGrammar.TupleTypeTraceParses typeTrace) := by
  intro input output value result
  rcases parseTupleType_success_iff_list.mp result with ⟨values, listResult, rfl⟩
  rcases delimited_trace_success_sound successSound contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr listResult with ⟨trace, parsed, events⟩
  exact ⟨trace, .parsed parsed, events⟩

theorem parseTupleType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested typeTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessComplete (parseTupleType nested)
      (DeclarativeGrammar.TupleTypeTraceParses typeTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed elements =>
      rcases delimited_trace_success_complete successComplete contextFrame
          .leftParen .rightParen true .typeExpr .typeExpr elements with
        ⟨output, result, afterEq, events⟩
      exact ⟨output, parseTupleType_success_iff_list.mpr ⟨_, result, rfl⟩, afterEq, events⟩

theorem parseTupleType_success_context (contextFrame : ParserSuccessContext nested) :
    ParserSuccessContext (parseTupleType nested) := by
  intro input output value result
  rcases parseTupleType_success_iff_list.mp result with ⟨values, listResult, _⟩
  exact delimited_success_context contextFrame .leftParen .rightParen true
    .typeExpr .typeExpr listResult

theorem parseTupleType_trace_success_iff
    (successSound : ParserTraceSuccessSound nested typeTrace)
    (successComplete : ParserTraceSuccessComplete nested typeTrace)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {value : TypeExpr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TupleTypeTraceParses typeTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parseTupleType nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseTupleType_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, events⟩
    rcases parseTupleType_trace_success_sound successSound contextFrame result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeDispatchSelectionTraceProperties
/-! Executable lookahead selects exactly one independent branch on every
state. These proof-side projections do not change the recursive parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

namespace TypeDispatchTraceInternals

def selectedBranch (input : State) : TypeDispatchBranch :=
  if isKeyword input .functionKw then .function
  else if isContextual input .comptime && (input.peekOffsetKind? 1 == some (.symbol .less)) then .comptime
  else if isContextual input .mapping && (input.peekOffsetKind? 1 == some (.symbol .leftParen)) then .mapping
  else if isSymbol input .at then .proxy
  else if isSymbol input .leftParen then .tuple
  else if isIdentifier input then .named
  else .final

def rawParser (nested : Parser TypeExpr) (branch : TypeDispatchBranch) : Parser TypeExpr :=
  match branch with
  | .function => parseFunctionType nested
  | .comptime => parseComptimeType nested
  | .mapping => parseMappingType nested
  | .proxy => parseProxyType nested
  | .tuple => parseTupleType nested
  | .named => parseNamedType nested
  | .final => fun input => rejectAt input { head := .typeExpr, tail := [] } .typeExpr

private theorem pair_present_of_guard {input : State}
    (word : ContextualKeyword) (symbolValue : Symbol)
    (guard : (isContextual input word && (input.peekOffsetKind? 1 == some (.symbol symbolValue))) = true) :
    TypeDispatchPairPresent input.declarativeRemainder word symbolValue := by
  rcases Bool.and_eq_true_iff.mp guard with ⟨wordPresent, symbolPresent⟩
  rcases contextual_eq_ok_of_isContextual_eq_true word .typeExpr wordPresent with ⟨marker, markerResult⟩
  have advanced := isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true symbolValue symbolPresent
  rcases symbol_eq_ok_of_isSymbol_eq_true symbolValue .typeExpr advanced with ⟨opening, openingResult⟩
  exact ⟨marker.span, opening.span,
    (contextual_success_exactTokenParses word .typeExpr markerResult).1,
    (symbol_success_exactTokenParses symbolValue .typeExpr openingResult).1⟩

theorem selectedBranch_selects (input : State) :
    TypeDispatchSelects input.declarativeRemainder (selectedBranch input) := by
  unfold selectedBranch
  split
  next present =>
    rcases keyword_eq_ok_of_isKeyword_eq_true .functionKw .typeExpr present with ⟨marker, result⟩
    exact .function ⟨marker.span, (keyword_success_exactTokenParses .functionKw .typeExpr result).1⟩
  next absent =>
    have functionAbsent := keywordAbsentAt_of_isKeyword_eq_false .functionKw (Bool.eq_false_iff.mpr absent)
    split
    next present => exact .comptime functionAbsent (pair_present_of_guard .comptime .less present)
    next absent =>
      have comptimeAbsent := contextualSymbolPairAbsentAt_of_guard_eq_false .comptime .less
        (Bool.eq_false_iff.mpr absent)
      split
      next present => exact .mapping functionAbsent comptimeAbsent (pair_present_of_guard .mapping .leftParen present)
      next absent =>
        have mappingAbsent := contextualSymbolPairAbsentAt_of_guard_eq_false .mapping .leftParen
          (Bool.eq_false_iff.mpr absent)
        split
        next present =>
          rcases symbol_eq_ok_of_isSymbol_eq_true .at .typeExpr present with ⟨marker, result⟩
          exact .proxy functionAbsent comptimeAbsent mappingAbsent
            ⟨marker.span, (symbol_success_exactTokenParses .at .typeExpr result).1⟩
        next absent =>
          have atAbsent := symbolAbsentAt_of_isSymbol_eq_false .at (Bool.eq_false_iff.mpr absent)
          split
          next present =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeExpr present with ⟨marker, result⟩
            exact .tuple functionAbsent comptimeAbsent mappingAbsent atAbsent
              ⟨marker.span, (symbol_success_exactTokenParses .leftParen .typeExpr result).1⟩
          next absent =>
            have leftParenAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftParen (Bool.eq_false_iff.mpr absent)
            split
            next present =>
              exact .named functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent
                (identifierPresentAt_of_isIdentifier_eq_true present)
            next absent =>
              exact .final functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent
                (identifierAbsentAt_of_isIdentifier_eq_false (Bool.eq_false_iff.mpr absent))

theorem selectedBranch_eq_iff {input : State} {branch : TypeDispatchBranch} :
    selectedBranch input = branch ↔ TypeDispatchSelects input.declarativeRemainder branch := by
  constructor
  · intro same; rw [← same]; exact selectedBranch_selects input
  · exact (selectedBranch_selects input).branch_unique

theorem typeExprWithFuel_eq_selected_raw (fuel : Nat) (input : State) :
    typeExprWithFuel (fuel + 1) input = rawParser (typeExprWithFuel fuel) (selectedBranch input) input := by
  change (if isKeyword input .functionKw then parseFunctionType (typeExprWithFuel fuel) input
    else if isContextual input .comptime && (input.peekOffsetKind? 1 == some (.symbol .less)) then
      parseComptimeType (typeExprWithFuel fuel) input
    else if isContextual input .mapping && (input.peekOffsetKind? 1 == some (.symbol .leftParen)) then
      parseMappingType (typeExprWithFuel fuel) input
    else if isSymbol input .at then parseProxyType (typeExprWithFuel fuel) input
    else if isSymbol input .leftParen then parseTupleType (typeExprWithFuel fuel) input
    else if isIdentifier input then parseNamedType (typeExprWithFuel fuel) input
    else rejectAt input { head := .typeExpr, tail := [] } .typeExpr) = _
  simp only [selectedBranch]
  repeat' first | split | rfl

end TypeDispatchTraceInternals

theorem typeExprWithFuel_eq_raw_of_selection (fuel : Nat) {input : State} {branch : TypeDispatchBranch}
    (selection : TypeDispatchSelects input.declarativeRemainder branch) :
    typeExprWithFuel (fuel + 1) input = TypeDispatchTraceInternals.rawParser (typeExprWithFuel fuel) branch input := by
  rw [TypeDispatchTraceInternals.typeExprWithFuel_eq_selected_raw,
    TypeDispatchTraceInternals.selectedBranch_eq_iff.mpr selection]

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeFunctionUnrestrictedFuelTotalityProperties
/-! Function, optional-return, and tuple parsing have ordinary outcomes on
arbitrary states under the recursive element bound. Successful child end-index
preservation suffices; no token carrier, source, or rejected-state frame is
required, and no global state-validity hypothesis is used. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeFunctionInternals

theorem parseFunctionReturns_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ returns next, parseFunctionReturns nested input = .ok returns next) ∨
      (∃ failure next, parseFunctionReturns nested input = .reject failure next) := by
  by_cases present : isContextual input .returns
  · rcases (contextual_ordinary .returns .typeExpr) input with
      ⟨marker, afterMarker, markerResult⟩ | ⟨failure, rejected, markerResult⟩
    · have afterMarkerAdequate : afterMarker.remainingCount < elementFuel :=
        contextual_remainingCount_lt_of_success .returns .typeExpr markerResult adequate
      rcases delimited_ordinary_of_unrestrictedElementFuel .leftParen .rightParen true
          nested .typeExpr .typeExpr elementFuel contract afterMarker (by omega) with
        ⟨values, final, valuesResult⟩ | ⟨failure, rejected, valuesResult⟩
      · exact Or.inl ⟨some values, final, by
          simp only [parseFunctionReturns, getState, bind, present,
            ↓reduceIte, markerResult, valuesResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseFunctionReturns, getState, bind, present,
            ↓reduceIte, markerResult, valuesResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseFunctionReturns, getState, bind, present, ↓reduceIte, markerResult]⟩
  · have absent : isContextual input .returns = false := Bool.eq_false_iff.mpr present
    exact Or.inl ⟨none, input, by
      simp only [parseFunctionReturns, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem parseFunctionReturns_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) : parseFunctionReturns nested input ≠ .invariant error := by
  intro failed
  rcases parseFunctionReturns_ordinary_of_unrestrictedElementFuel nested elementFuel contract input adequate with
    ⟨returns, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end TypeFunctionInternals

theorem parseFunctionType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseFunctionType nested input = .ok value next) ∨
      (∃ failure next, parseFunctionType nested input = .reject failure next) := by
  rcases (keyword_ordinary .functionKw .typeExpr) input with
    ⟨functionKeyword, afterKeyword, keywordResult⟩ | ⟨failure, rejected, keywordResult⟩
  · have afterKeywordAdequate : afterKeyword.remainingCount < elementFuel :=
      keyword_remainingCount_lt_of_success .functionKw .typeExpr keywordResult adequate
    rcases delimited_ordinary_of_unrestrictedElementFuel .leftParen .rightParen true nested
        .typeExpr .typeExpr elementFuel contract afterKeyword (by omega) with
      ⟨parameters, afterParameters, parametersResult⟩ | ⟨failure, rejected, parametersResult⟩
    · have parametersEndIndex := delimited_endIndex_onSuccess contract.endIndexOnSuccess
        .leftParen .rightParen true .typeExpr .typeExpr parametersResult
      have parametersMonotone := delimited_cursorMonotoneOnSuccess
        .leftParen .rightParen true nested .typeExpr .typeExpr
        afterKeyword parameters afterParameters parametersResult
      have afterParametersAdequate : afterParameters.remainingCount < elementFuel :=
        remainingCount_lt_of_endIndex_eq parametersEndIndex parametersMonotone afterKeywordAdequate
      rcases TypeFunctionInternals.parseFunctionReturns_ordinary_of_unrestrictedElementFuel
          nested elementFuel contract afterParameters (by omega) with
        ⟨returns, final, returnsResult⟩ | ⟨failure, rejected, returnsResult⟩
      · let endSpan := match returns with
          | some values => values.span
          | none => parameters.span
        exact Or.inl ⟨{
            span := SourceSpan.cover functionKeyword.span endSpan
            value := .function functionKeyword.span parameters returns
          }, final, by
            simp only [parseFunctionType, bind, keywordResult, parametersResult, returnsResult, pure]
            rfl⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseFunctionType, bind, keywordResult, parametersResult, returnsResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseFunctionType, bind, keywordResult, parametersResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseFunctionType, bind, keywordResult]⟩

theorem parseFunctionType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) : parseFunctionType nested input ≠ .invariant error := by
  intro failed
  rcases parseFunctionType_ordinary_of_unrestrictedElementFuel nested elementFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem parseTupleType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseTupleType nested input = .ok value next) ∨
      (∃ failure next, parseTupleType nested input = .reject failure next) := by
  rcases delimited_ordinary_of_unrestrictedElementFuel .leftParen .rightParen true nested
      .typeExpr .typeExpr elementFuel contract input adequate with
    ⟨tuple, next, tupleResult⟩ | ⟨failure, rejected, tupleResult⟩
  · exact Or.inl ⟨{ span := tuple.span, value := .tuple tuple.elements }, next, by
      simp only [parseTupleType, tupleResult, bind, pure]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseTupleType, tupleResult, bind]⟩

theorem parseTupleType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) : parseTupleType nested input ≠ .invariant error := by
  intro failed
  rcases parseTupleType_ordinary_of_unrestrictedElementFuel nested elementFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeNamedUnrestrictedFuelTotalityProperties
/-! Adequate-fuel named types have ordinary outcomes on arbitrary states.
Optional absence is a silent success, nonempty arguments are structural, and
the qualified-name cursor bound is transported without input validity. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem parseNamedTypeArguments_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ arguments next, parseNamedTypeArguments nested input = .ok arguments next) ∨
      (∃ failure next, parseNamedTypeArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .less
  · rcases delimited_ordinary_of_unrestrictedElementFuel .less .greater false nested
        .typeExpr .typeExpr elementFuel contract input adequate with
      ⟨parsed, afterDelimited, parsedResult⟩ | ⟨failure, rejected, parsedResult⟩
    · rcases requireNonempty_ok_of_delimited_false_ok .less .greater nested
          .typeExpr .typeExpr parsedResult with ⟨nonempty, nonemptyResult⟩
      exact Or.inl ⟨some nonempty, afterDelimited, by
        simp only [parseNamedTypeArguments, getState, bind, present,
          ↓reduceIte, parsedResult, nonemptyResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedTypeArguments, getState, bind, present, ↓reduceIte, parsedResult]⟩
  · have absent : isSymbol input .less = false := Bool.eq_false_iff.mpr present
    exact Or.inl ⟨none, input, by
      simp only [parseNamedTypeArguments, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem parseNamedTypeArguments_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) : parseNamedTypeArguments nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedTypeArguments_ordinary_of_unrestrictedElementFuel nested elementFuel contract input adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem parseNamedType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseNamedType nested input = .ok value next) ∨
      (∃ failure next, parseNamedType nested input = .reject failure next) := by
  rcases (qualifiedName_ordinary .typeExpr .typeExpr) input with
    ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
  · have nameWindow := qualifiedName_preservesTokenWindow .typeExpr .typeExpr input
    rw [nameResult] at nameWindow
    have afterNameAdequate : afterName.remainingCount < elementFuel + 1 :=
      remainingCount_lt_of_endIndex_eq (congrArg TokenWindow.endIndex nameWindow.2)
        (Nat.le_of_lt (qualifiedName_cursor_lt_onSuccess .typeExpr .typeExpr nameResult)) adequate
    rcases parseNamedTypeArguments_ordinary_of_unrestrictedElementFuel nested elementFuel
        contract afterName afterNameAdequate with
      ⟨arguments, afterArguments, argumentsResult⟩ | ⟨failure, rejected, argumentsResult⟩
    · rcases finishNamedType_ordinary name arguments afterArguments with
        ⟨value, final, finished⟩ | ⟨failure, rejected, finished⟩
      · exact Or.inl ⟨value, final, by
          simp only [parseNamedType, bind, nameResult, argumentsResult, finished]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseNamedType, bind, nameResult, argumentsResult, finished]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedType, bind, nameResult, argumentsResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseNamedType, bind, nameResult]⟩

theorem parseNamedType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) : parseNamedType nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedType_ordinary_of_unrestrictedElementFuel nested elementFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeSimpleUnrestrictedFuelTotalityProperties
/-! Raw proxy, comptime, and mapping types have ordinary outcomes on arbitrary
states when a real prefix token pays for the nested fuel. No source, token,
diagnostic, or validity invariant is needed. Successful child end-index and
cursor laws only propagate the bound between mapping's two nested calls. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem parseProxyType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseProxyType nested input = .ok value next) ∨
    (∃ failure next, parseProxyType nested input = .reject failure next) := by
  rcases symbol_ordinary .at .typeExpr input with
    ⟨marker, afterMarker, markerResult⟩ | ⟨failure, rejected, markerResult⟩
  · have afterMarkerAdequate : afterMarker.remainingCount < elementFuel :=
      symbol_remainingCount_lt_of_success .at .typeExpr markerResult adequate
    rcases contract.ordinary afterMarker afterMarkerAdequate with
      ⟨inner, final, innerResult⟩ | ⟨failure, rejected, innerResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover marker.span inner.span
          value := .proxy marker.span inner
        }, final, by simp only [parseProxyType, markerResult, innerResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseProxyType, markerResult, innerResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseProxyType, markerResult]⟩

theorem parseProxyType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseProxyType nested input ≠ .invariant error := by
  intro failed
  rcases parseProxyType_ordinary_of_unrestrictedElementFuel nested elementFuel contract
      input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem parseComptimeType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseComptimeType nested input = .ok value next) ∨
    (∃ failure next, parseComptimeType nested input = .reject failure next) := by
  rcases contextual_ordinary .comptime .typeExpr input with
    ⟨marker, afterMarker, markerResult⟩ | ⟨failure, rejected, markerResult⟩
  · have afterMarkerAdequate : afterMarker.remainingCount < elementFuel :=
      contextual_remainingCount_lt_of_success .comptime .typeExpr markerResult adequate
    rcases symbol_ordinary .less .typeExpr afterMarker with
      ⟨opening, afterOpening, openingResult⟩ | ⟨failure, rejected, openingResult⟩
    · have afterOpeningAdequate : afterOpening.remainingCount < elementFuel :=
        symbol_remainingCount_lt_of_success .less .typeExpr openingResult
          (Nat.lt_succ_of_lt afterMarkerAdequate)
      rcases contract.ordinary afterOpening afterOpeningAdequate with
        ⟨inner, afterInner, innerResult⟩ | ⟨failure, rejected, innerResult⟩
      · rcases symbol_ordinary .greater .typeExpr afterInner with
          ⟨closing, final, closingResult⟩ | ⟨failure, rejected, closingResult⟩
        · exact Or.inl ⟨{
              span := SourceSpan.cover marker.span closing.span
              value := .comptime marker.span
                (SourceSpan.cover opening.span closing.span) inner
            }, final, by
            simp only [parseComptimeType, bind, markerResult, openingResult,
              innerResult, closingResult, pure]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [parseComptimeType, bind, markerResult, openingResult,
              innerResult, closingResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseComptimeType, bind, markerResult, openingResult, innerResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseComptimeType, bind, markerResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseComptimeType, bind, markerResult]⟩

theorem parseComptimeType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseComptimeType nested input ≠ .invariant error := by
  intro failed
  rcases parseComptimeType_ordinary_of_unrestrictedElementFuel nested elementFuel contract
      input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem parseMappingType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseMappingType nested input = .ok value next) ∨
    (∃ failure next, parseMappingType nested input = .reject failure next) := by
  rcases contextual_ordinary .mapping .typeExpr input with
    ⟨mapping, afterMapping, mappingResult⟩ | ⟨failure, rejected, mappingResult⟩
  · have afterMappingAdequate : afterMapping.remainingCount < elementFuel :=
      contextual_remainingCount_lt_of_success .mapping .typeExpr mappingResult adequate
    rcases symbol_ordinary .leftParen .typeExpr afterMapping with
      ⟨opening, afterOpening, openingResult⟩ | ⟨failure, rejected, openingResult⟩
    · have afterOpeningAdequate : afterOpening.remainingCount < elementFuel :=
        symbol_remainingCount_lt_of_success .leftParen .typeExpr openingResult
          (Nat.lt_succ_of_lt afterMappingAdequate)
      rcases contract.ordinary afterOpening afterOpeningAdequate with
        ⟨key, afterKey, keyResult⟩ | ⟨failure, rejected, keyResult⟩
      · have afterKeyAdequate : afterKey.remainingCount < elementFuel :=
          contract.remainingCount_lt_of_success keyResult afterOpeningAdequate
        rcases symbol_ordinary .fatArrow .typeExpr afterKey with
          ⟨arrow, afterArrow, arrowResult⟩ | ⟨failure, rejected, arrowResult⟩
        · have afterArrowAdequate : afterArrow.remainingCount < elementFuel :=
            symbol_remainingCount_lt_of_success .fatArrow .typeExpr arrowResult
              (Nat.lt_succ_of_lt afterKeyAdequate)
          rcases contract.ordinary afterArrow afterArrowAdequate with
            ⟨mapped, afterValue, valueResult⟩ | ⟨failure, rejected, valueResult⟩
          · rcases symbol_ordinary .rightParen .typeExpr afterValue with
              ⟨closing, final, closingResult⟩ | ⟨failure, rejected, closingResult⟩
            · exact Or.inl ⟨{
                  span := SourceSpan.cover mapping.span closing.span
                  value := .mapping mapping.span
                    (SourceSpan.cover opening.span closing.span) key mapped
                }, final, by
                simp only [parseMappingType, bind, mappingResult, openingResult,
                  keyResult, arrowResult, valueResult, closingResult, pure]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [parseMappingType, bind, mappingResult, openingResult,
                  keyResult, arrowResult, valueResult, closingResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [parseMappingType, bind, mappingResult, openingResult,
                keyResult, arrowResult, valueResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [parseMappingType, bind, mappingResult, openingResult, keyResult, arrowResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseMappingType, bind, mappingResult, openingResult, keyResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseMappingType, bind, mappingResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseMappingType, bind, mappingResult]⟩

theorem parseMappingType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseMappingType nested input ≠ .invariant error := by
  intro failed
  rcases parseMappingType_ordinary_of_unrestrictedElementFuel nested elementFuel contract
      input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeSourceFrameProperties
/-! Every ordinary recursive-type reply retains the complete input source
file, including rejection after successful children. Raw forms require only
that child source law. No validity, progress, token, window, diagnostic, or
ordinary-outcome premise is used; invariant replies carry no returned state. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem requireNonempty_preservesFile {α : Type}
    (parsed : DelimitedList α) (phase : ParserPhase) :
    Parser.PreservesFile (requireNonempty parsed phase) := by
  intro input
  unfold requireNonempty
  cases parsed.elements with
  | nil => trivial
  | cons head tail => rfl

theorem parseNamedTypeArguments_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseNamedTypeArguments nested) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_preservesFile getState_preservesFile
  intro observed
  split
  · apply Parser.bind_preservesFile
      (delimited_preservesFile .less .greater false nested .typeExpr .typeExpr nestedFile)
    intro parsed
    apply Parser.bind_preservesFile (requireNonempty_preservesFile parsed .typeExpr)
    intro nonempty
    exact Parser.pure_preservesFile _
  · exact Parser.pure_preservesFile none

theorem finishNamedType_preservesFile (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    Parser.PreservesFile (finishNamedType name arguments) := by
  unfold finishNamedType
  split
  · apply Parser.bind_preservesFile (emitDiagnostic_preservesFile _)
    intro ignored
    exact Parser.pure_preservesFile _
  · exact Parser.pure_preservesFile _

theorem parseNamedType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseNamedType nested) := by
  unfold parseNamedType
  apply Parser.bind_preservesFile (qualifiedName_preservesFile .typeExpr .typeExpr)
  intro name
  apply Parser.bind_preservesFile (parseNamedTypeArguments_preservesFile nested nestedFile)
  intro arguments
  exact finishNamedType_preservesFile name arguments

theorem parseMappingType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseMappingType nested) := by
  unfold parseMappingType
  apply Parser.bind_preservesFile (contextual_preservesFile .mapping .typeExpr)
  intro marker
  apply Parser.bind_preservesFile (symbol_preservesFile .leftParen .typeExpr)
  intro opening
  apply Parser.bind_preservesFile nestedFile
  intro key
  apply Parser.bind_preservesFile (symbol_preservesFile .fatArrow .typeExpr)
  intro arrow
  apply Parser.bind_preservesFile nestedFile
  intro value
  apply Parser.bind_preservesFile (symbol_preservesFile .rightParen .typeExpr)
  intro closing
  exact Parser.pure_preservesFile _

theorem parseComptimeType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseComptimeType nested) := by
  unfold parseComptimeType
  apply Parser.bind_preservesFile (contextual_preservesFile .comptime .typeExpr)
  intro marker
  apply Parser.bind_preservesFile (symbol_preservesFile .less .typeExpr)
  intro opening
  apply Parser.bind_preservesFile nestedFile
  intro inner
  apply Parser.bind_preservesFile (symbol_preservesFile .greater .typeExpr)
  intro closing
  exact Parser.pure_preservesFile _

theorem parseProxyType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseProxyType nested) := by
  intro input
  unfold parseProxyType
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => trivial
  | reject failure rejected => exact (symbol_preservesFile .at .typeExpr).file_eq_of_reject markerResult
  | ok marker afterMarker =>
      have markerFile := (symbol_preservesFile .at .typeExpr).file_eq_of_ok markerResult
      simp only
      cases innerResult : nested afterMarker with
      | invariant error => trivial
      | ok inner output => exact Eq.trans (nestedFile.file_eq_of_ok innerResult) markerFile
      | reject failure rejected => exact Eq.trans (nestedFile.file_eq_of_reject innerResult) markerFile

theorem parseTupleType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseTupleType nested) := by
  unfold parseTupleType
  apply Parser.bind_preservesFile
    (delimited_preservesFile .leftParen .rightParen true nested .typeExpr .typeExpr nestedFile)
  intro tuple
  exact Parser.pure_preservesFile _

theorem TypeFunctionInternals.parseFunctionReturns_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (TypeFunctionInternals.parseFunctionReturns nested) := by
  unfold TypeFunctionInternals.parseFunctionReturns
  apply Parser.bind_preservesFile getState_preservesFile
  intro observed
  split
  · apply Parser.bind_preservesFile (contextual_preservesFile .returns .typeExpr)
    intro marker
    apply Parser.bind_preservesFile
      (delimited_preservesFile .leftParen .rightParen true nested .typeExpr .typeExpr nestedFile)
    intro values
    exact Parser.pure_preservesFile _
  · exact Parser.pure_preservesFile none

theorem parseFunctionType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseFunctionType nested) := by
  unfold parseFunctionType
  apply Parser.bind_preservesFile (keyword_preservesFile .functionKw .typeExpr)
  intro marker
  apply Parser.bind_preservesFile
    (delimited_preservesFile .leftParen .rightParen true nested .typeExpr .typeExpr nestedFile)
  intro parameters
  apply Parser.bind_preservesFile (TypeFunctionInternals.parseFunctionReturns_preservesFile nested nestedFile)
  intro returns
  exact Parser.pure_preservesFile _

theorem typeExprWithFuel_preservesFile (fuel : Nat) :
    Parser.PreservesFile (typeExprWithFuel fuel) := by
  induction fuel with
  | zero => intro input; trivial
  | succ fuel ih =>
      intro input
      simp only [typeExprWithFuel]
      split
      · exact parseFunctionType_preservesFile _ ih input
      · split
        · exact parseComptimeType_preservesFile _ ih input
        · split
          · exact parseMappingType_preservesFile _ ih input
          · split
            · exact parseProxyType_preservesFile _ ih input
            · split
              · exact parseTupleType_preservesFile _ ih input
              · split
                · exact parseNamedType_preservesFile _ ih input
                · exact rejectAt_preservesFile input _ .typeExpr

theorem typeExpr_preservesFile : Parser.PreservesFile typeExpr := by
  intro input
  exact typeExprWithFuel_preservesFile (input.remainingCount + 1) input

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeSuccessContextProperties
/-! Successful recursive types retain their source and complete active window
on every state, without a validity assumption. This frame alone is not a
recursive diagnostic-trace soundness or completeness theorem. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem typeExprWithFuel_success_context (fuel : Nat) :
    ParserSuccessContext (typeExprWithFuel fuel) := by
  induction fuel with
  | zero =>
      intro input output value result
      simp [typeExprWithFuel] at result
  | succ fuel ih =>
      intro input output value result
      simp only [typeExprWithFuel] at result
      split at result
      · exact parseFunctionType_success_context ih result
      · split at result
        · exact parseComptimeType_success_context ih result
        · split at result
          · exact parseMappingType_success_context ih result
          · split at result
            · exact parseProxyType_success_context ih result
            · split at result
              · exact parseTupleType_success_context ih result
              · split at result
                · exact parseNamedType_success_context ih result
                · simp [rejectAt] at result

theorem typeExpr_success_context : ParserSuccessContext typeExpr := by
  intro input output value result
  exact typeExprWithFuel_success_context (input.remainingCount + 1) result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeDispatchRejectionTraceProperties
/-! Exact rejection of one positive-fuel type-dispatch layer. Earlier guards
select a raw branch, or the final silent expected-typeExpr failure. Nested
success/rejection contracts are explicit, while the fixed child's frame is
unconditional; no general recursive production trace is asserted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar TypeDispatchTraceInternals

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

namespace TypeDispatchTraceInternals

theorem raw_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) (branch : TypeDispatchBranch) :
    ParserTraceRejectSound (rawParser nested branch) (TypeDispatchRawTraceRejects elementTrace elementRejects branch) := by
  cases branch with
  | function => exact parseFunctionType_reject_trace_sound successSound rejectSound contextFrame
  | comptime => exact parseComptimeType_reject_trace_sound successSound rejectSound contextFrame
  | mapping => exact parseMappingType_reject_trace_sound successSound rejectSound contextFrame
  | proxy => exact parseProxyType_reject_trace_sound rejectSound
  | tuple => exact parseTupleType_reject_trace_sound successSound rejectSound contextFrame
  | named => exact parseNamedType_reject_trace_sound successSound rejectSound contextFrame
  | final =>
      intro input rejected failure result
      have reported := rejectAt_reject_reports { head := .typeExpr, tail := [] } .typeExpr result
      have same : rejected = input := by
        unfold rawParser rejectAt at result
        cases result
        rfl
      subst rejected
      exact ⟨[], .rejected reported.1, by simp only [List.append_nil]⟩

theorem raw_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) (branch : TypeDispatchBranch) :
    ParserTraceRejectComplete (rawParser nested branch) (TypeDispatchRawTraceRejects elementTrace elementRejects branch) := by
  cases branch with
  | function => exact parseFunctionType_trace_reject_complete successComplete rejectComplete contextFrame
  | comptime => exact parseComptimeType_trace_reject_complete successComplete rejectComplete contextFrame
  | mapping => exact parseMappingType_trace_reject_complete successComplete rejectComplete contextFrame
  | proxy => exact parseProxyType_trace_reject_complete rejectComplete
  | tuple => exact parseTupleType_trace_reject_complete successComplete rejectComplete contextFrame
  | named => exact parseNamedType_trace_reject_complete successComplete rejectComplete contextFrame
  | final =>
      intro input after report trace rejection
      cases rejection with
      | rejected reported =>
          rcases (rejectAt_reports_iff (alpha := TypeExpr)).mp reported with ⟨failure, result, reportEq⟩
          exact ⟨failure, input, result, rfl, reportEq, by simp only [List.append_nil]⟩

end TypeDispatchTraceInternals

theorem typeExprWithFuel_dispatch_reject_trace_sound (fuel : Nat)
    (successSound : ParserTraceSuccessSound (typeExprWithFuel fuel) elementTrace)
    (rejectSound : ParserTraceRejectSound (typeExprWithFuel fuel) elementRejects) :
    ParserTraceRejectSound (typeExprWithFuel (fuel + 1)) (TypeDispatchTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  rw [typeExprWithFuel_eq_selected_raw] at result
  rcases raw_reject_trace_sound successSound rejectSound (typeExprWithFuel_success_context fuel)
      (selectedBranch input) result with
    ⟨trace, rejection, events⟩
  exact ⟨trace, .selected (selectedBranch input) (selectedBranch_selects input) rejection, events⟩

theorem typeExprWithFuel_dispatch_trace_reject_complete (fuel : Nat)
    (successComplete : ParserTraceSuccessComplete (typeExprWithFuel fuel) elementTrace)
    (rejectComplete : ParserTraceRejectComplete (typeExprWithFuel fuel) elementRejects) :
    ParserTraceRejectComplete (typeExprWithFuel (fuel + 1)) (TypeDispatchTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | selected branch selection raw =>
      rcases raw_trace_reject_complete successComplete rejectComplete (typeExprWithFuel_success_context fuel) branch raw with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, (typeExprWithFuel_eq_raw_of_selection fuel selection).trans result,
        afterEq, reportEq, events⟩

theorem typeExprWithFuel_dispatch_trace_reject_iff (fuel : Nat)
    (successSound : ParserTraceSuccessSound (typeExprWithFuel fuel) elementTrace)
    (rejectSound : ParserTraceRejectSound (typeExprWithFuel fuel) elementRejects)
    (successComplete : ParserTraceSuccessComplete (typeExprWithFuel fuel) elementTrace)
    (rejectComplete : ParserTraceRejectComplete (typeExprWithFuel fuel) elementRejects)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    TypeDispatchTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, typeExprWithFuel (fuel + 1) input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact typeExprWithFuel_dispatch_trace_reject_complete fuel successComplete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases typeExprWithFuel_dispatch_reject_trace_sound fuel successSound rejectSound result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem typeExprWithFuel_dispatch_trace_reject_failure_iff (fuel : Nat)
    (successSound : ParserTraceSuccessSound (typeExprWithFuel fuel) elementTrace)
    (rejectSound : ParserTraceRejectSound (typeExprWithFuel fuel) elementRejects)
    (successComplete : ParserTraceSuccessComplete (typeExprWithFuel fuel) elementTrace)
    (rejectComplete : ParserTraceRejectComplete (typeExprWithFuel fuel) elementRejects)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    TypeDispatchTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, typeExprWithFuel (fuel + 1) input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [typeExprWithFuel_dispatch_trace_reject_iff fuel successSound rejectSound successComplete rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeDispatchSuccessTraceProperties
/-! One positive-fuel dispatch layer composes the six raw success contracts.
The recursive child is the actual preceding-fuel parser, whose success contracts
remain explicit; its frame is unconditional. This is not a complete recursive
production trace theorem. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar TypeDispatchTraceInternals

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}

namespace TypeDispatchTraceInternals

theorem raw_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested) (branch : TypeDispatchBranch) :
    ParserTraceSuccessSound (rawParser nested branch) (TypeDispatchRawTraceParses elementTrace branch) := by
  cases branch with
  | function => exact parseFunctionType_trace_success_sound successSound contextFrame
  | comptime => exact parseComptimeType_trace_success_sound successSound
  | mapping => exact parseMappingType_trace_success_sound successSound contextFrame
  | proxy => exact parseProxyType_trace_success_sound successSound
  | tuple => exact parseTupleType_trace_success_sound successSound contextFrame
  | named => exact parseNamedType_trace_success_sound successSound contextFrame
  | final => intro input output value result; simp [rawParser, rejectAt] at result

theorem raw_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested) (branch : TypeDispatchBranch) :
    ParserTraceSuccessComplete (rawParser nested branch) (TypeDispatchRawTraceParses elementTrace branch) := by
  cases branch with
  | function => exact parseFunctionType_trace_success_complete successComplete contextFrame
  | comptime => exact parseComptimeType_trace_success_complete successComplete
  | mapping => exact parseMappingType_trace_success_complete successComplete contextFrame
  | proxy => exact parseProxyType_trace_success_complete successComplete
  | tuple => exact parseTupleType_trace_success_complete successComplete contextFrame
  | named => exact parseNamedType_trace_success_complete successComplete contextFrame
  | final => intro input value after trace parsed; exact False.elim parsed

theorem raw_success_context
    (contextFrame : ParserSuccessContext nested) (branch : TypeDispatchBranch) :
    ParserSuccessContext (rawParser nested branch) := by
  cases branch with
  | function => exact parseFunctionType_success_context contextFrame
  | comptime => exact parseComptimeType_success_context contextFrame
  | mapping => exact parseMappingType_success_context contextFrame
  | proxy => exact parseProxyType_success_context contextFrame
  | tuple => exact parseTupleType_success_context contextFrame
  | named => exact parseNamedType_success_context contextFrame
  | final => intro input output value result; simp [rawParser, rejectAt] at result

end TypeDispatchTraceInternals

theorem typeExprWithFuel_dispatch_trace_success_sound (fuel : Nat)
    (successSound : ParserTraceSuccessSound (typeExprWithFuel fuel) elementTrace) :
    ParserTraceSuccessSound (typeExprWithFuel (fuel + 1)) (TypeDispatchTraceParses elementTrace) := by
  intro input output value result
  rw [typeExprWithFuel_eq_selected_raw] at result
  rcases raw_trace_success_sound successSound (typeExprWithFuel_success_context fuel) (selectedBranch input) result with
    ⟨trace, parsed, events⟩
  exact ⟨trace, .selected (selectedBranch input) (selectedBranch_selects input) parsed, events⟩

theorem typeExprWithFuel_dispatch_trace_success_complete (fuel : Nat)
    (successComplete : ParserTraceSuccessComplete (typeExprWithFuel fuel) elementTrace) :
    ParserTraceSuccessComplete (typeExprWithFuel (fuel + 1)) (TypeDispatchTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | selected branch selection raw =>
      rcases raw_trace_success_complete successComplete (typeExprWithFuel_success_context fuel) branch raw with
        ⟨output, result, afterEq, events⟩
      exact ⟨output, (typeExprWithFuel_eq_raw_of_selection fuel selection).trans result, afterEq, events⟩

theorem typeExprWithFuel_dispatch_success_context (fuel : Nat) :
    ParserSuccessContext (typeExprWithFuel (fuel + 1)) :=
  typeExprWithFuel_success_context (fuel + 1)

theorem typeExprWithFuel_dispatch_trace_success_iff (fuel : Nat)
    (successSound : ParserTraceSuccessSound (typeExprWithFuel fuel) elementTrace)
    (successComplete : ParserTraceSuccessComplete (typeExprWithFuel fuel) elementTrace)
    {input : State} {value : TypeExpr} {after : Remainder} {trace : List ParseDiagnostic} :
    TypeDispatchTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, typeExprWithFuel (fuel + 1) input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact typeExprWithFuel_dispatch_trace_success_complete fuel successComplete
  · rintro ⟨output, result, afterEq, events⟩
    rcases typeExprWithFuel_dispatch_trace_success_sound fuel successSound result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeExprTraceSoundnessProperties
/-! Every actual successful or rejected recursive type execution has the
fuel-free independent trace, on arbitrary states and with every prior event
preserved. Resource induction is confined to execution soundness; neither
completeness nor existence of a successful/rejected outcome is asserted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

private theorem typeTraceSoundAtFuel (fuel : Nat) :
    ParserTraceSuccessSound (typeExprWithFuel fuel) TypeExprTraceParses ∧
    ParserTraceRejectSound (typeExprWithFuel fuel) TypeExprTraceRejects := by
  induction fuel with
  | zero =>
      constructor
      · intro input output value result
        simp [typeExprWithFuel] at result
      · intro input rejected failure result
        simp [typeExprWithFuel] at result
  | succ fuel ih =>
      constructor
      · intro input output value result
        rcases typeExprWithFuel_dispatch_trace_success_sound fuel ih.1 result with
          ⟨trace, step, events⟩
        exact ⟨trace, TypeExprTraceParses.roll step, events⟩
      · intro input rejected failure result
        rcases typeExprWithFuel_dispatch_reject_trace_sound fuel ih.1 ih.2 result with
          ⟨trace, step, events⟩
        exact ⟨trace, TypeExprTraceRejects.roll step, events⟩

theorem typeExprWithFuel_trace_success_sound (fuel : Nat) :
    ParserTraceSuccessSound (typeExprWithFuel fuel) TypeExprTraceParses :=
  (typeTraceSoundAtFuel fuel).1

theorem typeExprWithFuel_reject_trace_sound (fuel : Nat) :
    ParserTraceRejectSound (typeExprWithFuel fuel) TypeExprTraceRejects :=
  (typeTraceSoundAtFuel fuel).2

theorem typeExpr_trace_success_sound : ParserTraceSuccessSound typeExpr TypeExprTraceParses := by
  intro input output value result
  exact typeExprWithFuel_trace_success_sound (input.remainingCount + 1) result

theorem typeExpr_reject_trace_sound : ParserTraceRejectSound typeExpr TypeExprTraceRejects := by
  intro input rejected failure result
  exact typeExprWithFuel_reject_trace_sound (input.remainingCount + 1) result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeExprTraceCompletenessProperties
/-! Recursive trace completeness at inputs where invariant failure is excluded.
The production parser's existing totality theorem supplies that premise on
valid states only. No unrestricted completeness or existence claim is hidden
in these pointwise correspondences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {input : State} {value : TypeExpr} {after : Remainder}
  {report : ParseDiagnostic} {trace : List ParseDiagnostic}

theorem typeExpr_trace_success_complete_of_ne_invariant
    (invariantFree : ∀ error, typeExpr input ≠ .invariant error)
    (parsed : TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace :=
  trace_success_exists_ok_of_sound typeExpr_trace_success_sound typeExpr_reject_trace_sound
    typeExprTraceExactOutcomeSpec invariantFree parsed

theorem typeExpr_trace_reject_complete_of_ne_invariant
    (invariantFree : ∀ error, typeExpr input ≠ .invariant error)
    (rejection : TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace) :
    ∃ failure rejected, typeExpr input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  trace_reject_exists_reject_of_sound typeExpr_trace_success_sound typeExpr_reject_trace_sound
    typeExprTraceExactOutcomeSpec invariantFree rejection

theorem typeExpr_trace_success_iff_of_ne_invariant
    (invariantFree : ∀ error, typeExpr input ≠ .invariant error) :
    TypeExprTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact typeExpr_trace_success_complete_of_ne_invariant invariantFree
  · rintro ⟨output, result, afterEq, events⟩
    rcases typeExpr_trace_success_sound result with ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem typeExpr_trace_reject_iff_of_ne_invariant
    (invariantFree : ∀ error, typeExpr input ≠ .invariant error) :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact typeExpr_trace_reject_complete_of_ne_invariant invariantFree
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases typeExpr_reject_trace_sound result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem typeExpr_trace_reject_failure_iff_of_ne_invariant
    (invariantFree : ∀ error, typeExpr input ≠ .invariant error) {failure : Failure} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ∃ rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [typeExpr_trace_reject_iff_of_ne_invariant invariantFree]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem typeExpr_trace_success_complete_onValid (inputValid : input.ValidFor)
    (parsed : TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_success_complete_of_ne_invariant (typeExpr_ne_invariant input inputValid) parsed

theorem typeExpr_trace_reject_complete_onValid (inputValid : input.ValidFor)
    (rejection : TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace) :
    ∃ failure rejected, typeExpr input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_reject_complete_of_ne_invariant (typeExpr_ne_invariant input inputValid) rejection

theorem typeExpr_trace_success_iff_onValid (inputValid : input.ValidFor) :
    TypeExprTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_success_iff_of_ne_invariant (typeExpr_ne_invariant input inputValid)

theorem typeExpr_trace_reject_iff_onValid (inputValid : input.ValidFor) :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_reject_iff_of_ne_invariant (typeExpr_ne_invariant input inputValid)

theorem typeExpr_trace_reject_failure_iff_onValid (inputValid : input.ValidFor) {failure : Failure} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ∃ rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_reject_failure_iff_of_ne_invariant (typeExpr_ne_invariant input inputValid)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeUnrestrictedFuelTotalityProperties
/-! The production resource bound suffices on every state, independently of
token provenance, active-window validity, or accumulated diagnostic spans.
Only actual token consumption and successful child progress are used. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem typeExprWithFuel_ordinary_of_remainingCount_lt_unrestricted :
    ∀ fuel input, input.remainingCount < fuel →
      (∃ value next, typeExprWithFuel fuel input = .ok value next) ∨
      (∃ failure next, typeExprWithFuel fuel input = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero => intro input adequate; omega
  | succ fuel ih =>
      intro input adequate
      let children : UnrestrictedFuelElementContract (typeExprWithFuel fuel) fuel := {
        endIndexOnSuccess := fun result =>
          congrArg TokenWindow.endIndex (typeExprWithFuel_success_context fuel result).2
        cursorLtOnSuccess := typeExprWithFuel_cursor_lt_onSuccess fuel
        ordinary := ih
      }
      simp only [typeExprWithFuel]
      split
      · exact parseFunctionType_ordinary_of_unrestrictedElementFuel
          (typeExprWithFuel fuel) fuel children input (by omega)
      · split
        · exact parseComptimeType_ordinary_of_unrestrictedElementFuel
            (typeExprWithFuel fuel) fuel children input (by omega)
        · split
          · exact parseMappingType_ordinary_of_unrestrictedElementFuel
              (typeExprWithFuel fuel) fuel children input (by omega)
          · split
            · exact parseProxyType_ordinary_of_unrestrictedElementFuel
                (typeExprWithFuel fuel) fuel children input (by omega)
            · split
              · exact parseTupleType_ordinary_of_unrestrictedElementFuel
                  (typeExprWithFuel fuel) fuel children input (by omega)
              · split
                · exact parseNamedType_ordinary_of_unrestrictedElementFuel
                    (typeExprWithFuel fuel) fuel children input (by omega)
                · exact Or.inr ⟨_, input, rfl⟩

theorem typeExprWithFuel_ne_invariant_of_remainingCount_lt_unrestricted
    (fuel : Nat) (input : State) (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) : typeExprWithFuel fuel input ≠ .invariant error := by
  intro failed
  rcases typeExprWithFuel_ordinary_of_remainingCount_lt_unrestricted fuel input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

theorem typeExpr_ordinary : Parser.Ordinary typeExpr := by
  intro input
  exact typeExprWithFuel_ordinary_of_remainingCount_lt_unrestricted
    (input.remainingCount + 1) input (by omega)

theorem typeExpr_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    typeExpr input ≠ .invariant error := by
  exact typeExprWithFuel_ne_invariant_of_remainingCount_lt_unrestricted
    (input.remainingCount + 1) input (by omega) error

theorem typeExprWithFuel_unrestrictedFuelElementContract (fuel : Nat) :
    UnrestrictedFuelElementContract (typeExprWithFuel fuel) fuel where
  endIndexOnSuccess result :=
    congrArg TokenWindow.endIndex (typeExprWithFuel_success_context fuel result).2
  cursorLtOnSuccess := typeExprWithFuel_cursor_lt_onSuccess fuel
  ordinary := typeExprWithFuel_ordinary_of_remainingCount_lt_unrestricted fuel

theorem typeExpr_unrestrictedFuelElementContract (fuel : Nat) :
    UnrestrictedFuelElementContract typeExpr fuel where
  endIndexOnSuccess result :=
    congrArg TokenWindow.endIndex (typeExpr_success_context result).2
  cursorLtOnSuccess := typeExpr_cursor_lt_onSuccess
  ordinary input _ := typeExpr_ordinary input

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeExprTraceExistenceProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeExprTraceUnrestrictedProperties
/-! Complete recursive type trace correspondence on arbitrary states. Production
totality discharges invariant exclusion without validity, canonical lexing,
prior-diagnostic, or child-contract assumptions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

theorem typeExpr_trace_success_complete : ParserTraceSuccessComplete typeExpr TypeExprTraceParses :=
  trace_success_complete_of_sound typeExpr_trace_success_sound typeExpr_reject_trace_sound
    (fun _ _ => typeExprTraceExactOutcomeSpec) typeExpr_ne_invariant_unrestricted

theorem typeExpr_trace_reject_complete : ParserTraceRejectComplete typeExpr TypeExprTraceRejects :=
  trace_reject_complete_of_sound typeExpr_trace_success_sound typeExpr_reject_trace_sound
    (fun _ _ => typeExprTraceExactOutcomeSpec) typeExpr_ne_invariant_unrestricted

theorem typeExpr_trace_success_iff
    {input : State} {value : TypeExpr} {after : Remainder} {trace : List ParseDiagnostic} :
    TypeExprTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_success_iff_of_ne_invariant (typeExpr_ne_invariant_unrestricted input)

theorem typeExpr_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_reject_iff_of_ne_invariant (typeExpr_ne_invariant_unrestricted input)

theorem typeExpr_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ∃ rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_reject_failure_iff_of_ne_invariant (typeExpr_ne_invariant_unrestricted input)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeExprTraceStateProperties
/-! Recursive trace correspondence fixes the whole successful/rejected state,
not just a cursor and event suffix. The rebuilt state carries every independent
remainder field, so no token or end-index mismatch is silently forgotten. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

theorem typeExpr_trace_success_state_iff
    {input : State} {value : TypeExpr} {after : Remainder} {trace : List ParseDiagnostic} :
    TypeExprTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      typeExpr input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases typeExpr_trace_success_iff.mp parsed with ⟨output, result, afterEq, events⟩
    have frame := typeExpr_success_context result
    have stateEq := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact stateEq ▸ result
  · intro result
    exact typeExpr_trace_success_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem typeExpr_trace_reject_failure_state_iff
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      typeExpr input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases typeExpr_trace_reject_failure_iff.mp rejection with ⟨rejected, result, afterEq, events⟩
    have window := typeExpr_preservesTokenWindow input
    rw [result] at window
    have stateEq := State.eq_traceResult_of_fields (typeExpr_preservesFile.file_eq_of_reject result)
      (congrArg TokenWindow.endByte window.2) afterEq events
    exact stateEq ▸ result
  · intro result
    exact typeExpr_trace_reject_failure_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem typeExpr_trace_reject_state_iff
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, typeExpr input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases typeExpr_trace_reject_iff.mp rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, typeExpr_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ typeExpr_trace_reject_failure_state_iff.mpr result

end Solcore.Syntax.Parser
end
