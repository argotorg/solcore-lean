import Solcore.Syntax.DeclarativeComptimeTypeTraceProperties
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
import Solcore.Syntax.Parser.Type

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
