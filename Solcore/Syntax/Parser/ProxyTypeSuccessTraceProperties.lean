import Solcore.Syntax.DeclarativeProxyTypeTraceGrammar
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
import Solcore.Syntax.Parser.Type

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
