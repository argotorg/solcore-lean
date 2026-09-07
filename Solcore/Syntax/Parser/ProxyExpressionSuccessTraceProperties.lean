import Solcore.Syntax.DeclarativeProxyExpressionTraceGrammar
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! The real proxy parser preserves every nested type event. Its execution
contracts are conditional on the real type parser, whose diagnostics are not
assumed silent. Source/full-window preservation is a separate child contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {typeTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem proxyExpression_success_iff_components {input output : State} {value : Expr} :
    proxyExpression input = .ok value output ↔
    ∃ marker afterMarker type,
      symbol .at .expression input = .ok marker afterMarker ∧
      typeExpr afterMarker = .ok type output ∧
      value = { span := SourceSpan.cover marker.span type.span, value := .proxy marker.span type } := by
  constructor
  · intro result
    unfold proxyExpression at result
    cases markerResult : symbol .at .expression input with
    | reject => simp only [bind, markerResult] at result; contradiction
    | invariant => simp only [bind, markerResult] at result; contradiction
    | ok marker afterMarker =>
        simp only [bind, markerResult] at result
        cases typeResult : typeExpr afterMarker with
        | reject => simp only [typeResult] at result; contradiction
        | invariant => simp only [typeResult] at result; contradiction
        | ok type next =>
            simp only [typeResult, pure] at result
            cases result
            exact ⟨marker, afterMarker, type, rfl, typeResult, rfl⟩
  · rintro ⟨marker, afterMarker, type, markerResult, typeResult, rfl⟩
    simp only [proxyExpression, bind, markerResult, typeResult, pure]

theorem proxyExpression_trace_success_sound
    (successSound : ParserTraceSuccessSound typeExpr typeTrace) :
    ExpressionTraceSuccessSound proxyExpression (DeclarativeGrammar.ProxyExpressionTraceParses typeTrace) := by
  intro input output value result
  rcases proxyExpression_success_iff_components.mp result with
    ⟨marker, afterMarker, type, markerResult, typeResult, rfl⟩
  have markerParsed := symbol_success_exactTokenParses .at .expression markerResult
  have markerState := (symbol_ok_tokenAt .at .expression markerResult).2
  subst afterMarker
  rcases successSound typeResult with ⟨trace, typed, events⟩
  exact ⟨trace, .parsed marker.span markerParsed typed, events⟩

theorem proxyExpression_trace_success_complete
    (successComplete : ParserTraceSuccessComplete typeExpr typeTrace) :
    ExpressionTraceSuccessComplete proxyExpression (DeclarativeGrammar.ProxyExpressionTraceParses typeTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed markerSpan marker typed =>
      have markerResult := symbol_eq_ok_of_exactTokenParses .at .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) typed with
        ⟨output, typeResult, afterEq, events⟩
      exact ⟨output, proxyExpression_success_iff_components.mpr
        ⟨_, _, _, markerResult, typeResult, rfl⟩, afterEq, events⟩

theorem proxyExpression_success_context (contextFrame : ParserSuccessContext typeExpr) :
    ExpressionSuccessContext proxyExpression := by
  intro input output value result
  rcases proxyExpression_success_iff_components.mp result with
    ⟨marker, afterMarker, type, markerResult, typeResult, _⟩
  have frame := contextFrame typeResult
  rw [(symbol_ok_tokenAt .at .expression markerResult).2] at frame
  exact frame

theorem proxyExpression_trace_success_iff
    (successSound : ParserTraceSuccessSound typeExpr typeTrace)
    (successComplete : ParserTraceSuccessComplete typeExpr typeTrace)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ProxyExpressionTraceParses typeTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, proxyExpression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact proxyExpression_trace_success_complete successComplete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases proxyExpression_trace_success_sound successSound result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans diagnostics)
    simpa only [afterEq, same] using parsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
