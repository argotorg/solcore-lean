import Solcore.Syntax.Parser.OptionalReturnValueTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
import Solcore.Syntax.Parser.StatementDiagnosticTraceContracts

/-! Exact successful return statements from explicit expression trace laws.
The keyword and semicolon are silent; only the optional expression adds events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
      next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- `return;` never invokes the supplied expression parser. Its unconditional
execution changes only the cursor, even if that parser would fail or emit events. -/
theorem returnStatement_eq_ok_none_of_exactTokens
    (expression : Parser Expr) {input : State} {afterMarker after : DeclarativeGrammar.Remainder}
    {markerSpan semicolonSpan : SourceSpan}
    (marker : DeclarativeGrammar.ExactTokenParses (.keyword .returnKw)
      input.declarativeRemainder markerSpan afterMarker)
    (semicolon : DeclarativeGrammar.ExactTokenParses (.symbol .semicolon)
      afterMarker semicolonSpan after) :
    returnStatement expression input = .ok {
      span := SourceSpan.cover markerSpan semicolonSpan, value := .returnStmt none
    } { input with cursor := input.cursor + 2 } := by
  have markerResult := keyword_eq_ok_of_exactTokenParses .returnKw .statement marker
  rcases marker with ⟨_, rfl⟩
  have valueResult := StatementSimpleInternals.optionalReturnValue_eq_ok_none_of_tokenAt
    expression (input := { input with cursor := input.cursor + 1 }) semicolon.1
  have semicolonResult := symbol_eq_ok_of_exactTokenParses .semicolon .statement
    (input := { input with cursor := input.cursor + 1 }) semicolon
  simp only [returnStatement, bind, markerResult, valueResult, semicolonResult, pure]

theorem returnStatement_trace_success_sound
    (sound : ExpressionTraceSuccessSound expression expressionTrace) :
    StatementTraceSuccessSound (returnStatement expression)
      (DeclarativeGrammar.ReturnStatementTraceParses expressionTrace) := by
  intro input output statement result
  unfold returnStatement at result
  rcases bind_ok_components result with ⟨marker, afterMarker, markerResult, valueStage⟩
  rcases bind_ok_components valueStage with ⟨value, afterValue, valueResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with ⟨semicolon, next, semicolonResult, finished⟩
  cases finished
  rcases StatementSimpleInternals.optionalReturnValue_success_trace_sound sound valueResult with
    ⟨trace, valueParsed, events⟩
  have markerShape := (keyword_ok_tokenAt .returnKw .statement markerResult).2
  have semicolonShape := (symbol_ok_tokenAt .semicolon .statement semicolonResult).2
  refine ⟨trace, .parsed marker.span semicolon.span
    (keyword_success_exactTokenParses .returnKw .statement markerResult) ?_
    (symbol_success_exactTokenParses .semicolon .statement semicolonResult), ?_⟩
  · simpa only [markerShape] using valueParsed
  · rw [semicolonShape]
    simpa only [markerShape, State.diagnostics] using events

theorem returnStatement_trace_success_complete
    (complete : ExpressionTraceSuccessComplete expression expressionTrace) :
    StatementTraceSuccessComplete (returnStatement expression)
      (DeclarativeGrammar.ReturnStatementTraceParses expressionTrace) := by
  intro input statement after trace parsed
  cases parsed with
  | parsed marker semicolon markerParsed valueParsed semicolonParsed =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .returnKw .statement markerParsed
      rcases markerParsed with ⟨_, rfl⟩
      rcases StatementSimpleInternals.optionalReturnValue_trace_success_complete complete
          (input := { input with cursor := input.cursor + 1 }) valueParsed with
        ⟨afterValue, valueResult, valueAfter, events⟩
      rw [← valueAfter] at semicolonParsed
      have semicolonResult := symbol_eq_ok_of_exactTokenParses .semicolon .statement semicolonParsed
      refine ⟨{ afterValue with cursor := afterValue.cursor + 1 }, ?_, semicolonParsed.2.symm, ?_⟩
      · simp only [returnStatement, bind, markerResult, valueResult, semicolonResult, pure]
      · simpa only [State.diagnostics] using events

theorem returnStatement_success_context
    (contextFrame : ExpressionSuccessContext expression) :
    StatementSuccessContext (returnStatement expression) := by
  intro input output statement result
  unfold returnStatement at result
  rcases bind_ok_components result with ⟨marker, afterMarker, markerResult, valueStage⟩
  rcases bind_ok_components valueStage with ⟨value, afterValue, valueResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with ⟨semicolon, next, semicolonResult, finished⟩
  cases finished
  have markerShape := (keyword_ok_tokenAt .returnKw .statement markerResult).2
  have semicolonShape := (symbol_ok_tokenAt .semicolon .statement semicolonResult).2
  have frame := StatementSimpleInternals.optionalReturnValue_success_context_eq contextFrame valueResult
  simpa only [semicolonShape, markerShape] using frame

/-- Return success retains the complete optional-value AST, token remainder,
and expression trace. General expressions remain an explicit conditional input. -/
theorem returnStatement_trace_success_iff
    (sound : ExpressionTraceSuccessSound expression expressionTrace)
    (complete : ExpressionTraceSuccessComplete expression expressionTrace)
    {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ReturnStatementTraceParses expressionTrace
      input.file.id input.window.endByte input.declarativeRemainder statement after trace ↔
    ∃ output, returnStatement expression input = .ok statement output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact returnStatement_trace_success_complete complete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases returnStatement_trace_success_sound sound result with ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser
