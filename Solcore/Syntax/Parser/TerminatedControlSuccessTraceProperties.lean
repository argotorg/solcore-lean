import Solcore.Syntax.DeclarativeTerminatedControlTraceProperties
import Solcore.Syntax.Parser.CoreStatementControlSoundnessProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
import Solcore.Syntax.Parser.StatementDiagnosticTraceContracts

/-! Exact silent success for the real keyword-plus-semicolon statement parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- A successful leaf changes only the cursor, advancing exactly two tokens. -/
theorem terminatedControl_success_state_shape
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input output : State} {statement : Statement}
    (result : terminatedControl keywordValue statementValue input = .ok statement output) :
    output = { input with cursor := input.cursor + 2 } := by
  unfold terminatedControl at result
  cases markerResult : keyword keywordValue .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      cases semicolonResult : symbol .semicolon .statement afterMarker with
      | invariant error => simp [bind, markerResult, semicolonResult] at result
      | reject failure rejected => simp [bind, markerResult, semicolonResult] at result
      | ok semicolon next =>
          simp only [bind, markerResult, semicolonResult, pure] at result
          cases result
          rw [(symbol_ok_tokenAt .semicolon .statement semicolonResult).2,
            (keyword_ok_tokenAt keywordValue .statement markerResult).2]

/-- Exact tokens determine the complete AST and cursor update, without source
validity, empty prior diagnostics, or any child-parser assumption. -/
theorem terminatedControl_eq_ok_of_ordinary
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TerminatedControlStatementOrdinaryParses
      keywordValue statementValue input.declarativeRemainder statement after) :
    terminatedControl keywordValue statementValue input = .ok statement
      { input with cursor := input.cursor + 2 } := by
  cases parsed with
  | parsed marker semicolon markerParsed semicolonParsed =>
      have markerResult := keyword_eq_ok_of_exactTokenParses keywordValue .statement markerParsed
      rcases markerParsed with ⟨_, rfl⟩
      have semicolonResult := symbol_eq_ok_of_exactTokenParses .semicolon .statement
        (input := { input with cursor := input.cursor + 1 }) semicolonParsed
      simp only [terminatedControl, bind, markerResult, semicolonResult, pure]

theorem terminatedControl_trace_success_sound
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    StatementTraceSuccessSound (terminatedControl keywordValue statementValue)
      (DeclarativeGrammar.TerminatedControlStatementTraceParses keywordValue statementValue) := by
  intro input output statement result
  refine ⟨[], ⟨terminatedControl_success_sound keywordValue statementValue result, rfl⟩, ?_⟩
  rw [terminatedControl_success_state_shape keywordValue statementValue result]
  simp only [List.append_nil, State.diagnostics]

theorem terminatedControl_trace_success_complete
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    StatementTraceSuccessComplete (terminatedControl keywordValue statementValue)
      (DeclarativeGrammar.TerminatedControlStatementTraceParses keywordValue statementValue) := by
  intro input statement after trace parsed
  rcases parsed with ⟨parsed, rfl⟩
  have result := terminatedControl_eq_ok_of_ordinary keywordValue statementValue parsed
  refine ⟨_, result, ?_, by simp only [List.append_nil, State.diagnostics]⟩
  cases parsed with
  | parsed marker semicolon markerParsed semicolonParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      exact semicolonParsed.2.symm

theorem terminatedControl_success_context
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    StatementSuccessContext (terminatedControl keywordValue statementValue) := by
  intro input output statement result
  rw [terminatedControl_success_state_shape keywordValue statementValue result]
  exact ⟨rfl, rfl⟩

/-- The complete independent success trace is equivalent to actual execution. -/
theorem terminatedControl_trace_success_iff
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TerminatedControlStatementTraceParses keywordValue statementValue
      input.file.id input.window.endByte input.declarativeRemainder statement after trace ↔
    ∃ output, terminatedControl keywordValue statementValue input = .ok statement output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact terminatedControl_trace_success_complete keywordValue statementValue
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases terminatedControl_trace_success_sound keywordValue statementValue result with
      ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser.ControlInternals
