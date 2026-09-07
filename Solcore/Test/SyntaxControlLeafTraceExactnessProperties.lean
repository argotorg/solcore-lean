import Solcore.Syntax.DeclarativeTerminatedControlTraceExactnessProperties
import Solcore.Syntax.Parser.ControlLeafDiagnosticTraceProperties

/-! Independent totality and joint exactness consumers for concrete control
leaves, including malformed token carriers and recovered block results. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxControlLeafTraceExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

/-- Every incoming state has a silent ordinary leaf outcome; in particular,
there is no validity or diagnostic-free premise hiding invariant cases. -/
theorem every_control_leaf_has_silent_outcome
    (keywordValue : HardKeyword) (statementValue : StatementValue) (input : State) :
    (∃ statement output,
      ControlInternals.terminatedControl keywordValue statementValue input = .ok statement output ∧
      output.diagnostics = input.diagnostics) ∨
    (∃ failure rejected,
      ControlInternals.terminatedControl keywordValue statementValue input = .reject failure rejected ∧
      rejected.diagnostics = input.diagnostics) := by
  rcases terminatedControlStatementTrace_exists_outcome keywordValue statementValue
      input.file.id input.window.endByte input.declarativeRemainder with successful | rejected
  · rcases successful with ⟨statement, after, parsed⟩
    rcases (ControlInternals.terminatedControl_trace_success_iff keywordValue statementValue).mp
        parsed with ⟨output, result, _, diagnostics⟩
    exact Or.inl ⟨statement, output, result, by simpa only [List.append_nil] using diagnostics⟩
  · rcases rejected with ⟨after, diagnostic, traced⟩
    rcases (ControlInternals.terminatedControl_trace_reject_iff keywordValue statementValue).mp
        traced with ⟨failure, rejected, result, _, _, diagnostics⟩
    exact Or.inr ⟨failure, rejected, result, by simpa only [List.append_nil] using diagnostics⟩

theorem break_rejection_excludes_all_success_traces
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : BreakStatementTraceRejects source endByte input rejected report trace) :
    ¬ ∃ statement output events, BreakStatementTraceParses source endByte
      input statement output events :=
  (breakStatementTraceExactOutcomeSpec source endByte).successRejectDisjoint rejection

/-- A missing slot inside an oversized window reports the explicit window
byte boundary without consuming a token or discarding incoming diagnostics. -/
theorem missing_array_slot_reports_break_at_window_byte
    {input : State} (inside : input.cursor < input.window.endIndex)
    (missing : input.tokens[input.cursor]? = none) :
    ∃ rejected, breakStatement input = .reject {
        span := { source := input.file.id
                  startByte := input.window.endByte
                  endByte := input.window.endByte },
        found := none, expected := { head := .keyword .breakKw, tail := [] }, context := .statement
      } rejected ∧ rejected.declarativeRemainder = input.declarativeRemainder ∧
      rejected.diagnostics = input.diagnostics := by
  have absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.keyword .breakKw) := by
    rintro ⟨span, _, present⟩
    simp only [missing] at present
    cases present
  simpa only [List.append_nil] using breakStatement_trace_reject_failure_iff.mp
    (.markerMissing absent (.reported (.missingToken inside missing)))

/-- Recovery does not introduce ambiguity in restricted continue blocks:
the AST, resumed parent remainder, and complete event list all stay unique. -/
theorem isolated_continue_block_trace_is_unique
    (policy : CoreBlockTailPolicy) {source : SourceId} {endByte : Nat}
    {input afterLeft afterRight : Remainder} {left right : Block}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : IsolatedBlockTraceParses (CoreBlockTraceParses ContinueStatementTraceParses policy)
      (CoreBlockTraceRejects ContinueStatementTraceParses ContinueStatementTraceRejects policy)
      source endByte input left afterLeft leftTrace)
    (rightParsed : IsolatedBlockTraceParses (CoreBlockTraceParses ContinueStatementTraceParses policy)
      (CoreBlockTraceRejects ContinueStatementTraceParses ContinueStatementTraceRejects policy)
      source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace :=
  (isolatedTerminatedControlCoreBlockTraceExactOutcomeSpec .continueKw .continueStmt
    policy source endByte).successResultUnique leftParsed rightParsed

end Solcore.Test.SyntaxControlLeafTraceExactnessProperties
