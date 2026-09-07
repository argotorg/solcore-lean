import Solcore.Syntax.Parser.ControlLeafDiagnosticTraceProperties
import Solcore.Syntax.Parser.CoreBlockTraceCompletenessProperties

/-! Concrete Core control leaves retain prior events, exact spans, and ordered
first-failure reports, without any abstract child-parser assumption. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserControlLeafDiagnosticTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @TerminatedControlStatementTraceParses.result_unique
example := @TerminatedControlStatementTraceRejects.result_unique
example := @breakStatement_trace_reject_sound
example := @continueStatement_trace_reject_complete

theorem break_retains_exact_spans_and_prior_events
    {input : State} {afterMarker after : Remainder} {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .breakKw) input.declarativeRemainder markerSpan afterMarker)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterMarker semicolonSpan after) :
    ∃ output, breakStatement input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan, value := .breakStmt
      } output ∧ output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using breakStatement_trace_success_iff.mp
    ⟨.parsed markerSpan semicolonSpan marker semicolon, rfl⟩

theorem continue_retains_exact_spans_and_prior_events
    {input : State} {afterMarker after : Remainder} {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .continueKw)
      input.declarativeRemainder markerSpan afterMarker)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterMarker semicolonSpan after) :
    ∃ output, continueStatement input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan, value := .continueStmt
      } output ∧ output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using continueStatement_trace_success_iff.mp
    ⟨.parsed markerSpan semicolonSpan marker semicolon, rfl⟩

/-- Even a semicolon at the initial cursor must first fail the required
`break` keyword; it is not consumed or reported as a missing semicolon. -/
theorem leading_semicolon_reports_missing_break
    {input : State} {span : SourceSpan} {afterSemicolon : Remainder}
    (semicolon : ExactTokenParses (.symbol .semicolon)
      input.declarativeRemainder span afterSemicolon) :
    ∃ rejected, breakStatement input = .reject {
        span, found := some (.symbol .semicolon),
        expected := { head := .keyword .breakKw, tail := [] }, context := .statement
      } rejected ∧ rejected.declarativeRemainder = input.declarativeRemainder ∧
      rejected.diagnostics = input.diagnostics := by
  have absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.keyword .breakKw) := by
    rintro ⟨otherSpan, _, found⟩
    have current := semicolon.1.2
    change input.tokens[input.cursor]? = some { span, value := .symbol .semicolon } at current
    rw [found] at current
    cases current
  simpa only [List.append_nil] using breakStatement_trace_reject_failure_iff.mp
    (.markerMissing absent (.reported (.token semicolon.1)))

/-- Once `continue` is consumed, a window end fixes every failure field at the
explicit byte boundary, regardless of any tokens outside that window. -/
theorem continue_window_end_reports_missing_semicolon
    {input : State} {afterMarker : Remainder} {markerSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .continueKw)
      input.declarativeRemainder markerSpan afterMarker)
    (atEnd : afterMarker.endIndex ≤ afterMarker.cursor) :
    ∃ rejected, continueStatement input = .reject {
        span := { source := input.file.id
                  startByte := input.window.endByte
                  endByte := input.window.endByte },
        found := none, expected := { head := .symbol .semicolon, tail := [] }, context := .statement
      } rejected ∧ rejected.declarativeRemainder = afterMarker ∧
      rejected.diagnostics = input.diagnostics := by
  have absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor
      (.symbol .semicolon) := by
    rintro ⟨span, inside, _⟩
    omega
  simpa only [List.append_nil] using continueStatement_trace_reject_failure_iff.mp
    (.semicolonMissing markerSpan marker absent (.reported (.windowEnd atEnd)))

/-- Failure on a non-semicolon after `break` reports that exact token's span
and kind, while retaining the keyword's consumption and the prior event order. -/
theorem break_missing_semicolon_retains_keyword_consumption
    {input : State} {afterMarker : Remainder} {markerSpan offendingSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .breakKw) input.declarativeRemainder markerSpan afterMarker)
    (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor
      (.symbol .semicolon))
    (found : Option TokenKind)
    (current : CurrentInputAt input.file.id input.window.endByte afterMarker offendingSpan found) :
    ∃ rejected, breakStatement input = .reject {
        span := offendingSpan, found, expected := { head := .symbol .semicolon, tail := [] },
        context := .statement
      } rejected ∧ rejected.declarativeRemainder = afterMarker ∧
      rejected.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using breakStatement_trace_reject_failure_iff.mp
    (.semicolonMissing markerSpan marker absent (.reported current))

/-- The actual leaf contracts instantiate raw block equivalence without
assuming any statement execution/grammar bridge from the consumer. -/
theorem break_only_raw_block_trace_iff
    (policy : TailExpressionPolicy) {input : State} {body : Block} {after : Remainder}
    {trace : List ParseDiagnostic} :
    CoreBlockTraceParses BreakStatementTraceParses policy.declarative
      input.file.id input.window.endByte input.declarativeRemainder body after trace ↔
    ∃ output, coreBlock breakStatement policy input = .ok body output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  coreBlock_trace_success_iff breakStatement_trace_success_sound
    breakStatement_trace_success_complete breakStatement_success_context policy

end Solcore.Test.SyntaxParserControlLeafDiagnosticTraceProperties
