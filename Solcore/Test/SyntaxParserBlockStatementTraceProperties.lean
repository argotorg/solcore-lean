import Solcore.Syntax.Parser.BlockStatementTraceProperties

/-! Exact raw block-statement consumers retain the AST and every prior event,
require the final expression semicolon, and propagate failures without recovery. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserBlockStatementTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → Remainder → Statement → Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}

example := @BlockStatementTraceParses.ordinary
example := @BlockStatementTraceRejects.ordinary
example := @BlockStatementTraceParses.result_unique
example := @BlockStatementTraceRejects.result_unique
example := @BlockStatementTraceRejects.disjoint_success
example := @blockStatementTraceExactOutcomeSpec
example := @coreBlockItems_success_context_eq
example := @coreBlock_success_context_eq
example := @blockStatement_trace_success_sound
example := @blockStatement_trace_reject_sound
example := @blockStatement_trace_success_complete
example := @blockStatement_trace_reject_complete
example := @blockStatement_success_context
example := @blockStatement_trace_success_iff
example := @blockStatement_trace_reject_iff
example := @blockStatement_trace_reject_failure_iff

/-- A raw failure leaves the same complete rejected state and failure record.
This statement boundary performs no balanced-window recovery or report commit. -/
theorem raw_rejection_propagates_whole_state
    {input rejected : State} {failure : Failure}
    (result : coreBlock statement .require input = .reject failure rejected) :
    blockStatement statement input = .reject failure rejected :=
  blockStatement_reject_iff_raw.mpr result

/-- The statement wrapper requires even the final expression's semicolon.
Its diagnostic follows both identical inner events after every prior event. -/
theorem block_statement_requires_last_expression_semicolon
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement)
    {input : State} {afterOpening beforeClose remainder : Remainder}
    {openingSpan closingSpan expressionSpan : SourceSpan} {expressionValue : Expr}
    {event : ParseDiagnostic}
    (opening : ExactTokenParses (.symbol .leftBrace)
      input.declarativeRemainder openingSpan afterOpening)
    (inside : afterOpening.cursor < afterOpening.endIndex)
    (notClosing : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex
      afterOpening.cursor (.symbol .rightBrace))
    (valueParsed : statementTrace input.file.id input.window.endByte afterOpening
      { span := expressionSpan, value := .expression expressionValue false } beforeClose [event, event])
    (progress : afterOpening.cursor < beforeClose.cursor)
    (closing : ExactTokenParses (.symbol .rightBrace) beforeClose closingSpan remainder) :
    ∃ output, blockStatement statement input = .ok {
        span := SourceSpan.cover openingSpan closingSpan,
        value := .block [{ span := expressionSpan, value := .expression expressionValue false }]
      } output ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ [event, event,
        { span := expressionSpan, kind := .constraintViolation .expressionRequiresSemicolon }] :=
  blockStatement_trace_success_complete successComplete contextFrame
    (.parsed (.parsed openingSpan closingSpan opening
      (.next inside notClosing valueParsed progress (.close closingSpan closing))
      (.lastRequired (.missing (fun impossible => impossible)))))

/-- Independent raw rejection keeps its earlier inner events, while the
specified whole failure remains separate from the appended diagnostic list. -/
theorem block_statement_rejection_keeps_report_uncommitted
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    {input : State} {remainder : Remainder} {failure : Failure}
    {first second : ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects .require
      input.file.id input.window.endByte input.declarativeRemainder remainder
      failure.toDiagnostic [first, second, first]) :
    ∃ rejected, blockStatement statement input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧
      rejected.diagnostics = input.diagnostics ++ [first, second, first] :=
  (blockStatement_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
    contextFrame).mp (.rejected rejection)

/-- Only the inner frame law is required for successful source/window
preservation; neither validity nor empty incoming diagnostics is assumed. -/
theorem successful_block_statement_retains_full_context
    (contextFrame : StatementSuccessContext statement)
    {input output : State} {value : Statement}
    (result : blockStatement statement input = .ok value output) :
    output.file = input.file ∧ output.window = input.window :=
  blockStatement_success_context contextFrame result

/-- Independent nested block statements retain strict progress and the active
token carrier when the corresponding inner trace law is available. -/
theorem independent_block_statement_keeps_window_and_progress
    {source : SourceId} {endByte : Nat}
    (statementWindow : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.cursor < output.cursor ∧ output.cursor ≤ output.endIndex :=
  ⟨(parsed.output_window statementWindow).1, (parsed.output_window statementWindow).2,
    parsed.cursor_lt, parsed.output_cursor_le_endIndex⟩

end Solcore.Test.SyntaxParserBlockStatementTraceProperties
