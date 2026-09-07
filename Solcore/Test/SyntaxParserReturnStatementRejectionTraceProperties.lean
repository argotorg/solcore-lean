import Solcore.Syntax.Parser.ReturnStatementRejectionTraceCompletenessProperties
import Solcore.Test.SyntaxReturnStatementRejectionTraceProperties

/-! Return execution consumers expose their abstract expression contracts.
Every incoming event remains before the specified rejecting value's events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserReturnStatementRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
    List ParseDiagnostic → Prop}

example := @StatementSimpleInternals.optionalReturnValue_reject_trace_sound
example := @StatementSimpleInternals.optionalReturnValue_trace_reject_complete
example := @StatementSimpleInternals.optionalReturnValue_trace_reject_iff
example := @returnStatement_reject_trace_sound
example := @returnStatement_trace_reject_complete
example := @returnStatement_trace_reject_iff
example := @returnStatement_trace_reject_failure_iff

/-- The semicolon guard bypasses even an expression parser that would reject
at that input. The complete state and all existing diagnostics stay unchanged. -/
theorem semicolon_bypasses_expression_failure
    {input : State} {span : SourceSpan}
    (current : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    StatementSimpleInternals.optionalReturnValue expression input = .ok none input :=
  StatementSimpleInternals.optionalReturnValue_eq_ok_none_of_tokenAt expression current

/-- Earlier expression events and their duplicates survive before the exact
window-end semicolon failure; the report is not part of the appended trace. -/
theorem missing_semicolon_retains_events_before_full_failure
    (successSound : ExpressionTraceSuccessSound expression expressionTrace)
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression)
    {input : State} {afterMarker afterValue : Remainder} {markerSpan : SourceSpan}
    {value : Expr} {event : ParseDiagnostic}
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (notEmpty : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon))
    (parsedValue : expressionTrace input.file.id input.window.endByte
      afterMarker value afterValue [event, event])
    (atEnd : afterValue.endIndex ≤ afterValue.cursor) :
    ∃ rejected, returnStatement expression input = .reject {
        span := { source := input.file.id, startByte := input.window.endByte, endByte := input.window.endByte },
        found := none, expected := { head := .symbol .semicolon, tail := [] }, context := .statement
      } rejected ∧ rejected.declarativeRemainder = afterValue ∧
      rejected.diagnostics = input.diagnostics ++ [event, event] :=
  (returnStatement_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
    contextFrame).mp
    (SyntaxReturnStatementRejectionTraceProperties.missing_semicolon_keeps_expression_events
      marker notEmpty parsedValue atEnd)

/-- The expression's first failure remains separate from its own event list;
return processing introduces no semicolon failure after it. -/
theorem expression_report_is_not_replaced
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression)
    {input : State} {afterMarker remainder : Remainder} {markerSpan : SourceSpan}
    {diagnostic first second : ParseDiagnostic}
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (notEmpty : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon))
    (rejectedValue : expressionRejects input.file.id input.window.endByte afterMarker remainder
      diagnostic [first, second, first]) :
    ∃ failure rejected, returnStatement expression input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ [first, second, first] :=
  returnStatement_trace_reject_complete successComplete rejectComplete contextFrame
    (.valueRejected markerSpan marker (.expressionRejected notEmpty rejectedValue))

end Solcore.Test.SyntaxParserReturnStatementRejectionTraceProperties
