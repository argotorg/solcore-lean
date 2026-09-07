import Solcore.Syntax.DeclarativeReturnStatementRejectionTraceProperties

/-! Independent return-rejection consumers preserve the first failure,
semicolon guard priority, repeated expression events, and source-window reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxReturnStatementRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Expr → Remainder →
    List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

example := @OptionalReturnValueTraceRejects.ordinary
example := @ReturnStatementTraceRejects.ordinary
example := @OptionalReturnValueTraceRejects.result_unique
example := @ReturnStatementTraceRejects.result_unique
example := @OptionalReturnValueTraceRejects.disjoint_success
example := @ReturnStatementTraceRejects.disjoint_success

/-- A current semicolon prevents any optional-value rejection regardless of
the outcomes described by the abstract expression grammar. -/
theorem semicolon_prevents_value_rejection
    {input : Remainder} {span : SourceSpan}
    (current : TokenAt input.tokens input.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    ¬ ∃ rejected diagnostic trace,
      OptionalReturnValueTraceRejects expressionRejects source endByte input rejected diagnostic trace := by
  rintro ⟨_, _, _, rejection⟩
  cases rejection with
  | expressionRejected absent _ => exact absent ⟨span, current⟩

/-- Return forwards the inner expression's own report and preceding events;
it does not replace that report with a later semicolon expectation. -/
theorem expression_rejection_is_first_failure
    {input afterMarker rejected : Remainder} {markerSpan : SourceSpan}
    {diagnostic first second : ParseDiagnostic}
    (marker : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
    (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon))
    (rejectedValue : expressionRejects source endByte afterMarker rejected diagnostic
      [first, second, first]) :
    ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input rejected diagnostic [first, second, first] :=
  .valueRejected markerSpan marker (.expressionRejected absent rejectedValue)

/-- A successful expression followed by the window end keeps its repeated
events and reports the required semicolon at the exact supplied byte boundary. -/
theorem missing_semicolon_keeps_expression_events
    {input afterMarker afterValue : Remainder} {markerSpan : SourceSpan}
    {value : Expr} {event : ParseDiagnostic}
    (marker : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
    (notEmpty : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon))
    (parsedValue : expressionTrace source endByte afterMarker value afterValue [event, event])
    (atEnd : afterValue.endIndex ≤ afterValue.cursor) :
    ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input afterValue {
        span := { source, startByte := endByte, endByte },
        kind := .unexpected none { head := .symbol .semicolon, tail := [] } .statement
      } [event, event] := by
  refine .semicolonRejected markerSpan marker (.present notEmpty parsedValue) ?_
    (.reported (.windowEnd atEnd))
  rintro ⟨span, inside, _⟩
  exact Nat.not_lt_of_ge atEnd inside

/-- An omitted return expression cannot later reach semicolon rejection:
its omission witness already fixes a present semicolon at the same remainder. -/
theorem absent_value_excludes_semicolon_rejection
    {input afterValue : Remainder} {trace : List ParseDiagnostic}
    (parsed : OptionalReturnValueTraceParses expressionTrace source endByte
      input none afterValue trace) :
    ¬ TokenKindAbsentAt afterValue.tokens afterValue.endIndex afterValue.cursor (.symbol .semicolon) := by
  intro absent
  cases parsed with
  | absent span current => exact absent ⟨span, current⟩

end Solcore.Test.SyntaxReturnStatementRejectionTraceProperties
