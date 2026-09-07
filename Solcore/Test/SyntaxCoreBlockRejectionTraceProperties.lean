import Solcore.Syntax.DeclarativeCoreBlockRejectionTraceProperties

/-! Independent consumers of exact raw Core rejection traces. Reports use
the supplied diagnostic window, and delayed tail checks never enter rejection. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCoreBlockRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable {statementTrace : SourceId → Nat → Remainder → Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}

/-- No opening brace means no statement or validation event is produced;
the full observed token and expectation remain in the separate failure report. -/
theorem missing_opening_keeps_exact_observation
    {input : Remainder} {span : SourceSpan} {found : Option TokenKind}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBrace))
    (current : CurrentInputAt source endByte input span found) :
    CoreBlockTraceRejects statementTrace statementRejects policy source endByte input input
      { span, kind := .unexpected found { head := .symbol .leftBrace, tail := [] } .statement } [] :=
  .openingMissing absent (.reported current)

/-- At the active window end, the supplied byte endpoint determines the report
even when tokens remain outside that window in the shared carrier. -/
theorem missing_close_uses_window_endpoint
    {input : Remainder} (atEnd : input.endIndex ≤ input.cursor) :
    CoreBlockItemsTraceRejects statementTrace statementRejects source endByte input input
      { span := { source, startByte := endByte, endByte },
        kind := .unexpected none { head := .symbol .rightBrace, tail := [] } .statement } [] := by
  refine .missingClose ?_ atEnd (.reported (.windowEnd atEnd))
  rintro ⟨span, inside, _⟩
  exact Nat.not_lt_of_ge atEnd inside

/-- The exact first statement report and its preceding events are retained
as soon as the preferred closing-brace branch has been excluded. -/
theorem first_statement_rejection_keeps_report
    {input afterOpening rejected : Remainder} {openingSpan : SourceSpan}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (opening : ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening)
    (inside : afterOpening.cursor < afterOpening.endIndex)
    (absent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex
      afterOpening.cursor (.symbol .rightBrace))
    (rejection : statementRejects source endByte afterOpening rejected diagnostic trace) :
    CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected diagnostic trace :=
  .itemsRejected openingSpan opening (.statementRejected inside absent rejection)

/-- Repeated events retain multiplicity and statement order, and the last
uncommitted report is not appended implicitly. Tail checks have not run. -/
theorem later_rejection_keeps_ordered_events
    {input afterOpening afterFirst beforeReject rejected : Remainder}
    {openingSpan : SourceSpan} {first second : Statement}
    {firstEvent secondEvent failureEvent diagnostic : ParseDiagnostic}
    (opening : ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening)
    (insideFirst : afterOpening.cursor < afterOpening.endIndex)
    (absentFirst : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex
      afterOpening.cursor (.symbol .rightBrace))
    (firstParsed : statementTrace source endByte afterOpening first afterFirst [firstEvent])
    (firstProgress : afterOpening.cursor < afterFirst.cursor)
    (insideSecond : afterFirst.cursor < afterFirst.endIndex)
    (absentSecond : TokenKindAbsentAt afterFirst.tokens afterFirst.endIndex
      afterFirst.cursor (.symbol .rightBrace))
    (secondParsed : statementTrace source endByte afterFirst second beforeReject [secondEvent, secondEvent])
    (secondProgress : afterFirst.cursor < beforeReject.cursor)
    (insideFailure : beforeReject.cursor < beforeReject.endIndex)
    (absentFailure : TokenKindAbsentAt beforeReject.tokens beforeReject.endIndex
      beforeReject.cursor (.symbol .rightBrace))
    (rejection : statementRejects source endByte beforeReject rejected diagnostic [failureEvent]) :
    CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected diagnostic [firstEvent, secondEvent, secondEvent, failureEvent] :=
  .itemsRejected openingSpan opening
    (.laterRejected insideFirst absentFirst firstParsed firstProgress
      (.laterRejected insideSecond absentSecond secondParsed secondProgress
        (.statementRejected insideFailure absentFailure rejection)))

/-- Changing the final-expression policy does not retroactively check a
successfully parsed prefix when its raw block later rejects. -/
theorem rejected_prefix_is_policy_independent
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects .allow source endByte
      input rejected diagnostic trace) :
    CoreBlockTraceRejects statementTrace statementRejects .require source endByte
      input rejected diagnostic trace := rejection.withPolicy .require

example := @CoreBlockItemsTraceRejects.ordinary
example := @CoreBlockTraceRejects.ordinary
example := @CoreBlockItemsTraceRejects.result_unique
example := @CoreBlockTraceRejects.result_unique
example := @CoreBlockItemsTraceRejects.disjoint_success
example := @CoreBlockTraceRejects.disjoint_success

end Solcore.Test.SyntaxCoreBlockRejectionTraceProperties
