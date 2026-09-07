import Solcore.Syntax.DeclarativeCoreBlockTraceProperties

/-! Independent raw-block trace consumers. Closing-brace priority, unchanged
ASTs, duplicated statement events, and delayed tail reports remain explicit. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCoreBlockTraceProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable {statementTrace : SourceId → Nat → Remainder → Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementOrdinary : Remainder → Statement → Remainder → Prop}
  {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}

example (statementErases : ∀ {input statement output trace},
    statementTrace source endByte input statement output trace →
      statementOrdinary input statement output)
    {input output : Remainder} {body : Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    CoreBlockOrdinaryParses statementOrdinary policy input body output :=
  parsed.ordinary statementErases

example (statementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    statementTrace source endByte input left afterLeft leftTrace →
    statementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Block}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : CoreBlockTraceParses statementTrace policy source endByte
      input left afterLeft leftTrace)
    (rightParsed : CoreBlockTraceParses statementTrace policy source endByte
      input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace :=
  leftParsed.result_unique statementUnique rightParsed

example (statementWindow : ∀ {input statement output trace},
    statementTrace source endByte input statement output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {body : Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.cursor < output.cursor ∧ output.cursor ≤ output.endIndex :=
  ⟨(parsed.output_window statementWindow).1, (parsed.output_window statementWindow).2,
    parsed.cursor_lt, parsed.output_cursor_le_endIndex⟩

example {input output : Remainder} {statements : List Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) :
    statements.length < output.cursor - input.cursor := parsed.length_lt_cursor_distance

/-- Empty raw blocks have no statement or tail-validation events under either
policy, and both exact brace spans still determine the retained empty AST. -/
theorem empty_block_is_silent
    {input afterOpening output : Remainder} {openingSpan closingSpan : SourceSpan}
    (opening : ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening)
    (closing : ExactTokenParses (.symbol .rightBrace) afterOpening closingSpan output) :
    CoreBlockTraceParses statementTrace policy source endByte input
      { span := SourceSpan.cover openingSpan closingSpan, value := [] } output [] :=
  .parsed openingSpan closingSpan opening (.close closingSpan closing) .nil

section OrderedEvents

variable {input afterOpening afterFirst beforeClose output : Remainder}
  {openingSpan closingSpan : SourceSpan} {first second : Statement}
  {firstEvent secondEvent : ParseDiagnostic}
  (opening : ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening)
  (insideFirst : afterOpening.cursor < afterOpening.endIndex)
  (notClosingFirst : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex
    afterOpening.cursor (.symbol .rightBrace))
  (firstParsed : statementTrace source endByte afterOpening first afterFirst [firstEvent])
  (firstProgress : afterOpening.cursor < afterFirst.cursor)
  (insideSecond : afterFirst.cursor < afterFirst.endIndex)
  (notClosingSecond : TokenKindAbsentAt afterFirst.tokens afterFirst.endIndex
    afterFirst.cursor (.symbol .rightBrace))
  (secondParsed : statementTrace source endByte afterFirst second beforeClose [secondEvent, secondEvent])
  (secondProgress : afterFirst.cursor < beforeClose.cursor)
  (closing : ExactTokenParses (.symbol .rightBrace) beforeClose closingSpan output)

include insideFirst notClosingFirst firstParsed firstProgress insideSecond
  notClosingSecond secondParsed secondProgress closing in
private theorem ordered_statement_events :
    CoreBlockItemsTraceParses statementTrace source endByte afterOpening
      [first, second] closingSpan output [firstEvent, secondEvent, secondEvent] :=
  .next insideFirst notClosingFirst firstParsed firstProgress
    (.next insideSecond notClosingSecond secondParsed secondProgress (.close closingSpan closing))

include opening insideFirst notClosingFirst firstParsed firstProgress insideSecond
  notClosingSecond secondParsed secondProgress closing in
/-- Both missing semicolons are reported only after every statement event.
The duplicate event from the second statement survives exactly twice. -/
theorem require_delays_all_tail_diagnostics
    (firstMissing : ¬ CoreBlockStatementTerminated first)
    (secondMissing : ¬ CoreBlockStatementTerminated second) :
    CoreBlockTraceParses statementTrace .require source endByte input
      { span := SourceSpan.cover openingSpan closingSpan, value := [first, second] } output
      [firstEvent, secondEvent, secondEvent,
        { span := first.span, kind := .constraintViolation .expressionRequiresSemicolon },
        { span := second.span, kind := .constraintViolation .expressionRequiresSemicolon }] := by
  exact .parsed openingSpan closingSpan opening
    (ordered_statement_events insideFirst notClosingFirst firstParsed firstProgress
      insideSecond notClosingSecond secondParsed secondProgress closing)
    (.cons (.missing firstMissing) (.lastRequired (.missing secondMissing)))

include opening insideFirst notClosingFirst firstParsed firstProgress insideSecond
  notClosingSecond secondParsed secondProgress closing in
/-- Allowing the final expression removes only its tail-validation report;
neither its statement events nor the earlier missing-semicolon report changes. -/
theorem allow_exempts_only_the_last_tail_check
    (firstMissing : ¬ CoreBlockStatementTerminated first) :
    CoreBlockTraceParses statementTrace .allow source endByte input
      { span := SourceSpan.cover openingSpan closingSpan, value := [first, second] } output
      [firstEvent, secondEvent, secondEvent,
        { span := first.span, kind := .constraintViolation .expressionRequiresSemicolon }] := by
  exact .parsed openingSpan closingSpan opening
    (ordered_statement_events insideFirst notClosingFirst firstParsed firstProgress
      insideSecond notClosingSecond secondParsed secondProgress closing)
    (.cons (.missing firstMissing) .lastAllowed)

end OrderedEvents

/-- Nonempty tail errors remain ordinary successes. Only an actually empty
total trace yields the original tail-validity condition. -/
theorem empty_trace_recovers_tail_validity
    {input output : Remainder} {body : Block}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output []) :
    CoreBlockTailsValid policy body.value := parsed.empty_trace_tailsValid rfl

end Solcore.Test.SyntaxCoreBlockTraceProperties
