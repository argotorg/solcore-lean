import Solcore.Syntax.Internal.BlockTrace
import Solcore.Syntax.Validity
import Solcore.Syntax.Parser.Internal.Completeness
import Solcore.Syntax.Parser.Internal.SignatureSoundness
import Solcore.Syntax.Parser.Internal.TermSoundness
import Solcore.Syntax.Parser.Internal.BlockTrace
import Solcore.Syntax.Parser.Internal.ContractOutcomeSoundness
import Solcore.Syntax.Parser.Correctness

/-!
# Core block tests

The core block and term parsers: block traces, cascades, isolation of block failures, and
exactness and completeness of core declarations and source files.
-/

section
-- leanmerge: from Solcore.Test.SyntaxCoreBlockCascadeProperties
/-! Normalization consumers retain the exact delayed body-validation suffix. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCoreBlockCascadeProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable
  {statementTrace : SourceId → Nat → Remainder → Statement → Remainder →
    List ParseDiagnostic → Prop}
  {policy : CoreBlockTailPolicy} {source : SourceId} {endByte : Nat}
  {input output : Remainder} {body : Block} {trace validationEvents : List ParseDiagnostic}
  (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace)
  (validated : CoreBlockTailsDiagnosticTrace policy body.value validationEvents)

example : ∃ openingSpan closingSpan afterOpening statementEvents,
    ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening ∧
    CoreBlockItemsTraceParses statementTrace source endByte afterOpening body.value
      closingSpan output statementEvents ∧
    body.span = SourceSpan.cover openingSpan closingSpan ∧
    trace = statementEvents ++ validationEvents := parsed.split_at_validation validated

example (text : String) (lexical : List SourceSpan) {kept : List ParseDiagnostic} :
    ParseDiagnosticCascadeFilters text lexical trace kept ↔
      ∃ statementEvents keptStatementEvents,
        trace = statementEvents ++ validationEvents ∧
        ParseDiagnosticCascadeFilters text lexical statementEvents keptStatementEvents ∧
        kept = keptStatementEvents ++ validationEvents :=
  parsed.cascadeFilters_iff validated text lexical

example {text : String} {lexical : List SourceSpan} {kept : List ParseDiagnostic}
    (filtered : ParseDiagnosticCascadeFilters text lexical trace kept) :
    ∃ leading, kept = leading ++ validationEvents :=
  parsed.normalized_validation_suffix validated filtered

include parsed in
/-- Every normalized result retains both identical validation occurrences in
their final positions, even if earlier statement reports were removed. -/
theorem repeated_validation_reports_remain_last
    {event : ParseDiagnostic}
    (checked : CoreBlockTailsDiagnosticTrace policy body.value [event, event])
    {text : String} {lexical : List SourceSpan} {kept : List ParseDiagnostic}
    (filtered : ParseDiagnosticCascadeFilters text lexical trace kept) :
    ∃ leading, kept = leading ++ [event, event] :=
  parsed.normalized_validation_suffix checked filtered

end Solcore.Test.SyntaxCoreBlockCascadeProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxCoreBlockRejectionTraceProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxCoreBlockTailCascadeProperties
/-! Consumers preserve the protected validation suffix after filtering an
arbitrary event prefix. Full reports remain ordered, including duplicates. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCoreBlockTailCascadeProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable {policy : CoreBlockTailPolicy} {statements : List Statement}
  {text : String} {lexical : List SourceSpan}

example {tailTrace events keptEvents : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements tailTrace)
    (filtered : ParseDiagnosticCascadeFilters text lexical events keptEvents) :
    ParseDiagnosticCascadeFilters text lexical
      (events ++ tailTrace) (keptEvents ++ tailTrace) :=
  parsed.append_cascadeFilters filtered

example {tailTrace events kept : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements tailTrace) :
    ParseDiagnosticCascadeFilters text lexical (events ++ tailTrace) kept ↔
      ∃ keptEvents, ParseDiagnosticCascadeFilters text lexical events keptEvents ∧
        kept = keptEvents ++ tailTrace := parsed.append_cascadeFilters_iff text lexical

/-- Suppressing the middle prefix event preserves both retained prefix
occurrences before both identical tail reports, without crossing the boundary. -/
theorem suppressed_middle_preserves_duplicate_groups
    {retainedEvent suppressedEvent tailEvent : ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements [tailEvent, tailEvent])
    (retained : ¬ ParseDiagnosticCascadeSuppresses text lexical retainedEvent)
    (suppressed : ParseDiagnosticCascadeSuppresses text lexical suppressedEvent) :
    ParseDiagnosticCascadeFilters text lexical
      [retainedEvent, suppressedEvent, retainedEvent, tailEvent, tailEvent]
      [retainedEvent, retainedEvent, tailEvent, tailEvent] :=
  parsed.append_cascadeFilters (.keep retained (.drop suppressed (.keep retained .nil)))

/-- Even deleting every repeated prefix event cannot remove either repeated
validation report. The iff forces every result to be this unchanged suffix. -/
theorem fully_suppressed_prefix_leaves_exact_tail
    {suppressedEvent tailEvent : ParseDiagnostic} {kept : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements [tailEvent, tailEvent])
    (suppressed : ParseDiagnosticCascadeSuppresses text lexical suppressedEvent) :
    ParseDiagnosticCascadeFilters text lexical
      [suppressedEvent, suppressedEvent, tailEvent, tailEvent] kept ↔
      kept = [tailEvent, tailEvent] := by
  have prefixFiltered : ParseDiagnosticCascadeFilters text lexical
      [suppressedEvent, suppressedEvent] [] := .drop suppressed (.drop suppressed .nil)
  constructor
  · intro filtered
    rcases (parsed.append_cascadeFilters_iff
      (events := [suppressedEvent, suppressedEvent]) text lexical).mp filtered with
      ⟨keptEvents, leading, same⟩
    rw [leading.output_unique prefixFiltered] at same
    exact same
  · intro same
    subst kept
    exact parsed.append_cascadeFilters prefixFiltered

end Solcore.Test.SyntaxCoreBlockTailCascadeProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxCoreBlockTailTraceProperties
/-! Grammar-only consumers of complete Core tail traces. Concrete ASTs keep
full statement spans, written order, duplicate events, and protected kinds. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCoreBlockTailTraceProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

section PublicApi

variable {statement : Statement} {policy : CoreBlockTailPolicy}
  {statements : List Statement} {left right : List ParseDiagnostic}

example (statement : Statement) :
    ∃ trace, CoreBlockStatementDiagnosticTrace statement trace :=
  CoreBlockStatementDiagnosticTrace.exists_trace statement

example (first : CoreBlockStatementDiagnosticTrace statement left)
    (second : CoreBlockStatementDiagnosticTrace statement right) : left = right :=
  first.output_unique second

example (parsed : CoreBlockStatementDiagnosticTrace statement left) :
    left = [] ↔ CoreBlockStatementTerminated statement := parsed.empty_iff

example (parsed : CoreBlockStatementDiagnosticTrace statement left)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical left left := parsed.cascadeFilters text lexical

example (policy : CoreBlockTailPolicy) (statements : List Statement) :
    ∃ trace, CoreBlockTailsDiagnosticTrace policy statements trace :=
  CoreBlockTailsDiagnosticTrace.exists_trace policy statements

example (first : CoreBlockTailsDiagnosticTrace policy statements left)
    (second : CoreBlockTailsDiagnosticTrace policy statements right) : left = right :=
  first.output_unique second

example (parsed : CoreBlockTailsDiagnosticTrace policy statements left) :
    left = [] ↔ CoreBlockTailsValid policy statements := parsed.empty_iff

example (parsed : CoreBlockTailsDiagnosticTrace policy statements left)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical left left := parsed.cascadeFilters text lexical

end PublicApi

private def byteSpan (first last : Nat) : SourceSpan := {
  source := { origin := .main, path := "core-tail-trace.sol" }
  startByte := first
  endByte := last
}

private def groupedName (start : Nat) (name : String) : Expr := {
  span := byteSpan start (start + 3)
  value := .group {
    span := byteSpan (start + 1) (start + 2)
    value := .identifier { span := byteSpan (start + 1) (start + 2), value := name }
  }
}

private def firstStatement : Statement := {
  span := byteSpan 0 3, value := .expression (groupedName 0 "a") false
}

private def middleStatement : Statement := {
  span := byteSpan 4 6
  value := .expression {
    span := byteSpan 4 5
    value := .identifier { span := byteSpan 4 5, value := "b" }
  } true
}

private def lastStatement : Statement := {
  span := byteSpan 7 10, value := .expression (groupedName 7 "c") false
}

private def missingSemicolon (first last : Nat) : ParseDiagnostic := {
  span := byteSpan first last, kind := .constraintViolation .expressionRequiresSemicolon
}

private theorem firstMissing :
    CoreBlockStatementDiagnosticTrace firstStatement [missingSemicolon 0 3] :=
  .missing (fun impossible => impossible)

private theorem middleClean : CoreBlockStatementDiagnosticTrace middleStatement [] :=
  .clean trivial

private theorem lastMissing :
    CoreBlockStatementDiagnosticTrace lastStatement [missingSemicolon 7 10] :=
  .missing (fun impossible => impossible)

/-- The allowed final group is exempt; the first whole group still needs a
semicolon, whereas the middle expression already has one. -/
theorem allow_three_statements :
    CoreBlockTailsDiagnosticTrace .allow
      [firstStatement, middleStatement, lastStatement] [missingSemicolon 0 3] :=
  .cons firstMissing (.cons middleClean .lastAllowed)

/-- Requiring the final semicolon reports the two full group-statement spans,
not just the inner names at bytes 1..2 and 8..9, in written order. -/
theorem require_three_statements :
    CoreBlockTailsDiagnosticTrace .require
      [firstStatement, middleStatement, lastStatement]
      [missingSemicolon 0 3, missingSemicolon 7 10] :=
  .cons firstMissing (.cons middleClean (.lastRequired lastMissing))

/-- Repeated AST occurrences produce repeated complete reports, not a set. -/
theorem repeated_statement_preserves_duplicates :
    CoreBlockTailsDiagnosticTrace .require
      [firstStatement, firstStatement, firstStatement]
      [missingSemicolon 0 3, missingSemicolon 0 3, missingSemicolon 0 3] :=
  .cons firstMissing (.cons firstMissing (.lastRequired firstMissing))

/-- Both statement spans meet the same-LF-line lexical suppression condition
at the invalid character's span, but neither constraint report can be dropped. -/
theorem same_line_lexical_error_preserves_constraints :
    LexicalSpanSuppresses "(a) b; (c) §" (byteSpan 11 13) (byteSpan 0 3) ∧
    LexicalSpanSuppresses "(a) b; (c) §" (byteSpan 11 13) (byteSpan 7 10) ∧
    ParseDiagnosticCascadeFilters "(a) b; (c) §" [byteSpan 11 13]
      [missingSemicolon 0 3, missingSemicolon 7 10]
      [missingSemicolon 0 3, missingSemicolon 7 10] := by
  refine ⟨⟨rfl, Or.inl ?_⟩, ⟨rfl, Or.inl ?_⟩,
    require_three_statements.cascadeFilters _ _⟩ <;> decide +kernel

/-- The old diagnostic-free predicate is recovered from the allowed singleton
trace, even though the very same statement fails a mandatory check. -/
theorem allowed_singleton_recovers_old_validity :
    CoreBlockTailsValid .allow [firstStatement] ∧
      ¬ CoreBlockStatementTerminated firstStatement :=
  ⟨(CoreBlockTailsDiagnosticTrace.empty_iff
    (CoreBlockTailsDiagnosticTrace.lastAllowed (last := firstStatement))).mp rfl,
    fun impossible => impossible⟩

/-- A non-expression needs no expression-semicolon report under either policy. -/
theorem nonexpression_is_silent :
    CoreBlockStatementDiagnosticTrace
      { span := byteSpan 4 10, value := .breakStmt } [] := .clean trivial

end Solcore.Test.SyntaxCoreBlockTailTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxCoreBlockTraceExactnessProperties
/-! Joint raw/isolated trace consumers expose the required statement laws and
retain distinct child byte boundaries, ordinary failures, and recovered events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCoreBlockTraceExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable
  {statementTrace : SourceId → Nat → Remainder → Statement → Remainder →
    List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}

example (statements : StatementTraceExactOutcomeSpec
    statementTrace statementRejects source endByte) :
    BlockTraceExactOutcomeSpec (CoreBlockTraceParses statementTrace policy)
      (CoreBlockTraceRejects statementTrace statementRejects policy) source endByte :=
  coreBlockTraceExactOutcomeSpec policy statements

example (statements : ∀ childEndByte,
    StatementTraceExactOutcomeSpec statementTrace statementRejects source childEndByte) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses (CoreBlockTraceParses statementTrace policy)
        (CoreBlockTraceRejects statementTrace statementRejects policy))
      (IsolatedBlockTraceRejects (CoreBlockTraceRejects statementTrace statementRejects policy))
      source endByte :=
  isolatedCoreBlockTraceExactOutcomeSpec policy statements

/-- A raw failure rules out a successful block with any proposed AST or trace. -/
theorem raw_rejection_excludes_every_success
    (statements : StatementTraceExactOutcomeSpec statementTrace statementRejects source endByte)
    {input rejected : Remainder} {report : ParseDiagnostic} {events : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected report events) :
    ¬ ∃ body output trace, CoreBlockTraceParses statementTrace policy source endByte
      input body output trace :=
  (coreBlockTraceExactOutcomeSpec policy statements).successRejectDisjoint rejection

/-- Once a captured raw failure is recovered, every isolated success has the
captured full span, parent resume point, and events followed by its report once. -/
theorem recovered_raw_block_result_is_fixed
    (statements : ∀ childEndByte,
      StatementTraceExactOutcomeSpec statementTrace statementRejects source childEndByte)
    {input childRejected output : Remainder} {capture : BalancedBlockCapture}
    {report : ParseDiagnostic} {events trace : List ParseDiagnostic} {body : Block}
    (captured : BalancedBlockCaptures input capture)
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source capture.endByte
      (capture.childRemainder input) childRejected report events)
    (parsed : IsolatedBlockTraceParses (CoreBlockTraceParses statementTrace policy)
      (CoreBlockTraceRejects statementTrace statementRejects policy) source endByte
      input body output trace) :
    body = { span := capture.span, value := [] } ∧
      output = capture.parentRemainder input ∧ trace = events ++ [report] :=
  (isolatedCoreBlockTraceExactOutcomeSpec policy statements).successResultUnique
    parsed (.recovered captured rejection)

end Solcore.Test.SyntaxCoreBlockTraceExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxCoreBlockTraceProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxCoreTermValidity
/-! External consumers for canonical recursive Core source-validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @Expr.ValidFor.mono
example := @Pattern.ValidFor.mono
example := @ForItem.ValidFor.mono
example := @Statement.ValidFor.mono
example := @CoreStatement.ValidForAt
example := @CoreStatement.ValidFor
example := @CoreExpr.ValidFor
example := @CorePattern.ValidFor
example := @CoreStatement.ValidFor.ofStatement
example := @CoreStatement.ValidFor.span_valid

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxIsolatedBlockTraceErasureProperties
/-! Independent erasure and repeated-isolation consumers. An outer successful
capture does not recommit a failure already recovered by an inner isolation. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxIsolatedBlockTraceErasureProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable
  {blockParses : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
    List ParseDiagnostic → Prop}
  {blockOrdinary : Remainder → Block → Remainder → Prop}
  {blockRejected : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat}

example
    (successErases : ∀ source endByte input body output trace,
      blockParses source endByte input body output trace → blockOrdinary input body output)
    (rejectionErases : ∀ source endByte input rejected diagnostic trace,
      blockRejects source endByte input rejected diagnostic trace → blockRejected input rejected)
    {input output : Remainder} {body : Block} {trace : List ParseDiagnostic}
    (parsed : IsolatedBlockTraceParses blockParses blockRejects source endByte
      input body output trace) :
    IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejected input body output :=
  parsed.ordinary successErases rejectionErases

example
    (rejectionErases : ∀ source endByte input rejected diagnostic trace,
      blockRejects source endByte input rejected diagnostic trace → blockRejected input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : IsolatedBlockTraceRejects blockRejects source endByte
      input rejected diagnostic trace) :
    IsolatedCoreBlockRejects blockRejected input rejected :=
  rejection.ordinary rejectionErases

/-- A child recovery is a success for its outer isolation. The inner captured
span is retained as the AST, while the outer capture sets the parent endpoint. -/
theorem nested_recovery_commits_report_once
    {input childRejected : Remainder} {outer inner : BalancedBlockCapture}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (outerCapture : BalancedBlockCaptures input outer)
    (innerCapture : BalancedBlockCaptures (outer.childRemainder input) inner)
    (rejection : blockRejects source inner.endByte
      (inner.childRemainder (outer.childRemainder input)) childRejected diagnostic trace) :
    IsolatedBlockTraceParses (IsolatedBlockTraceParses blockParses blockRejects)
      (IsolatedBlockTraceRejects blockRejects) source endByte input
      { span := inner.span, value := [] } (outer.parentRemainder input)
      (trace ++ [diagnostic]) :=
  .captured outerCapture (.recovered innerCapture rejection)

end Solcore.Test.SyntaxIsolatedBlockTraceErasureProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxIsolatedBlockTraceProperties
/-! Independent consumers of isolation trace exactness. Child and parent byte
boundaries remain separate, and captured failure is committed once after its events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxIsolatedBlockTraceProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable
  {blockParses : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
    List ParseDiagnostic → Prop}
  {source : SourceId} {parentEndByte : Nat}

example (innerOutcomes : ∀ childEndByte,
    BlockTraceExactOutcomeSpec blockParses blockRejects source childEndByte) :
    BlockTraceExactOutcomeSpec (IsolatedBlockTraceParses blockParses blockRejects)
      (IsolatedBlockTraceRejects blockRejects) source parentEndByte :=
  isolatedBlockTraceExactOutcomeSpec innerOutcomes

example (innerOutcomes : ∀ childEndByte,
    BlockTraceExactOutcomeSpec blockParses blockRejects source childEndByte)
    {input leftOutput rightOutput : Remainder} {left right : Block}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : IsolatedBlockTraceParses blockParses blockRejects source parentEndByte
      input left leftOutput leftTrace)
    (rightParsed : IsolatedBlockTraceParses blockParses blockRejects source parentEndByte
      input right rightOutput rightTrace) :
    left = right ∧ leftOutput = rightOutput ∧ leftTrace = rightTrace :=
  leftParsed.result_unique innerOutcomes rightParsed

example (innerOutcomes : BlockTraceExactOutcomeSpec blockParses blockRejects source parentEndByte)
    {input leftOutput rightOutput : Remainder}
    {leftReport rightReport : ParseDiagnostic} {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : IsolatedBlockTraceRejects blockRejects source parentEndByte
      input leftOutput leftReport leftTrace)
    (rightRejected : IsolatedBlockTraceRejects blockRejects source parentEndByte
      input rightOutput rightReport rightTrace) :
    leftOutput = rightOutput ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  leftRejected.result_unique innerOutcomes rightRejected

example (innerOutcomes : BlockTraceExactOutcomeSpec blockParses blockRejects source parentEndByte)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : IsolatedBlockTraceRejects blockRejects source parentEndByte
      input rejected diagnostic trace) :
    ¬ ∃ body output events, IsolatedBlockTraceParses blockParses blockRejects source parentEndByte
      input body output events :=
  rejection.disjoint_success innerOutcomes

/-- A child failure uses capture.endByte and becomes an exact empty-block
success at the parent's resume point, preserving duplicate earlier events. -/
theorem recovered_child_appends_once
    {input childRejected : Remainder} {capture : BalancedBlockCapture}
    {event diagnostic : ParseDiagnostic}
    (captured : BalancedBlockCaptures input capture)
    (rejected : blockRejects source capture.endByte (capture.childRemainder input)
      childRejected diagnostic [event, event]) :
    IsolatedBlockTraceParses blockParses blockRejects source parentEndByte input
      { span := capture.span, value := [] } (capture.parentRemainder input)
      [event, event, diagnostic] :=
  .recovered captured rejected

/-- Any competing successful derivation has this recovered AST, exact parent
resume point, and complete child trace followed by its one committed report. -/
theorem recovered_result_is_unique
    (innerOutcomes : ∀ childEndByte,
      BlockTraceExactOutcomeSpec blockParses blockRejects source childEndByte)
    {input childRejected output : Remainder} {capture : BalancedBlockCapture}
    {diagnostic : ParseDiagnostic} {trace events : List ParseDiagnostic} {body : Block}
    (captured : BalancedBlockCaptures input capture)
    (rejected : blockRejects source capture.endByte (capture.childRemainder input)
      childRejected diagnostic trace)
    (parsed : IsolatedBlockTraceParses blockParses blockRejects source parentEndByte
      input body output events) :
    body = { span := capture.span, value := [] } ∧
      output = capture.parentRemainder input ∧ events = trace ++ [diagnostic] :=
  parsed.result_unique innerOutcomes (.recovered captured rejected)

/-- Once capture exists, no external rejection escapes the isolation wrapper,
even without inner exactness or a successful child derivation. -/
theorem captured_cannot_escape_rejection
    {input rejected : Remainder} {capture : BalancedBlockCapture}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (captured : BalancedBlockCaptures input capture) :
    ¬ IsolatedBlockTraceRejects blockRejects source parentEndByte
      input rejected diagnostic trace := by
  intro rejection
  cases rejection with
  | direct absent childRejected => exact absent ⟨capture, captured⟩

end Solcore.Test.SyntaxIsolatedBlockTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCoreAuxiliaryCompletenessProperties
/-! Compile-time consumers for type, lambda parameter, and policy-preserving
raw and isolated block grammar correspondence. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreAuxiliaryCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @typeExpr_ordinary_success_iff
example := @typeExpr_ordinary_reject_iff
example := @lambdaParameter_ordinary_success_iff
example := @lambdaParameter_ordinary_reject_iff
example := @block_ordinary_success_iff
example := @block_ordinary_reject_iff
example := @isolatedCoreBlockPublic_ordinary_success_iff
example := @isolatedCoreBlockPublic_ordinary_reject_iff

example {input : State} (inputValid : input.ValidFor)
    {value : TypeExpr} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TypeExprOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, typeExpr input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (typeExpr_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.TypeExprRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, typeExpr input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (typeExpr_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : LambdaParameter} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.LambdaParameterOrdinaryParses
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
        input.declarativeRemainder value remainder) :
    ∃ output, lambdaParameter input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (lambdaParameter_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.LambdaParameterRejects
      DeclarativeGrammar.TypeExprRejects input.declarativeRemainder rejected) :
    ∃ failure output, lambdaParameter input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (lambdaParameter_ordinary_reject_iff inputValid).mp rejection

example (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {value : Block} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative
      input.declarativeRemainder value remainder) :
    ∃ output, block policy input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (block_ordinary_success_iff policy inputValid).mp parsed

example (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.CoreBlockPublicRejects policy.declarative
      input.declarativeRemainder rejected) :
    ∃ failure output, block policy input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (block_ordinary_reject_iff policy inputValid).mp rejection

example (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {value : Block} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses
      policy.declarative input.declarativeRemainder value remainder) :
    ∃ output, isolateBlock (block policy) input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (isolatedCoreBlockPublic_ordinary_success_iff policy inputValid).mp parsed

example (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.IsolatedCoreBlockPublicRejects
      policy.declarative input.declarativeRemainder rejected) :
    ∃ failure output, isolateBlock (block policy) input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (isolatedCoreBlockPublic_ordinary_reject_iff policy inputValid).mp rejection

end Solcore.Test.SyntaxParserCoreAuxiliaryCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCoreBlockClosingTraceProperties
/-! Independent tail checks and exact brace-closing diagnostic consumers. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreBlockClosingTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @closeCoreBlock_success_trace_sound
example := @closeCoreBlock_success_diagnostics_eq_of_trace
example := @closeCoreBlock_reject_iff_symbol
example := @closeCoreBlock_reject_reports
example := @closeCoreBlock_reject_reports_iff

example (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {body : Block} {remainder : Remainder} {trace : List ParseDiagnostic}
    (ordinary : ∃ closingSpan,
      ExactTokenParses (.symbol .rightBrace) input.declarativeRemainder closingSpan remainder ∧
      body = { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse })
    (checked : CoreBlockTailsDiagnosticTrace policy.declarative bodyRev.reverse trace) :
    ∃ output, closeCoreBlock opening policy bodyRev input = .ok body output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  (closeCoreBlock_trace_success_iff opening policy bodyRev).mp ⟨ordinary, checked⟩

example (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input output : State} {body : Block} {remainder : Remainder} {trace : List ParseDiagnostic}
    (result : closeCoreBlock opening policy bodyRev input = .ok body output)
    (after : output.declarativeRemainder = remainder)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    (∃ closingSpan,
      ExactTokenParses (.symbol .rightBrace) input.declarativeRemainder closingSpan remainder ∧
      body = { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse }) ∧
      CoreBlockTailsDiagnosticTrace policy.declarative bodyRev.reverse trace :=
  (closeCoreBlock_trace_success_iff opening policy bodyRev).mpr
    ⟨output, result, after, diagnostics⟩

example (first last : SourceSpan) (left right : Expr) :
    CoreBlockTailsDiagnosticTrace .allow
      [{ span := first, value := .expression left false },
        { span := last, value := .expression right false }]
      [{ span := first, kind := .constraintViolation .expressionRequiresSemicolon }] :=
  .cons (first := { span := first, value := .expression left false })
    (.missing (fun impossible => impossible)) .lastAllowed

example (opening : Token) {input : State} {closingSpan : SourceSpan} {remainder : Remainder}
    (first last : SourceSpan) (left right : Expr)
    (closing : ExactTokenParses (.symbol .rightBrace)
      input.declarativeRemainder closingSpan remainder) :
    ∃ output, closeCoreBlock opening .require
        [{ span := last, value := .expression right false },
          { span := first, value := .expression left false }] input = .ok {
          span := SourceSpan.cover opening.span closingSpan
          value := [{ span := first, value := .expression left false },
            { span := last, value := .expression right false }]
        } output ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++
        [{ span := first, kind := .constraintViolation .expressionRequiresSemicolon },
          { span := last, kind := .constraintViolation .expressionRequiresSemicolon }] :=
  (closeCoreBlock_trace_success_iff opening .require
    [{ span := last, value := .expression right false },
      { span := first, value := .expression left false }]).mp
    ⟨⟨closingSpan, closing, rfl⟩,
      .cons (first := { span := first, value := .expression left false })
      (.missing (fun impossible => impossible))
      (.lastRequired (.missing (fun impossible => impossible)))⟩

example (opening : Token) {input : State} {closingSpan : SourceSpan} {remainder : Remainder}
    (span : SourceSpan) (expression : Expr)
    (closing : ExactTokenParses (.symbol .rightBrace)
      input.declarativeRemainder closingSpan remainder) :
    ∃ output, closeCoreBlock opening .allow
        [{ span, value := .expression expression false }] input = .ok {
          span := SourceSpan.cover opening.span closingSpan
          value := [{ span, value := .expression expression false }]
        } output ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil, List.reverse_cons, List.reverse_nil, List.nil_append] using
    (closeCoreBlock_trace_success_iff opening .allow
      [{ span, value := .expression expression false }] (trace := [])).mp
      ⟨⟨closingSpan, closing, rfl⟩, .lastAllowed⟩

example (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {span : SourceSpan} {found : Option TokenKind}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .rightBrace))
    (current : CurrentInputAt input.file.id input.window.endByte input.declarativeRemainder span found) :
    closeCoreBlock opening policy bodyRev input = .reject
      { span, found, expected := { head := .symbol .rightBrace, tail := [] }, context := .statement }
      input :=
  (closeCoreBlock_reject_failure_iff opening policy bodyRev).mp ⟨absent, .reported current⟩

end Solcore.Test.SyntaxParserCoreBlockClosingTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCoreBlockExactnessProperties
/-! Compile-time consumers for conditional exact Core-block outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreBlockExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @CoreBlockItemsParses.result_unique
example := @CoreBlockOrdinaryParses.result_unique
example := @CoreBlockOrdinaryParses.value_unique
example := @CoreBlockItemsRejects.output_unique
example := @CoreBlockRejects.output_unique
example := @coreBlockExactOutcomeSpec
example := @coreBlockPublicExactOutcomeSpecOfStatementFuel
example := @IsolatedCoreBlockOrdinaryParses.value_unique
example := @IsolatedCoreBlockOrdinaryParses.result_unique
example := @IsolatedCoreBlockRejects.output_unique
example := @isolatedCoreBlockExactOutcomeSpec
example := @isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel
example := @block_exactOutcomeSpec_of_statementFuel
example := @block_success_result_unique_of_statementFuel
example := @block_reject_output_unique_of_statementFuel
example := @isolatedCoreBlockPublic_exactOutcomeSpec_of_statementFuel
example := @isolatedCoreBlockPublic_success_result_unique_of_statementFuel
example := @isolatedCoreBlockPublic_reject_output_unique_of_statementFuel

end Solcore.Test.SyntaxParserCoreBlockExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCoreBlockIsolationTraceProperties
/-! Isolated Core consumers expose only statement contracts and independent
block syntax. Captured recovery skips raw tail validation and commits once. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreBlockIsolationTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @isolatedCoreBlock_success_trace_sound
example := @isolatedCoreBlock_reject_trace_sound
example := @isolatedCoreBlock_success_trace_complete
example := @isolatedCoreBlock_reject_trace_complete
example := @isolatedCoreBlock_trace_success_iff
example := @isolatedCoreBlock_trace_reject_iff

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → Remainder → Statement → Remainder →
    List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  (successComplete : StatementTraceSuccessComplete statement statementTrace)
  (rejectComplete : StatementTraceRejectComplete statement statementRejects)
  (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)

include successComplete rejectComplete contextFrame in
/-- A captured raw rejection restores the parent endpoint and retains all
earlier events before one committed report, under either raw tail policy. -/
theorem captured_raw_rejection_has_exact_trace
    {input : State} {capture : BalancedBlockCapture} {childRejected : Remainder}
    {report : ParseDiagnostic} {events : List ParseDiagnostic}
    (captured : BalancedBlockCaptures input.declarativeRemainder capture)
    (rejected : CoreBlockTraceRejects statementTrace statementRejects policy.declarative
      input.file.id capture.endByte (capture.childRemainder input.declarativeRemainder)
      childRejected report events) :
    ∃ output, isolateBlock (coreBlock statement policy) input =
        .ok { span := capture.span, value := [] } output ∧
      output.declarativeRemainder = capture.parentRemainder input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ (events ++ [report]) :=
  isolatedCoreBlock_success_trace_complete successComplete rejectComplete contextFrame policy
    (.recovered captured rejected)

include successComplete rejectComplete contextFrame in
/-- A successful captured block preserves its independently described total
trace, including validation reports already appended by raw block closing. -/
theorem captured_raw_success_retains_complete_trace
    {input : State} {capture : BalancedBlockCapture} {childAfter : Remainder}
    {body : Block} {events : List ParseDiagnostic}
    (captured : BalancedBlockCaptures input.declarativeRemainder capture)
    (parsed : CoreBlockTraceParses statementTrace policy.declarative input.file.id
      capture.endByte (capture.childRemainder input.declarativeRemainder) body childAfter events) :
    ∃ output, isolateBlock (coreBlock statement policy) input = .ok body output ∧
      output.declarativeRemainder = capture.parentRemainder input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ events :=
  isolatedCoreBlock_success_trace_complete successComplete rejectComplete contextFrame policy
    (.captured captured parsed)

include successComplete rejectComplete contextFrame in
/-- Without a capture, raw rejection escapes with the report still separate
from its trace. No recovered report is introduced at this boundary. -/
theorem uncaptured_raw_rejection_keeps_report_separate
    {input : State} {after : Remainder} {report : ParseDiagnostic}
    {events : List ParseDiagnostic}
    (absent : BalancedBlockCaptureAbsentAt input.declarativeRemainder)
    (rejected : CoreBlockTraceRejects statementTrace statementRejects policy.declarative
      input.file.id input.window.endByte input.declarativeRemainder after report events) :
    ∃ failure output, isolateBlock (coreBlock statement policy) input = .reject failure output ∧
      output.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      output.diagnostics = input.diagnostics ++ events :=
  isolatedCoreBlock_reject_trace_complete successComplete rejectComplete contextFrame policy
    (.direct absent rejected)

end Solcore.Test.SyntaxParserCoreBlockIsolationTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCoreBlockRejectionTraceProperties
/-! Executable consumers with arbitrary statement contracts and existing
diagnostics. Ordinary rejection never starts delayed block-tail validation. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreBlockRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → Remainder → Statement → Remainder →
    List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}

example := @coreBlockItems_reject_trace_sound
example := @coreBlock_reject_trace_sound
example := @coreBlockItems_trace_reject_complete
example := @coreBlockItems_production_trace_reject_complete
example := @coreBlock_trace_reject_complete
example := @coreBlock_trace_reject_iff
example := @coreBlock_trace_reject_failure_iff

/-- An exhausted subwindow rejects before checking any prefix statement,
even when the selected policy requires its final expression's semicolon. -/
theorem exhausted_window_preserves_all_prior_events
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (bodyRev : List Statement) {input : State}
    (atEnd : input.window.endIndex ≤ input.cursor) :
    ∃ failure rejected, coreBlockItems statement opening .require
      (input.remainingCount + 1) bodyRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = input.declarativeRemainder ∧
      failure.toDiagnostic = {
        span := { source := input.file.id, startByte := input.window.endByte, endByte := input.window.endByte },
        kind := .unexpected none { head := .symbol .rightBrace, tail := [] } .statement } ∧
      rejected.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using
    coreBlockItems_production_trace_reject_complete successComplete rejectComplete contextFrame
      opening .require bodyRev
      (SyntaxCoreBlockRejectionTraceProperties.missing_close_uses_window_endpoint atEnd)

/-- The original input's diagnostic list can be nonempty; every specified
event from a rejecting statement is appended once, without a final report. -/
theorem rejecting_statement_appends_only_its_events
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {remainder : Remainder} {diagnostic : ParseDiagnostic}
    {first second : ParseDiagnostic}
    (inside : input.cursor < input.window.endIndex)
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .rightBrace))
    (rejection : statementRejects input.file.id input.window.endByte input.declarativeRemainder
      remainder diagnostic [first, second, first]) :
    ∃ failure rejected, coreBlockItems statement opening policy (input.remainingCount + 1)
      bodyRev input = .reject failure rejected ∧ rejected.declarativeRemainder = remainder ∧
      failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ [first, second, first] :=
  coreBlockItems_production_trace_reject_complete successComplete rejectComplete contextFrame
    opening policy bodyRev (.statementRejected inside absent rejection)

/-- A raw rejection under one tail policy supplies exactly the same failure,
remainder, and appended diagnostics under the other policy. -/
theorem changing_tail_policy_preserves_rejection
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    {input rejected : State} {failure : Failure}
    (result : coreBlock statement .allow input = .reject failure rejected) :
    ∃ required, coreBlock statement .require input = .reject failure required ∧
      required.declarativeRemainder = rejected.declarativeRemainder ∧
      required.diagnostics = rejected.diagnostics := by
  rcases coreBlock_reject_trace_sound successSound rejectSound contextFrame .allow result with
    ⟨trace, rejection, diagnostics⟩
  rcases (coreBlock_trace_reject_failure_iff successSound rejectSound successComplete
      rejectComplete contextFrame .require).mp (rejection.withPolicy .require) with
    ⟨required, requiredResult, remainder, requiredDiagnostics⟩
  exact ⟨required, requiredResult, remainder, requiredDiagnostics.trans diagnostics.symm⟩

end Solcore.Test.SyntaxParserCoreBlockRejectionTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCoreBlockTraceProperties
/-! Conditional raw-block execution consumers. Existing reverse prefixes are
checked once at closing; only fresh statements contribute statement events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreBlockTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → Remainder → Statement →
    Remainder → List ParseDiagnostic → Prop}

example := @coreBlockItems_success_trace_sound
example := @coreBlock_success_trace_sound
example := @coreBlockItems_trace_success_complete
example := @coreBlockItems_production_trace_success_complete
example := @coreBlock_trace_success_complete

/-- Both directions expose their statement assumptions, and incoming diagnostic
events remain unrestricted. This is not a concrete Core-statement trace claim. -/
theorem exact_success_under_statement_contracts
    (sound : StatementTraceSuccessSound statement statementTrace)
    (complete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)
    {input : State} {body : Block} {after : Remainder} {trace : List ParseDiagnostic} :
    CoreBlockTraceParses statementTrace policy.declarative input.file.id input.window.endByte
      input.declarativeRemainder body after trace ↔
    ∃ output, coreBlock statement policy input = .ok body output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  coreBlock_trace_success_iff sound complete contextFrame policy

/-- Successful empty blocks preserve all prior events under both tail policies. -/
theorem empty_block_retains_prior_events
    (complete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)
    {input : State} {afterOpening after : Remainder} {openingSpan closingSpan : SourceSpan}
    (opening : ExactTokenParses (.symbol .leftBrace)
      input.declarativeRemainder openingSpan afterOpening)
    (closing : ExactTokenParses (.symbol .rightBrace) afterOpening closingSpan after) :
    ∃ output, coreBlock statement policy input = .ok {
        span := SourceSpan.cover openingSpan closingSpan, value := []
      } output ∧ output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using
    coreBlock_trace_success_complete complete contextFrame policy
      (.parsed openingSpan closingSpan opening (.close closingSpan closing) .nil)

/-- Two accumulated statements are reversed back into source order, then one
fresh statement is appended. Its duplicate events precede the three distinct
tail-check events; accumulated statements contribute no replayed parse events. -/
theorem reverse_prefix_is_checked_once_after_fresh_events
    (complete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (opening : Token)
    {input : State} {beforeClose after : Remainder} {closingSpan : SourceSpan}
    (first second fresh : Statement) (event : ParseDiagnostic)
    (inside : input.cursor < input.window.endIndex)
    (notClosing : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.symbol .rightBrace))
    (freshParsed : statementTrace input.file.id input.window.endByte
      input.declarativeRemainder fresh beforeClose [event, event])
    (progress : input.cursor < beforeClose.cursor)
    (closing : ExactTokenParses (.symbol .rightBrace) beforeClose closingSpan after)
    (firstMissing : ¬ CoreBlockStatementTerminated first)
    (secondMissing : ¬ CoreBlockStatementTerminated second)
    (freshMissing : ¬ CoreBlockStatementTerminated fresh) :
    ∃ output, coreBlockItems statement opening .require
        (input.remainingCount + 1) [second, first] input = .ok {
          span := SourceSpan.cover opening.span closingSpan, value := [first, second, fresh]
        } output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ [event, event,
        { span := first.span, kind := .constraintViolation .expressionRequiresSemicolon },
        { span := second.span, kind := .constraintViolation .expressionRequiresSemicolon },
        { span := fresh.span, kind := .constraintViolation .expressionRequiresSemicolon }] := by
  have items : CoreBlockItemsTraceParses statementTrace input.file.id input.window.endByte
      input.declarativeRemainder [fresh] closingSpan after [event, event] :=
    .next inside notClosing freshParsed progress (.close closingSpan closing)
  have validated : CoreBlockTailsDiagnosticTrace .require
      ([second, first].reverse ++ [fresh]) [
        { span := first.span, kind := .constraintViolation .expressionRequiresSemicolon },
        { span := second.span, kind := .constraintViolation .expressionRequiresSemicolon },
        { span := fresh.span, kind := .constraintViolation .expressionRequiresSemicolon }] :=
    .cons (.missing firstMissing) (.cons (.missing secondMissing) (.lastRequired (.missing freshMissing)))
  exact coreBlockItems_production_trace_success_complete complete contextFrame
    opening .require [second, first] items validated

/-- The allow policy exempts only the fresh final expression's tail report.
The previous expression still reports after the fresh statement's own event. -/
theorem allow_preserves_prior_tail_error_after_fresh_event
    (complete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (opening : Token)
    {input : State} {beforeClose after : Remainder} {closingSpan : SourceSpan}
    (earlier fresh : Statement) (event : ParseDiagnostic)
    (inside : input.cursor < input.window.endIndex)
    (notClosing : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.symbol .rightBrace))
    (freshParsed : statementTrace input.file.id input.window.endByte
      input.declarativeRemainder fresh beforeClose [event])
    (progress : input.cursor < beforeClose.cursor)
    (closing : ExactTokenParses (.symbol .rightBrace) beforeClose closingSpan after)
    (earlierMissing : ¬ CoreBlockStatementTerminated earlier) :
    ∃ output, coreBlockItems statement opening .allow
        (input.remainingCount + 1) [earlier] input = .ok {
          span := SourceSpan.cover opening.span closingSpan, value := [earlier, fresh]
        } output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ [event,
        { span := earlier.span, kind := .constraintViolation .expressionRequiresSemicolon }] :=
  coreBlockItems_production_trace_success_complete complete contextFrame opening .allow [earlier]
    (.next inside notClosing freshParsed progress (.close closingSpan closing))
    (.cons (.missing earlierMissing) .lastAllowed)

end Solcore.Test.SyntaxParserCoreBlockTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCoreDeclarationExactnessProperties
/-! External consumers for unconditional Core declaration exactness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreDeclarationExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeclarativeGrammar.functionDeclExactOutcomeSpec
example := @DeclarativeGrammar.constructorDeclExactOutcomeSpec
example := @DeclarativeGrammar.fallbackDeclExactOutcomeSpec
example := @DeclarativeGrammar.implMethodExactOutcomeSpec
example := @DeclarativeGrammar.implBodyExactOutcomeSpec
example := @DeclarativeGrammar.implDeclExactOutcomeSpec
example := @DeclarativeGrammar.contractFieldPublicExactOutcomeSpec
example := @DeclarativeGrammar.contractMemberCoreExactOutcomeSpec
example := @DeclarativeGrammar.contractMemberExactOutcomeSpec
example := @DeclarativeGrammar.contractBodyExactOutcomeSpec
example := @DeclarativeGrammar.contractDeclExactOutcomeSpec

example := @functionDecl_exactOutcomeSpec
example := @functionDecl_success_result_unique
example := @functionDecl_reject_output_unique
example := @constructorDecl_exactOutcomeSpec
example := @constructorDecl_success_result_unique
example := @constructorDecl_reject_output_unique
example := @fallbackDecl_exactOutcomeSpec
example := @fallbackDecl_success_result_unique
example := @fallbackDecl_reject_output_unique
example := @ImplInternals.implMethod_exactOutcomeSpec
example := @ImplInternals.implMethod_success_result_unique
example := @ImplInternals.implMethod_reject_output_unique
example := @ImplInternals.implBody_exactOutcomeSpec
example := @ImplInternals.implBody_success_result_unique
example := @ImplInternals.implBody_reject_output_unique
example := @implDecl_exactOutcomeSpec
example := @implDecl_success_result_unique
example := @implDecl_reject_output_unique
example := @ContractInternals.contractFieldPublic_exactOutcomeSpec
example := @ContractInternals.contractFieldPublic_success_result_unique
example := @ContractInternals.contractFieldPublic_reject_output_unique
example := @ContractInternals.contractMemberCore_exactOutcomeSpec
example := @ContractInternals.contractMemberCore_success_result_unique_unconditional
example := @ContractInternals.contractMemberCore_reject_output_unique_unconditional
example := @ContractInternals.contractMemberWithAttribute_exactOutcomeSpec
example := @ContractInternals.contractMemberWithAttribute_success_result_unique
example := @ContractInternals.contractMemberWithAttribute_reject_output_unique
example := @ContractInternals.contractBody_exactOutcomeSpec
example := @ContractInternals.contractBody_success_result_unique
example := @ContractInternals.contractBody_reject_output_unique
example := @contractDecl_exactOutcomeSpec
example := @contractDecl_success_result_unique
example := @contractDecl_reject_output_unique

example (location : FunctionLocation)
    {input leftOutput rightOutput : State} {left right : FunctionDecl}
    (leftResult : functionDecl location input = .ok left leftOutput)
    (rightResult : functionDecl location input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  functionDecl_success_result_unique location leftResult rightResult

example {input leftOutput rightOutput : State}
    {left right : ImplInternals.ImplBody}
    (leftResult : ImplInternals.implBody input = .ok left leftOutput)
    (rightResult : ImplInternals.implBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  ImplInternals.implBody_success_result_unique leftResult rightResult

example {input leftOutput rightOutput : State} {left right : ContractField}
    (leftResult : ContractInternals.contractField expression input =
      .ok left leftOutput)
    (rightResult : ContractInternals.contractField expression input =
      .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  ContractInternals.contractFieldPublic_success_result_unique
    leftResult rightResult

example {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractDecl input = .reject leftFailure leftOutput)
    (rightResult : contractDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractDecl_reject_output_unique leftResult rightResult

end Solcore.Test.SyntaxParserCoreDeclarationExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCoreSourceFileOrdinarySoundnessProperties
/-! External consumers for concrete ordinary Core-file grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreSourceFileOrdinarySoundnessProperties

open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @CoreTopItemOrdinaryParses
example := @CoreSourceFileOrdinaryParses
example := @CoreSourceFileOrdinaryParsesFromStart
example := @CoreSourceFileOrdinaryParses.output_atEnd

example := @FileInternals.sourceFile_success_coreOrdinary_sound
example := @FileInternals.sourceFile_success_coreOrdinary_sound_toEnd
example := @FileInternals.sourceFile_success_coreOrdinary_sound_and_validFor
example := @parseLexed_ok_coreOrdinary_sound
example := @parseLexed_ok_coreOrdinary_sound_and_validFor
example := @parse_ok_coreOrdinary_sound
example := @parse_ok_coreOrdinary_sound_and_validFor

example {file : Solcore.Syntax.SourceFile}
    {tokens : List Solcore.Syntax.Token}
    {comments : List Solcore.Syntax.Comment}
    {parsedFile : Solcore.Syntax.ParsedFile}
    (parsed : CoreSourceFileOrdinaryParsesFromStart file tokens comments
      parsedFile) :
    CoreSourceFileOrdinaryParses file comments {
      tokens := tokens.toArray
      endIndex := tokens.length
      cursor := 0
    } parsedFile {
      tokens := tokens.toArray
      endIndex := tokens.length
      cursor := tokens.length
    } :=
  parsed

example {file : Solcore.Syntax.SourceFile}
    {output : Solcore.Syntax.ParseOutput}
    (diagnosticFree : output.DiagnosticFree)
    (result : parse file = .ok output) :
    CoreSourceFileOrdinaryParses file output.parsed.comments {
      tokens := output.tokens.toArray
      endIndex := output.tokens.length
      cursor := 0
    } output.parsed {
      tokens := output.tokens.toArray
      endIndex := output.tokens.length
      cursor := output.tokens.length
    } :=
  parse_ok_coreOrdinary_sound diagnosticFree result

end Solcore.Test.SyntaxParserCoreSourceFileOrdinarySoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCoreTermExactnessProperties
/-! External consumers of unconditional exact Core terms and block boundaries. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreTermExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example (fuel : Nat) : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel) :=
  TermInternals.coreExpressionWithFuel_exactOutcomeSpec fuel

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.CoreExpressionOrdinaryParses
    DeclarativeGrammar.CoreExpressionPublicRejects :=
  expression_exactOutcomeSpec

-- Compare an executable success with any independently derived grammar result.
example {input output : State} {actual expected : Expr}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : expression input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  expression_exactOutcomeSpec.successResultUnique
    (expression_success_ordinary_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : expression input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  expression_exactOutcomeSpec.rejectOutputUnique
    (expression_reject_ordinary_sound result) expectedRejected

example := @TermInternals.coreExpressionWithFuel_success_result_unique
example := @TermInternals.coreExpressionWithFuel_reject_output_unique
example := @expression_success_result_unique
example := @expression_reject_output_unique

example (fuel : Nat) : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.CorePatternOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.CorePatternRejectsWithFuel fuel) :=
  TermInternals.corePatternWithFuel_exactOutcomeSpec fuel

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.CorePatternOrdinaryParses
    DeclarativeGrammar.CorePatternPublicRejects :=
  pattern_exactOutcomeSpec

-- Compare an executable success with any independently derived grammar result.
example {input output : State} {actual expected : Pattern}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : pattern input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.CorePatternOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  pattern_exactOutcomeSpec.successResultUnique
    (pattern_success_ordinary_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : pattern input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.CorePatternPublicRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  pattern_exactOutcomeSpec.rejectOutputUnique
    (pattern_reject_ordinary_sound result) expectedRejected

example := @TermInternals.corePatternWithFuel_success_result_unique
example := @TermInternals.corePatternWithFuel_reject_output_unique
example := @pattern_success_result_unique
example := @pattern_reject_output_unique

example (fuel : Nat) : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel) :=
  TermInternals.coreStatementWithFuel_exactOutcomeSpec fuel

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.CoreStatementOrdinaryParses
    DeclarativeGrammar.CoreStatementPublicRejects :=
  statement_exactOutcomeSpec

-- Compare an executable success with any independently derived grammar result.
example {input output : State} {actual expected : Statement}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : statement input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.CoreStatementOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  statement_exactOutcomeSpec.successResultUnique
    (statement_success_ordinary_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : statement input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.CoreStatementPublicRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  statement_exactOutcomeSpec.rejectOutputUnique
    (statement_reject_ordinary_sound result) expectedRejected

example := @TermInternals.coreStatementWithFuel_success_result_unique
example := @TermInternals.coreStatementWithFuel_reject_output_unique
example := @statement_success_result_unique
example := @statement_reject_output_unique

example (policy : TailExpressionPolicy) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative)
      (DeclarativeGrammar.CoreBlockPublicRejects policy.declarative) :=
  block_exactOutcomeSpec policy

example (policy : TailExpressionPolicy)
    {input output : State} {actual expected : Block}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : block policy input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.CoreBlockPublicOrdinaryParses
      policy.declarative input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (block_exactOutcomeSpec policy).successResultUnique
    (block_success_ordinary_sound policy result) expectedParsed

example (policy : TailExpressionPolicy)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : block policy input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.CoreBlockPublicRejects
      policy.declarative input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (block_exactOutcomeSpec policy).rejectOutputUnique
    (block_reject_ordinary_sound policy result) expectedRejected

example := @block_success_result_unique
example := @block_reject_output_unique

example (policy : TailExpressionPolicy) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses policy.declarative)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects policy.declarative) :=
  isolatedCoreBlockPublic_exactOutcomeSpec policy

example (policy : TailExpressionPolicy)
    {input output : State} {actual expected : Block}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : isolateBlock (block policy) input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses
      policy.declarative input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (isolatedCoreBlockPublic_exactOutcomeSpec policy).successResultUnique
    (isolatedCoreBlockPublic_success_ordinary_sound policy result) expectedParsed

example (policy : TailExpressionPolicy)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : isolateBlock (block policy) input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.IsolatedCoreBlockPublicRejects
      policy.declarative input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (isolatedCoreBlockPublic_exactOutcomeSpec policy).rejectOutputUnique
    (isolatedCoreBlockPublic_reject_ordinary_sound policy result) expectedRejected

example := @isolatedCoreBlockPublic_success_result_unique
example := @isolatedCoreBlockPublic_reject_output_unique

end Solcore.Test.SyntaxParserCoreTermExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCoreTermPublicCompletenessProperties
/-! Compile-time consumers of exact ordinary grammar correspondence. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreTermPublicCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @ordinary_success_iff_exists_ok
example := @ordinary_reject_iff_exists_reject
example := @expression_ordinary_success_iff
example := @expression_ordinary_reject_iff
example := @pattern_ordinary_success_iff
example := @pattern_ordinary_reject_iff
example := @statement_ordinary_success_iff
example := @statement_ordinary_reject_iff

example {input : State} (inputValid : input.ValidFor)
    {value : Expr} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, expression input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (expression_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, expression input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (expression_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : Pattern} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.CorePatternOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, pattern input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (pattern_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.CorePatternPublicRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, pattern input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (pattern_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : Statement} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.CoreStatementOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, statement input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (statement_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.CoreStatementPublicRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, statement input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (statement_ordinary_reject_iff inputValid).mp rejection

end Solcore.Test.SyntaxParserCoreTermPublicCompletenessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserIsolatedBlockDiagnosticTraceProperties
/-! Consumers of executable isolation laws, preserving order and duplicates. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserIsolatedBlockDiagnosticTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @State.mergeDiagnostics_diagnostics_eq_append
example := @isolateBlock_captured_success_iff
example := @isolateBlock_captured_success_trace_cases
example := @isolateBlock_captured_ne_reject

example (input : State) (captured : BlockInternals.CapturedBlock) :
    (input.enterWindow input.cursor captured.window).diagnostics = [] ∧
      (input.enterWindow input.cursor captured.window).file = input.file ∧
      (input.enterWindow input.cursor captured.window).tokens = input.tokens ∧
      (input.enterWindow input.cursor captured.window).cursor = input.cursor ∧
      (input.enterWindow input.cursor captured.window).window = captured.window :=
  ⟨State.enterWindow_diagnostics_eq_nil _ _ _, rfl, rfl, rfl, rfl⟩

example {parser : Parser Block} {input rejected : State} {failure : Failure}
    (notCaptured : BlockInternals.captureBlock? input = none)
    (childResult : parser input = .reject failure rejected) :
    isolateBlock parser input = .reject failure rejected :=
  (isolateBlock_eq_of_no_capture parser notCaptured).trans childResult

example {parser : Parser Block} {input output : State} {body : Block}
    (notCaptured : BlockInternals.captureBlock? input = none)
    (childResult : parser input = .ok body output) :
    isolateBlock parser input = .ok body output :=
  (isolateBlock_eq_of_no_capture parser notCaptured).trans childResult

example {parser : Parser Block} {input childAfter : State} {body : Block}
    {captured : BlockInternals.CapturedBlock} {prior events : List ParseDiagnostic}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .ok body childAfter)
    (priorEq : input.diagnostics = prior) (eventsEq : childAfter.diagnostics = events) :
    ∃ output, isolateBlock parser input = .ok body output ∧
      output.diagnostics = prior ++ events := by
  have traced := isolateBlock_captured_success_trace capture childResult
  exact ⟨_, traced.1, by simpa only [priorEq, eventsEq] using traced.2⟩

example {parser : Parser Block} {input childAfter : State} {failure : Failure}
    {captured : BlockInternals.CapturedBlock} {prior events : List ParseDiagnostic}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter)
    (priorEq : input.diagnostics = prior) (eventsEq : childAfter.diagnostics = events) :
    ∃ output, isolateBlock parser input = .ok { span := captured.span, value := [] } output ∧
      output.diagnostics = prior ++ events ++ [failure.toDiagnostic] := by
  have traced := isolateBlock_captured_reject_trace capture childResult
  exact ⟨_, traced.1, by simpa only [priorEq, eventsEq] using traced.2⟩

example {parser : Parser Block} {input childAfter : State} {failure : Failure}
    {captured : BlockInternals.CapturedBlock} (prior event : ParseDiagnostic)
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter)
    (priorEq : input.diagnostics = [prior])
    (eventsEq : childAfter.diagnostics = [event, event]) :
    ∃ output, isolateBlock parser input = .ok { span := captured.span, value := [] } output ∧
      output.diagnostics = [prior, event, event, failure.toDiagnostic] := by
  have traced := isolateBlock_captured_reject_trace capture childResult
  exact ⟨_, traced.1, by simpa only [priorEq, eventsEq,
    List.cons_append, List.nil_append] using traced.2⟩

example {parser : Parser Block} {input childAfter : State} {failure : Failure}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter)
    (priorEq : input.diagnostics = [failure.toDiagnostic])
    (eventsEq : childAfter.diagnostics = [failure.toDiagnostic]) :
    ∃ output, isolateBlock parser input = .ok { span := captured.span, value := [] } output ∧
      output.diagnostics = [failure.toDiagnostic, failure.toDiagnostic, failure.toDiagnostic] := by
  have traced := isolateBlock_captured_reject_trace capture childResult
  exact ⟨_, traced.1, by simpa only [priorEq, eventsEq,
    List.cons_append, List.nil_append] using traced.2⟩

example {parser : Parser Block} {input : State} {error : ParserInvariantError}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .invariant error) :
    isolateBlock parser input = .invariant error :=
  (isolateBlock_captured_invariant_iff capture).mpr childResult

example {parser : Parser Block} {input : State} {error : ParserInvariantError}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (result : isolateBlock parser input = .invariant error) :
    parser (input.enterWindow input.cursor captured.window) = .invariant error :=
  (isolateBlock_captured_invariant_iff capture).mp result

example {parser : Parser Block} {input output : State} {body : Block}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (result : isolateBlock parser input = .ok body output) :
    output.file = input.file ∧ output.tokens = input.tokens ∧
      output.window = input.window ∧ output.cursor = captured.window.endIndex :=
  isolateBlock_captured_success_frame capture result

example {parser : Parser Block} {input output : State} {body : Block}
    {captured : BlockInternals.CapturedBlock} {nextToken : Token}
    (capture : BlockInternals.captureBlock? input = some captured)
    (result : isolateBlock parser input = .ok body output)
    (inside : captured.window.endIndex < input.window.endIndex)
    (following : input.tokens[captured.window.endIndex]? = some nextToken) :
    output.peek? = some nextToken := by
  rcases isolateBlock_captured_success_frame capture result with
    ⟨_, tokensEq, windowEq, cursorEq⟩
  simp only [State.peek?, tokensEq, windowEq, cursorEq, inside, if_true, following]

end Solcore.Test.SyntaxParserIsolatedBlockDiagnosticTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserIsolatedBlockTraceProperties
/-! Conditional isolation-trace consumers. Inner contracts are visible and no
example asserts that the concrete Core parser already has a full trace grammar.
All parent diagnostics and inner/parent byte boundaries remain unrestricted. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserIsolatedBlockTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {parser : Parser Block}
  {blockParses : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  (successSound : BlockTraceSuccessSound parser blockParses)
  (rejectSound : BlockTraceRejectSound parser blockRejects)
  (successComplete : BlockTraceSuccessComplete parser blockParses)
  (rejectComplete : BlockTraceRejectComplete parser blockRejects)

example : BlockTraceSuccessSound (isolateBlock parser)
    (IsolatedBlockTraceParses blockParses blockRejects) :=
  isolateBlock_success_trace_sound successSound rejectSound

example : BlockTraceRejectSound (isolateBlock parser)
    (IsolatedBlockTraceRejects blockRejects) :=
  isolateBlock_reject_trace_sound rejectSound

example : BlockTraceSuccessComplete (isolateBlock parser)
    (IsolatedBlockTraceParses blockParses blockRejects) :=
  isolateBlock_success_trace_complete successComplete rejectComplete

example : BlockTraceRejectComplete (isolateBlock parser)
    (IsolatedBlockTraceRejects blockRejects) :=
  isolateBlock_reject_trace_complete rejectComplete

example {input : State} {body : Block} {after : Remainder} {trace : List ParseDiagnostic} :
    IsolatedBlockTraceParses blockParses blockRejects input.file.id input.window.endByte
      input.declarativeRemainder body after trace ↔
      ∃ output, isolateBlock parser input = .ok body output ∧
        output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_trace_success_iff successSound rejectSound successComplete rejectComplete

example {input : State} {after : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    IsolatedBlockTraceRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
      ∃ failure output, isolateBlock parser input = .reject failure output ∧
        output.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_trace_reject_iff rejectSound rejectComplete

include successSound rejectSound in
/-- Soundness guarantees some complete suffix for every success, even before
any trace is proposed. Nonempty prior diagnostics do not invalidate the claim. -/
theorem every_success_has_an_independent_suffix
    {input output : State} {body : Block}
    (result : isolateBlock parser input = .ok body output) :
    ∃ trace, IsolatedBlockTraceParses blockParses blockRejects
      input.file.id input.window.endByte input.declarativeRemainder body
      output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_success_trace_sound successSound rejectSound result

include successComplete rejectComplete in
/-- The captured child uses the closing brace's byte endpoint, not the parent
window endpoint. Its own final cursor does not determine the resumed parent. -/
theorem captured_success_uses_child_context
    {input : State} {capture : BalancedBlockCapture} {childAfter : Remainder}
    {body : Block} {trace : List ParseDiagnostic}
    (captured : BalancedBlockCaptures input.declarativeRemainder capture)
    (bodyParsed : blockParses input.file.id capture.endByte
      (capture.childRemainder input.declarativeRemainder) body childAfter trace) :
    ∃ output, isolateBlock parser input = .ok body output ∧
      output.declarativeRemainder = capture.parentRemainder input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_success_trace_complete successComplete rejectComplete (.captured captured bodyParsed)

include successComplete rejectComplete in
/-- Ordinary child rejection contributes the exact report once after child
events, restores the complete parent frame, and returns only an empty block. -/
theorem captured_rejection_restores_parent_and_commits_once
    {input : State} {capture : BalancedBlockCapture} {childAfter : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (captured : BalancedBlockCaptures input.declarativeRemainder capture)
    (bodyRejected : blockRejects input.file.id capture.endByte
      (capture.childRemainder input.declarativeRemainder) childAfter diagnostic trace) :
    ∃ output, isolateBlock parser input = .ok { span := capture.span, value := [] } output ∧
      output.declarativeRemainder = capture.parentRemainder input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) ∧
      output.file = input.file ∧ output.tokens = input.tokens ∧
      output.window = input.window ∧ output.cursor = capture.endIndex := by
  rcases isolateBlock_success_trace_complete successComplete rejectComplete
      (.recovered captured bodyRejected) with ⟨output, result, remainderEq, traceEq⟩
  rcases BlockInternals.captureBlock?_complete captured with
    ⟨executableCapture, captureResult, _, endIndexEq, _⟩
  have frame := isolateBlock_captured_success_frame captureResult result
  exact ⟨output, result, remainderEq, traceEq, frame.1, frame.2.1,
    frame.2.2.1, frame.2.2.2.trans endIndexEq⟩

include rejectComplete in
/-- With no balanced capture, a rejection escapes with the child's report
still uncommitted; no singleton is added to the preceding diagnostic suffix. -/
theorem uncaptured_rejection_preserves_uncommitted_report
    {input : State} {after : Remainder} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (absent : BalancedBlockCaptureAbsentAt input.declarativeRemainder)
    (bodyRejected : blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace) :
    ∃ failure output, isolateBlock parser input = .reject failure output ∧
      output.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_reject_trace_complete rejectComplete (.direct absent bodyRejected)

end Solcore.Test.SyntaxParserIsolatedBlockTraceProperties
end
