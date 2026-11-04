import Solcore.Syntax.Parser.DelimitedNoTrailingRejectionTraceCorrespondenceProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingRejectionTraceProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties
import Solcore.Syntax.Parser.DelimitedTrailingTraceContextProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceProtectionProperties
import Solcore.Syntax.Parser
import Solcore.Syntax.Parser.SourceFileBoundaryStopTraceProperties
import Solcore.Syntax.Parser.CertifiedParseProperties
import Solcore.Syntax.Parser.CompleteOutputProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingExactnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingTraceContextProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceExactnessProperties
import Solcore.Syntax.Parser.DelimitedNonemptyProperties
import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.DelimitedSoundnessProperties
import Solcore.Syntax.Parser.SelectorNameSoundnessProperties
import Solcore.Syntax.Parser.DelimitedTotalityProperties
import Solcore.Syntax.Parser.Operator
import Solcore.Syntax.Parser.SourceFileSingleRecoveryTraceProperties
import Solcore.Syntax.Parser.SourceFileSingleSuccessTraceProperties
import Solcore.Syntax.Parser.SyntaxExactnessProperties
import Solcore

/-!
# Delimited lists, operators and recovery tests

Delimited lists with and without trailing separators, operator tables, single-token recovery and
stops at boundaries, and the whole-parser exactness, totality and provenance statements.
-/

section
-- leanmerge: from Solcore.Test.SyntaxDelimitedNoTrailingRejectionTraceProperties
/-! Independent no-trailing rejection consumers with real checked-name
expression children. Tokens are explicit carriers, not canonical lexer claims.
No complete parser is evaluated by decision tactics. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxDelimitedNoTrailingRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "no-trailing-reject.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def nameA : Identifier := { span := span 1 4, value := "a-b" }
private def nameC : Identifier := { span := span 5 8, value := "c-d" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def nameExpr (name : Identifier) : Expr := { span := name.span, value := .identifier name }
private def hyphen (name : Identifier) : ParseDiagnostic := {
  span := name.span, kind := .invalidIdentifierHyphen name.value
}
private def inputState (text : String) (tokens : Array Token) (endByte : Nat)
    (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := text }, tokens, cursor := 0
  window := { endIndex := tokens.size, endByte }, diagnosticsRev := prior.reverse
}

private theorem nameParsed {input : Remainder} (name : Identifier) (reportSource : SourceId) (endByte : Nat)
    (token : TokenAt input.tokens input.endIndex input.cursor (nameToken name))
    (spelling : IdentifierHyphenSpelling name.value) :
    IdentifierExpressionTraceParses reportSource endByte input (nameExpr name)
      { input with cursor := input.cursor + 1 } [hyphen name] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨otherSpan, other⟩ <;>
      have impossible := TokenAt.token_unique token other <;> cases impossible
  exact .parsed (.identifier absent (.parsed ⟨token, rfl, rfl, rfl⟩ (.hyphen spelling)))

private def laterTokens : Array Token := #[
  { span := span 0 1, value := .symbol .leftBracket }, nameToken nameA,
  { span := span 4 5, value := .symbol .comma }, nameToken nameC,
  { span := span 8 9, value := .symbol .comma },
  { span := span 9 10, value := .symbol .plus },
  { span := span 10 11, value := .symbol .rightBracket }]
private def laterRem (cursor : Nat) : Remainder := { tokens := laterTokens, endIndex := 7, cursor }
private def plusFailure : Failure := {
  span := span 9 10, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .expression
}

private theorem laterRejected (allowEmpty : Bool) :
    NoTrailingDelimitedListTraceRejects .leftBracket .rightBracket allowEmpty .expression
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 11 (laterRem 0)
      (laterRem 5) plusFailure.toDiagnostic [hyphen nameA, hyphen nameC] := by
  have last : NoTrailingDelimitedTailTraceRejects .rightBracket .expression
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 11
      (laterRem 4) (laterRem 5) plusFailure.toDiagnostic [] :=
    .elementRejected (span 8 9) (afterComma := laterRem 5) ⟨⟨by decide, rfl⟩, rfl⟩
      ⟨by simp [BooleanPatternAbsentAt, TokenKindAbsentAt, TokenAt, laterRem, laterTokens],
        .absent (by simp [IdentifierAbsentAt, TokenAt, laterRem, laterTokens]),
        .reported (.token (current := { span := span 9 10, value := .symbol .plus }) ⟨by decide, rfl⟩), rfl⟩
  have tail : NoTrailingDelimitedTailTraceRejects .rightBracket .expression
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 11
      (laterRem 2) (laterRem 5) plusFailure.toDiagnostic [hyphen nameC] :=
    .laterRejected (span 4 5) (afterComma := laterRem 3) (afterElement := laterRem 4)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (nameParsed nameC source 11 ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameC; decide))
      (by decide) last
  have continues : PreferredCloseNotTaken .rightBracket allowEmpty (laterRem 1) := by
    cases allowEmpty with
    | false => exact .disabled
    | true => exact .absent (by simp [TokenKindAbsentAt, TokenAt, laterRem, laterTokens, nameToken])
  exact .tailRejected (span 0 1) (afterOpening := laterRem 1) (afterFirst := laterRem 2)
    ⟨⟨by decide, rfl⟩, rfl⟩ continues
    (nameParsed (input := laterRem 1) nameA source 11 ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameA; decide))
    (by decide) tail

/-- Two successful name children contribute events in order. The rejecting
third child's exact identifier failure remains outside the appended events. -/
theorem earlier_names_survive_later_child_rejection (allowEmpty : Bool) (prior : List ParseDiagnostic) :
    ∃ output, delimitedNoTrailing .leftBracket .rightBracket allowEmpty identifierExpression .expression .expression
        (inputState "[a-b,c-d,+]" laterTokens 11 prior) = .reject plusFailure output ∧
      output.declarativeRemainder = laterRem 5 ∧ output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] := by
  simpa only [inputState, State.diagnostics, List.reverse_reverse] using
    (delimitedNoTrailing_trace_reject_failure_iff identifierExpression_trace_success_sound
      identifierExpression_trace_reject_sound identifierExpression_trace_success_complete
      identifierExpression_trace_reject_complete identifierExpression_success_context
      .leftBracket .rightBracket allowEmpty .expression .expression
      (input := inputState "[a-b,c-d,+]" laterTokens 11 prior)).mp (laterRejected allowEmpty)

private def commaTokens : Array Token := #[
  { span := span 0 1, value := .symbol .leftBracket }, nameToken nameA,
  { span := span 4 5, value := .symbol .comma },
  { span := span 5 6, value := .symbol .rightBracket }]
private def commaRem (cursor : Nat) : Remainder := { tokens := commaTokens, endIndex := 4, cursor }
private def closeFailure : Failure := {
  span := span 5 6, found := some (.symbol .rightBracket)
  expected := { head := .identifier, tail := [] }, context := .expression
}

private theorem commaRejected (closing : Symbol) (allowEmpty : Bool) :
    NoTrailingDelimitedListTraceRejects .leftBracket closing allowEmpty .expression
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 6 (commaRem 0)
      (commaRem 3) closeFailure.toDiagnostic [hyphen nameA] := by
  have tail : NoTrailingDelimitedTailTraceRejects closing .expression IdentifierExpressionTraceParses
      IdentifierExpressionTraceRejects source 6 (commaRem 2) (commaRem 3) closeFailure.toDiagnostic [] :=
    .elementRejected (span 4 5) (afterComma := commaRem 3) ⟨⟨by decide, rfl⟩, rfl⟩
      ⟨by simp [BooleanPatternAbsentAt, TokenKindAbsentAt, TokenAt, commaRem, commaTokens],
        .absent (by simp [IdentifierAbsentAt, TokenAt, commaRem, commaTokens]),
        .reported (.token (current := { span := span 5 6, value := .symbol .rightBracket }) ⟨by decide, rfl⟩), rfl⟩
  have continues : PreferredCloseNotTaken closing allowEmpty (commaRem 1) := by
    cases allowEmpty with
    | false => exact .disabled
    | true => exact .absent (by simp [TokenKindAbsentAt, TokenAt, commaRem, commaTokens, nameToken])
  exact .tailRejected (span 0 1) (afterOpening := commaRem 1) (afterFirst := commaRem 2)
    ⟨⟨by decide, rfl⟩, rfl⟩ continues
    (nameParsed (input := commaRem 1) nameA source 6 ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameA; decide))
    (by decide) tail

/-- This covers both closing=rightBracket (no closing guard after comma)
and closing=comma (the current comma wins over the closing branch). -/
theorem comma_calls_child_before_any_closing (closing : Symbol) (allowEmpty : Bool) (prior : List ParseDiagnostic) :
    ∃ output, delimitedNoTrailing .leftBracket closing allowEmpty identifierExpression .expression .expression
        (inputState "[a-b,]" commaTokens 6 prior) = .reject closeFailure output ∧
      output.declarativeRemainder = commaRem 3 ∧ output.diagnostics = prior ++ [hyphen nameA] := by
  simpa only [inputState, State.diagnostics, List.reverse_reverse] using
    (delimitedNoTrailing_trace_reject_failure_iff identifierExpression_trace_success_sound
      identifierExpression_trace_reject_sound identifierExpression_trace_success_complete
      identifierExpression_trace_reject_complete identifierExpression_success_context
      .leftBracket closing allowEmpty .expression .expression
      (input := inputState "[a-b,]" commaTokens 6 prior)).mp (commaRejected closing allowEmpty)

/-- At a byte-window endpoint with closing=comma, the delimiter report retains
two comma expectations. Every input field and arbitrary reverse prefix survives;
the child need not satisfy any contract because no child is called here. -/
theorem window_end_keeps_duplicate_comma_expectations {α : Type} (element : Parser α)
    (opening : Token) (context : ParseContext) (phase : ParserPhase) (fuel : Nat) (elementsRev : List α)
    {input : State} (ended : input.window.endIndex ≤ input.cursor) :
    afterDelimitedElement element .comma false context phase opening (fuel + 1) elementsRev input =
      .reject {
        span := { source := input.file.id, startByte := input.window.endByte, endByte := input.window.endByte }
        found := none, expected := { head := .symbol .comma, tail := [.symbol .comma] }, context
      } input := by
  have absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .comma) := by
    rintro ⟨_, token⟩
    exact Nat.not_lt_of_ge ended token.1
  have reported : RejectAtReports input.file.id input.window.endByte
      { head := .symbol .comma, tail := [.symbol .comma] } context input.declarativeRemainder
      (Failure.toDiagnostic {
        span := { source := input.file.id, startByte := input.window.endByte, endByte := input.window.endByte }
        found := none, expected := { head := .symbol .comma, tail := [.symbol .comma] }, context
      }) :=
    .reported (.windowEnd ended)
  rcases (rejectAt_reports_iff (alpha := DelimitedList α)).mp reported with ⟨failure, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [afterDelimitedElement, DelimitedTraceInternals.symbol_absent .comma absent,
    Bool.false_eq_true, if_false, result]

/-- A diagnosed rejecting child follows a diagnosed successful child without
deduplication. The arbitrary reverse prefix is not replayed and the final
report is still separate from all three copies of the event. -/
theorem successful_and_rejected_child_events_remain_ordered {α : Type} (element : Parser α)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α) (event report : ParseDiagnostic)
    {input : State} {afterComma afterElement afterNextComma rejectedRem : Remainder}
    {value : α} {commaSpan nextCommaSpan : SourceSpan}
    (comma : ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (child : elementTrace input.file.id input.window.endByte afterComma value afterElement [event, event])
    (progress : afterComma.cursor < afterElement.cursor)
    (nextComma : ExactTokenParses (.symbol .comma) afterElement nextCommaSpan afterNextComma)
    (childRejected : elementRejects input.file.id input.window.endByte afterNextComma rejectedRem report [event])
    (adequate : input.remainingCount < fuel) :
    ∃ failure rejected, afterDelimitedElement element closing false context phase opening fuel elementsRev input =
        .reject failure rejected ∧ rejected.declarativeRemainder = rejectedRem ∧
      failure.toDiagnostic = report ∧ rejected.diagnostics = input.diagnostics ++ [event, event, event] := by
  have rejection : NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder rejectedRem report [event, event, event] :=
    .laterRejected commaSpan comma child progress (.elementRejected nextCommaSpan nextComma childRejected)
  exact afterDelimitedElement_noTrailing_trace_reject_complete successComplete rejectComplete contextFrame
    closing context phase opening fuel elementsRev rejection adequate

end Solcore.Test.SyntaxDelimitedNoTrailingRejectionTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties
/-! The trailing guard bypasses every possible child behavior. A comma-valued
closing delimiter still obeys comma-first priority and consumes two tokens. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.DelimitedTraceInternals

theorem trailing_close_bypasses_any_child {α : Type} (element : Parser α)
    (opening : Token) (closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    (fuel : Nat) (elementsRev : List α) {input : State}
    {afterComma after : Remainder} {commaSpan closingSpan : SourceSpan}
    (comma : ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (finish : ExactTokenParses (.symbol closing) afterComma closingSpan after) :
    afterDelimitedElement element closing true context phase opening (fuel + 1) elementsRev input =
      .ok { span := SourceSpan.cover opening.span closingSpan, elements := elementsRev.reverse }
        { input with cursor := input.cursor + 2 } := by
  have commaResult := symbol_eq_ok_of_exactTokenParses .comma context comma
  have commaPresent := symbol_present .comma comma
  rcases comma with ⟨_, rfl⟩
  have finishResult := symbol_eq_ok_of_exactTokenParses closing context
    (input := { input with cursor := input.cursor + 1 }) finish
  simp only [afterDelimitedElement, commaPresent, if_true, commaResult, Bool.true_and,
    symbol_present closing (input := { input with cursor := input.cursor + 1 }) finish,
    closeDelimited, finishResult]

theorem comma_closing_consumes_two_commas {α : Type} (element : Parser α)
    (opening : Token) (context : ParseContext) (phase : ParserPhase)
    (fuel : Nat) (elementsRev : List α) {input : State}
    {afterComma after : Remainder} {commaSpan closingSpan : SourceSpan}
    (comma : ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (finish : ExactTokenParses (.symbol .comma) afterComma closingSpan after) :
    afterDelimitedElement element .comma true context phase opening (fuel + 1) elementsRev input =
      .ok { span := SourceSpan.cover opening.span closingSpan, elements := elementsRev.reverse }
        { input with cursor := input.cursor + 2 } :=
  trailing_close_bypasses_any_child element opening .comma context phase fuel elementsRev comma finish

theorem empty_list_bypasses_any_child {α : Type} (element : Parser α)
    (opening closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    {input : State} {afterOpening after : Remainder} {openingSpan closingSpan : SourceSpan}
    (marker : ExactTokenParses (.symbol opening) input.declarativeRemainder openingSpan afterOpening)
    (finish : ExactTokenParses (.symbol closing) afterOpening closingSpan after) :
    delimited opening closing true element context phase input =
      .ok { span := SourceSpan.cover openingSpan closingSpan, elements := [] }
        { input with cursor := input.cursor + 2 } := by
  have markerResult := symbol_eq_ok_of_exactTokenParses opening context marker
  rcases marker with ⟨_, rfl⟩
  have finishResult := symbol_eq_ok_of_exactTokenParses closing context
    (input := { input with cursor := input.cursor + 1 }) finish
  simp only [delimited, delimitedWithPolicy, markerResult, Bool.true_and,
    symbol_present closing (input := { input with cursor := input.cursor + 1 }) finish,
    if_true, closeDelimited, finishResult, List.reverse_nil]

/-- A single comma selects the child when the following token is not the
comma-valued closing delimiter; the child's exact failure and state escape. -/
theorem single_comma_invokes_child {α : Type} (element : Parser α)
    (opening : Token) (context : ParseContext) (phase : ParserPhase)
    (fuel : Nat) (elementsRev : List α) {input rejected : State} {failure : Failure}
    {afterComma : Remainder} {commaSpan : SourceSpan}
    (comma : ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (absent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol .comma))
    (child : element { input with cursor := input.cursor + 1 } = .reject failure rejected) :
    afterDelimitedElement element .comma true context phase opening (fuel + 1) elementsRev input =
      .reject failure rejected := by
  have commaResult := symbol_eq_ok_of_exactTokenParses .comma context comma
  have commaPresent := symbol_present .comma comma
  rcases comma with ⟨_, rfl⟩
  simp only [afterDelimitedElement, commaPresent, if_true, commaResult, Bool.true_and,
    symbol_absent .comma (input := { input with cursor := input.cursor + 1 }) absent,
    Bool.false_eq_true, if_false, child]

end Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserBodyIsolation
/-! Regression coverage for balanced Core-body parsing and local fallback. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def isolationSource : SourceId := {
  origin := .main
  path := "parser-body-isolation.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := isolationSource, content }
  let output ← match Parser.parse file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"{label}: parser invariant failed: {reprStr error}")
  assertEqual output.lexicalDiagnostics [] s!"{label} lexical diagnostics"
  unless output.parsed.items.all (fun item => item.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid item span")
  unless output.parseDiagnostics.all
      (fun diagnostic => diagnostic.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid diagnostic span")
  pure output

private def missingExpression : ParseDiagnosticKind :=
  .unexpected (some (.symbol .semicolon))
    { head := .expression, tail := [] } .expression

private def assertSingleErrorExpression
    (body : Block) (label : String) : IO Unit :=
  match body.value with
  | [{ value := .expression { value := .error, .. } true, .. }] => pure ()
  | statements => throw (IO.userError
      s!"{label}: expected one recovered expression, got {reprStr statements}")

private def testTopLevelIsolationAndDiagnosticOrder : IO Unit := do
  let source := String.intercalate "\n" [
    "function bad() public { x = y let broken = ; }",
    "type Kept = word;",
    "function good() { return; }"
  ]
  let output ← checkedParse "top-level body isolation" source
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((15, 21), .constraintViolation
      (.modifierOutsideContract .publicKw)),
    ((24, 29), .constraintViolation .assignmentRequiresSemicolon),
    ((43, 44), missingExpression)
  ] "top-level diagnostic order"
  match output.parsed.items with
  | [
      { span := badSpan, value := .function bad, .. },
      { value := .typeAlias kept, .. },
      { value := .function good, .. }
    ] =>
      assertEqual (byteRange badSpan) (0, 46) "bad function item span"
      assertEqual bad.value.signature.name.value "bad" "bad function name"
      assertEqual (byteRange bad.value.body.span) (22, 46)
        "bad function body span"
      match bad.value.body.value with
      | [
          { value := .assignValue left _ right, .. },
          { value := .expression { value := .error, .. } true, .. }
        ] =>
          match left.value, right.value with
          | .identifier leftName, .identifier rightName =>
              assertEqual leftName.value "x" "statement before fallback"
              assertEqual rightName.value "y" "assignment before fallback"
          | left, right => throw (IO.userError
              s!"assignment around fallback changed: {reprStr left}; {reprStr right}")
      | body => throw (IO.userError
          s!"bad function fallback body changed: {reprStr body}")
      assertEqual kept.value.name.value "Kept" "following alias"
      assertEqual good.value.signature.name.value "good" "following function"
      assertEqual good.value.body.value.length 1 "following function body"
  | items => throw (IO.userError
      s!"top-level body isolation changed: {reprStr items}")

private def testContractEntryIsolation : IO Unit := do
  let source := String.intercalate "\n" [
    "contract C {",
    "  function bad() { let x = ; }",
    "  first: word;",
    "  constructor() { let y = ; }",
    "  second: bool;",
    "  fallback() { let z = ; }",
    "  function good() {}",
    "}",
    "type After = word;"
  ]
  let output ← checkedParse "contract entry isolation" source
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((40, 41), missingExpression),
    ((85, 86), missingExpression),
    ((128, 129), missingExpression)
  ] "contract entry diagnostics"
  match output.parsed.items with
  | [
      { value := .contract contract, .. },
      { value := .typeAlias after, .. }
    ] =>
      assertEqual contract.value.name.value "C" "contract name"
      assertEqual (byteRange contract.value.bodySpan) (11, 154)
        "contract body span"
      assertEqual after.value.name.value "After" "post-contract alias"
      match contract.value.members with
      | [
          { value := .function bad, .. },
          { value := .field first, .. },
          { value := .constructor constructor, .. },
          { value := .field second, .. },
          { value := .fallback fallback, .. },
          { value := .function good, .. }
        ] =>
          assertSingleErrorExpression bad.value.body
            "contract function fallback body"
          assertEqual (byteRange bad.value.body.span) (30, 43)
            "contract function body span"
          assertEqual first.value.name.value "first" "member after function"
          assertSingleErrorExpression constructor.value.body
            "constructor fallback body"
          assertEqual (byteRange constructor.value.body.span) (75, 88)
            "constructor body span"
          assertEqual second.value.name.value "second"
            "member after constructor"
          assertSingleErrorExpression fallback.value.body
            "fallback entry body"
          assertEqual (byteRange fallback.value.body.span) (118, 131)
            "fallback body span"
          assertEqual good.value.signature.name.value "good"
            "member after fallback"
      | members => throw (IO.userError
          s!"contract entry members changed: {reprStr members}")
  | items => throw (IO.userError
      s!"contract entry isolation changed: {reprStr items}")

private def testNestedBlockIsolation : IO Unit := do
  let source := String.intercalate "\n" [
    "function outer() { { let broken = ; } return; }",
    "function after() {}"
  ]
  let output ← checkedParse "nested block isolation" source
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((34, 35), missingExpression)
  ] "nested block diagnostic"
  match output.parsed.items with
  | [
      { value := .function outer, .. },
      { value := .function after, .. }
    ] =>
      assertEqual outer.value.signature.name.value "outer" "outer function"
      assertEqual (byteRange outer.value.body.span) (17, 47)
        "outer isolated body span"
      match outer.value.body.value with
      | [
          { value := .block [
              { value := .expression { value := .error, .. } true, .. }
            ], .. },
          { value := .returnStmt none, .. }
        ] => pure ()
      | body => throw (IO.userError
          s!"nested fallback body changed: {reprStr body}")
      assertEqual after.value.signature.name.value "after"
        "function after nested error"
  | items => throw (IO.userError
      s!"nested block isolation changed: {reprStr items}")

private def testLambdaBodyIsolation : IO Unit := do
  let source := String.intercalate "\n" [
    "function outer() { let f = lam() { let broken = ; }; return; }",
    "type After = word;"
  ]
  let output ← checkedParse "lambda body isolation" source
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((48, 49), missingExpression)
  ] "lambda body diagnostic"
  match output.parsed.items with
  | [
      { value := .function outer, .. },
      { value := .typeAlias after, .. }
    ] =>
      assertEqual (byteRange outer.value.body.span) (17, 62)
        "lambda owner body span"
      assertEqual after.value.name.value "After" "item after lambda owner"
      match outer.value.body.value with
      | [
          { value := .letDecl _ none (some initializer), .. },
          { value := .returnStmt none, .. }
        ] => match initializer.value with
          | .lambda _ _ none body =>
              assertEqual (byteRange initializer.span) (27, 51)
                "isolated lambda span"
              assertEqual (byteRange body.span) (33, 51)
                "isolated lambda body span"
              assertSingleErrorExpression body "lambda fallback body"
          | value => throw (IO.userError
              s!"lambda initializer changed: {reprStr value}")
      | statements => throw (IO.userError
          s!"lambda owner body changed: {reprStr statements}")
  | items => throw (IO.userError
      s!"lambda body isolation changed: {reprStr items}")

private def testUnclosedBodyIsNotRecovered : IO Unit := do
  let source := String.intercalate "\n" [
    "function open() { return;",
    "type Ambiguous = word;"
  ]
  let output ← checkedParse "unclosed body" source
  assertEqual output.parsed.items.length 0 "unclosed body item count"
  match output.parseDiagnostics.getLast? with
  | some {
      span,
      kind := .unexpected none
        { head := .symbol .rightBrace, tail := [] } .statement
    } =>
      assertEqual (byteRange span)
        (source.utf8ByteSize, source.utf8ByteSize)
        "unclosed body terminal span"
  | diagnostic => throw (IO.userError
      s!"unclosed body diagnostic changed: {reprStr diagnostic}")

/-- Run balanced-body fallback, isolation, and unclosed-body regressions. -/
def testSyntaxParserBodyIsolation : IO Unit := do
  testTopLevelIsolationAndDiagnosticOrder
  testContractEntryIsolation
  testNestedBlockIsolation
  testLambdaBodyIsolation
  testUnclosedBodyIsNotRecovered

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserBoundaryStopTraceProperties
/-! Compositional consumers retain failed-attempt diagnostics at a file stop. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserBoundaryStopTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example (fuel : Nat) (itemsRev : List TopItem)
    {input failed : State} {failure : Failure}
    (inside : input.cursor < input.window.endIndex)
    (starts : atTopItemStart input = true)
    (rejected : parseItemsItem input = .reject failure failed) :
    ∃ output, parseItems (fuel + 1) itemsRev input = .ok itemsRev.reverse output ∧
      output.diagnostics = failed.diagnostics ++ [failure.toDiagnostic] := by
  rcases parseItems_boundaryStop_trace_exact fuel itemsRev inside starts rejected with
    ⟨output, result, _, trace⟩
  exact ⟨output, result, trace⟩

example (comments : List Comment)
    {input failed : State} {failure : Failure}
    (inside : input.cursor < input.window.endIndex)
    (starts : atTopItemStart input = true)
    (rejected : parseItemsItem input = .reject failure failed) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := []
        comments
      } output ∧
      output.cursor = input.cursor ∧
      output.diagnostics = failed.diagnostics ++ [failure.toDiagnostic] := by
  rcases sourceFile_boundaryStop_trace_exact comments inside starts rejected with
    ⟨output, result, remainderEq, trace⟩
  exact ⟨output, result, congrArg (·.cursor) remainderEq, trace⟩

end Solcore.Test.SyntaxParserBoundaryStopTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCertifiedParseProperties
/-! External consumers for total parsing with complete output provenance. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCertifiedParseProperties

open Solcore.Syntax.Parser

example := @productionParseLexed_exists_ok_completeOutput_validFor
example := @productionParse_exists_ok_completeOutput_validFor
example := @productionParseLexed_exists_ok_publicSourceFileOrdinary
example := @productionParse_exists_ok_publicSourceFileOrdinary

end Solcore.Test.SyntaxParserCertifiedParseProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCompleteOutputProperties
/-! External consumers for complete public parser output validity. -/

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @ParseOutput.CanonicalValidFor
example := @parseLexed_ok_completeOutput_validFor
example := @parse_ok_completeOutput_validFor

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDelimitedAllowEmptySoundnessProperties
/-! External consumers for allow-empty trailing-list grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedAllowEmptySoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TrailingDelimitedListParses
example := @TrailingDelimitedListParses.value_unique
example := @trailingDelimitedListExactOutcomeSpec
example := @delimited_allowEmpty_trailing_success_sound

example {α : Type} (opening closing : Symbol) (element : Parser α)
    (elementParses : Remainder → α → Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimited opening closing true element context phase input =
      .ok values next) :
    TrailingDelimitedListParses opening closing elementParses
      input.declarativeRemainder values next.declarativeRemainder :=
  delimited_allowEmpty_trailing_success_sound opening closing element
    elementParses context phase elementSound elementShape result

end Solcore.Test.SyntaxParserDelimitedAllowEmptySoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDelimitedFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @remainingCount_lt_of_cursor_le
example := @remainingCount_lt_after_strict_progress
example := @FuelElementTotalityContract.weaken
example := @FuelElementTotalityContract.ne_invariant
example := @afterDelimitedElement_ordinary_of_elementFuel
example := @delimitedWithPolicy_ordinary_of_elementFuel
example := @delimited_ordinary_of_elementFuel
example := @delimited_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserDelimitedFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDelimitedNoTrailingAllowEmptySoundnessProperties
/-! External consumers for allow-empty no-trailing-list grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedNoTrailingAllowEmptySoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @NoTrailingDelimitedListParses
example := @NoTrailingDelimitedListParses.value_unique
example := @noTrailingDelimitedListExactOutcomeSpec
example := @delimitedNoTrailing_allowEmpty_success_sound

example {α : Type} (opening closing : Symbol) (element : Parser α)
    (elementParses : Remainder → α → Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimitedNoTrailing opening closing true element context phase
      input = .ok values next) :
    NoTrailingDelimitedListParses opening closing elementParses
      input.declarativeRemainder values next.declarativeRemainder :=
  delimitedNoTrailing_allowEmpty_success_sound opening closing element
    elementParses context phase elementSound elementShape result

end Solcore.Test.SyntaxParserDelimitedNoTrailingAllowEmptySoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDelimitedNoTrailingSoundnessProperties
/-! External consumers for no-trailing delimited-list soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedNoTrailingSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @NoTrailingDelimitedTailParses
example := @NonemptyNoTrailingDelimitedListParses
example := @NoTrailingDelimitedTailParses.result_unique
example := @NonemptyNoTrailingDelimitedListParses.value_unique
example := @nonemptyNoTrailingDelimitedListExactOutcomeSpec
example := @delimitedNoTrailing_nonempty_success_sound

example {α : Type} (opening closing : Symbol) (element : Parser α)
    (elementParses : Remainder → α → Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimitedNoTrailing opening closing false element context phase
      input = .ok values next) :
    NonemptyNoTrailingDelimitedListParses opening closing elementParses
      input.declarativeRemainder values next.declarativeRemainder :=
  delimitedNoTrailing_nonempty_success_sound opening closing element
    elementParses context phase elementSound elementShape result

end Solcore.Test.SyntaxParserDelimitedNoTrailingSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDelimitedNoTrailingTraceProperties
/-! Boundary consumers for actual generic delimited parsers. All states may
already carry arbitrary diagnostics; no lexer or general-expression claim. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedNoTrailingTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @NoTrailingDelimitedListTraceParses.ordinary
example := @NoTrailingDelimitedListTraceParses.result_unique
example := @afterDelimitedElement_noTrailing_production_trace_success_iff
example := @delimitedNoTrailing_success_context

/-- The immediate empty branch precedes child execution, even when closing is comma. -/
theorem empty_comma_close_bypasses_any_child {α : Type} (child : Parser α)
    (context : ParseContext) (phase : ParserPhase) {input : State}
    {openingSpan closingSpan : SourceSpan} {afterOpening after : Remainder}
    (marker : ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (finish : ExactTokenParses (.symbol .comma) afterOpening closingSpan after) :
    delimitedNoTrailing .leftParen .comma true child context phase input = .ok {
      span := SourceSpan.cover openingSpan closingSpan
      elements := [] } { input with cursor := input.cursor + 2 } := by
  have markerResult := symbol_eq_ok_of_exactTokenParses .leftParen context marker
  rcases marker with ⟨_, rfl⟩
  have present := DelimitedTraceInternals.symbol_present .comma
    (input := { input with cursor := input.cursor + 1 }) finish
  have result := symbol_eq_ok_of_exactTokenParses .comma context
    (input := { input with cursor := input.cursor + 1 }) finish
  simp only [delimitedNoTrailing, delimitedWithPolicy, markerResult, Bool.true_and,
    present, if_true, closeDelimited, result, List.reverse_nil]

/-- Once a first value has been read, a comma is never interpreted as closing. -/
theorem comma_closing_never_completes_a_tail {α : Type} {child : Parser α}
    {childTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
    (sound : ParserTraceSuccessSound child childTrace) (frame : ParserSuccessContext child)
    (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (prefixRev : List α) (input output : State) (values : DelimitedList α) :
    afterDelimitedElement child .comma false context phase opening fuel prefixRev input ≠
      .ok values output := by
  intro result
  rcases afterDelimitedElement_noTrailing_success_trace_sound sound frame .comma context phase
      opening fuel prefixRev input values output result with ⟨_, _, _, _, parsed, _⟩
  exact parsed.closing_ne_comma rfl

private def symbolTrace (symbolValue : Symbol) (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (token : Token) (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  ExactTokenParses (.symbol symbolValue) input token.span output ∧
    token.value = .symbol symbolValue ∧ trace = []

private theorem symbol_complete (symbolValue : Symbol) (context : ParseContext) :
    ParserTraceSuccessComplete (symbol symbolValue context) (symbolTrace symbolValue) := by
  intro input token after trace parsed
  rcases parsed with ⟨parsed, kindEq, rfl⟩
  rcases token with ⟨span, kind⟩
  cases kindEq
  exact ⟨_, symbol_eq_ok_of_exactTokenParses symbolValue context parsed,
    parsed.2.symm, by simp only [State.diagnostics, List.append_nil]⟩

private theorem symbol_context (symbolValue : Symbol) (context : ParseContext) :
    ParserSuccessContext (symbol symbolValue context) := by
  intro input output value result
  rw [(symbol_ok_tokenAt symbolValue context result).2]
  exact ⟨rfl, rfl⟩

/-- With empty disabled, the first closing token can be the child's own value. -/
theorem nonempty_child_can_consume_first_closing
    (context : ParseContext) (phase : ParserPhase) {input : State}
    {openingSpan valueSpan closingSpan : SourceSpan} {afterOpening afterValue after : Remainder}
    (marker : ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (value : ExactTokenParses (.symbol .rightParen) afterOpening valueSpan afterValue)
    (finish : ExactTokenParses (.symbol .rightParen) afterValue closingSpan after) :
    ∃ output, delimitedNoTrailing .leftParen .rightParen false (symbol .rightParen context)
      context phase input = .ok {
        span := SourceSpan.cover openingSpan closingSpan
        elements := [{ span := valueSpan, value := .symbol .rightParen }] } output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  have commaAbsent : TokenKindAbsentAt afterValue.tokens afterValue.endIndex
      afterValue.cursor (.symbol .comma) := by
    rintro ⟨span, comma⟩
    have tokenEq := comma.token_unique finish.1
    cases tokenEq
  have valueTrace : symbolTrace .rightParen input.file.id input.window.endByte afterOpening
      { span := valueSpan, value := .symbol .rightParen } afterValue [] := ⟨value, rfl, rfl⟩
  have parsed : NoTrailingDelimitedListTraceParses .leftParen .rightParen false
      (symbolTrace .rightParen) input.file.id input.window.endByte input.declarativeRemainder
      { span := SourceSpan.cover openingSpan closingSpan,
        elements := [{ span := valueSpan, value := .symbol .rightParen }] } after [] :=
    .nonempty openingSpan closingSpan marker .disabled valueTrace
      (by rw [value.2]; exact Nat.lt_succ_self _) (.close commaAbsent finish)
  simpa only [List.append_nil] using delimitedNoTrailing_trace_success_complete
    (symbol_complete .rightParen context) (symbol_context .rightParen context)
    .leftParen .rightParen false context phase parsed

private theorem name_trace {source : SourceId} {endByte : Nat}
    {input output : Remainder} {name : Identifier}
    (parsed : IdentifierParses input name output) (hyphen : IdentifierHyphenSpelling name.value) :
    IdentifierExpressionTraceParses source endByte input { span := name.span, value := .identifier name }
      output [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨span, keyword⟩ <;>
      have tokenEq := parsed.1.token_unique keyword <;> cases tokenEq
  exact .parsed (.identifier absent (.parsed parsed (.hyphen hyphen)))

/-- The actual checked-name leaf appends both exact spelling events in written order. -/
theorem checked_name_list_keeps_complete_event_order
    (context : ParseContext) (phase : ParserPhase) {input : State}
    {openingSpan commaSpan closingSpan : SourceSpan} {first second : Identifier}
    {afterOpening afterFirst afterComma afterSecond after : Remainder}
    (marker : ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (firstParsed : IdentifierParses afterOpening first afterFirst)
    (firstHyphen : IdentifierHyphenSpelling first.value)
    (comma : ExactTokenParses (.symbol .comma) afterFirst commaSpan afterComma)
    (secondParsed : IdentifierParses afterComma second afterSecond)
    (secondHyphen : IdentifierHyphenSpelling second.value)
    (finish : ExactTokenParses (.symbol .rightParen) afterSecond closingSpan after) :
    ∃ output, delimitedNoTrailing .leftParen .rightParen true identifierExpression context phase input =
      .ok { span := SourceSpan.cover openingSpan closingSpan, elements := [
        { span := first.span, value := .identifier first },
        { span := second.span, value := .identifier second }] } output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ [
        { span := first.span, kind := .invalidIdentifierHyphen first.value },
        { span := second.span, kind := .invalidIdentifierHyphen second.value }] := by
  have firstAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex
      afterOpening.cursor (.symbol .rightParen) := by
    rintro ⟨span, token⟩; have tokenEq := firstParsed.1.token_unique token; cases tokenEq
  have commaAbsent : TokenKindAbsentAt afterSecond.tokens afterSecond.endIndex
      afterSecond.cursor (.symbol .comma) := by
    rintro ⟨span, token⟩; have tokenEq := finish.1.token_unique token; cases tokenEq
  apply delimitedNoTrailing_trace_success_complete identifierExpression_trace_success_complete
    identifierExpression_success_context .leftParen .rightParen true context phase
  exact .nonempty openingSpan closingSpan marker (.absent firstAbsent)
    (name_trace firstParsed firstHyphen) (by rw [firstParsed.2.2.2]; exact Nat.lt_succ_self _)
    (.next commaSpan comma (name_trace secondParsed secondHyphen)
      (by rw [secondParsed.2.2.2]; exact Nat.lt_succ_self _) (.close commaAbsent finish))

end Solcore.Test.SyntaxParserDelimitedNoTrailingTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDelimitedNonemptyProperties
/-! External consumers for nonempty delimited-result laws. -/

namespace Tests

open Solcore.Syntax.Parser

example := @afterDelimitedElement_elements_ne_nil_onSuccess
example := @delimitedWithPolicy_false_elements_ne_nil_onSuccess
example := @delimited_false_elements_ne_nil_onSuccess
example := @delimitedNoTrailing_false_elements_ne_nil_onSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDelimitedProperties
/-! External consumers for delimited parser provenance contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DelimitedList.ValidFor
example := @Parser.PreservesTokensOnSuccess
example := @delimitedWithPolicy_validFor
example := @delimited_validFor
example := @delimitedNoTrailing_validFor
example := @delimitedWithPolicy_preservesTokensOnSuccess
example := @delimited_preservesTokensOnSuccess
example := @delimitedNoTrailing_preservesTokensOnSuccess
example := @delimitedWithPolicy_cursor_lt_onSuccess
example := @delimitedWithPolicy_cursorMonotoneOnSuccess
example := @delimited_cursorMonotoneOnSuccess
example := @delimitedNoTrailing_cursorMonotoneOnSuccess
example := @delimitedWithPolicy_startsAtCurrentTokenOnSuccess
example := @delimited_startsAtCurrentTokenOnSuccess
example := @delimitedNoTrailing_startsAtCurrentTokenOnSuccess

example {α : Type} (file : SourceFile) (values : DelimitedList α)
    (elementValid : SourceFile → α → Prop)
    (valid : DelimitedList.ValidFor elementValid file values)
    (element : α) (member : element ∈ values.elements) :
    values.span.ValidFor file ∧ elementValid file element :=
  ⟨valid.1, valid.2 element member⟩

example (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (identifier context) := by
  intro input value next result
  rcases identifier_ok_state_shape context result with
    ⟨_token, _found, _span, tokensEq, _cursor⟩
  exact tokensEq

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDelimitedSoundnessProperties
/-! External consumers for declarative delimited-list soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDelimitedSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TrailingDelimitedTailParses
example := @NonemptyTrailingDelimitedListParses
example := @TrailingDelimitedTailParses.result_unique
example := @NonemptyTrailingDelimitedListParses.value_unique
example := @nonemptyTrailingDelimitedListExactOutcomeSpec
example := @DelimitedTailRejects.output_unique
example := @DelimitedListRejects.output_unique
example := @delimited_nonempty_trailing_success_sound

example {α : Type} (opening closing : Symbol) (element : Parser α)
    (elementParses : Remainder → α → Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimited opening closing false element context phase input =
      .ok values next) :
    NonemptyTrailingDelimitedListParses opening closing elementParses
      input.declarativeRemainder values next.declarativeRemainder :=
  delimited_nonempty_trailing_success_sound opening closing element
    elementParses context phase elementSound elementShape result

example {input next : State} {values : DelimitedList SelectorName}
    (result : delimited .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel input =
        .ok values next) :
    NonemptyTrailingDelimitedListParses .leftBrace .rightBrace
      SelectorNameParses input.declarativeRemainder values
      next.declarativeRemainder :=
  delimited_nonempty_trailing_success_sound .leftBrace .rightBrace
    (selectorName .importDecl) SelectorNameParses .importDecl .topLevel
    (selectorName_success_sound .importDecl)
    (selectorName_preservesTokenWindow .importDecl) result

end Solcore.Test.SyntaxParserDelimitedSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserDelimitedTotalityProperties
/-! External consumers for generic delimited-loop totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @ElementTotalityContract
example := @afterDelimitedElement_ordinary_of_remainingCount_lt
example := @afterDelimitedElement_ne_invariant_of_remainingCount_lt
example := @delimitedWithPolicy_ordinary
example := @delimitedWithPolicy_ne_invariant
example := @delimited_ordinary
example := @delimited_ne_invariant
example := @delimitedNoTrailing_ordinary
example := @delimitedNoTrailing_ne_invariant

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserOperatorInternals
/-! External visibility checks for the operator-parts parser. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserOperatorInternals

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @OperatorInternals.operatorParts

example (context : ParseContext) (partsRev : List String) (state : State) :
    OperatorInternals.operatorParts context 0 partsRev state =
      .invariant (.fuelExhausted .topLevel state.currentSpan) :=
  rfl

end Solcore.Test.SyntaxParserOperatorInternals
end

section
-- leanmerge: from Solcore.Test.SyntaxParserOperatorProperties
/-! External consumers for selector-name provenance and shape contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @SelectorName.ValidFor
example := @operatorSelector_validFor
example := @selectorName_validFor
example := @operatorSelector_preservesTokenWindow
example := @selectorName_preservesTokenWindow
example := @operatorSelector_preservesTokensOnSuccess
example := @selectorName_preservesTokensOnSuccess
example := @operatorSelector_startsAtCurrentTokenOnSuccess
example := @selectorName_startsAtCurrentTokenOnSuccess
example := @operatorSelector_cursor_lt_onSuccess
example := @operatorSelector_cursorMonotoneOnSuccess
example := @selectorName_cursor_lt_onSuccess
example := @selectorName_cursorMonotoneOnSuccess

example (context : ParseContext) :
    (operatorSelector context).ValidFor SelectorName.ValidFor ∧
      Parser.PreservesTokenWindow (operatorSelector context) ∧
      Parser.PreservesTokensOnSuccess (operatorSelector context) ∧
      Parser.CursorMonotoneOnSuccess (operatorSelector context) ∧
      Parser.StartsAtCurrentTokenOnSuccess
        (operatorSelector context) (·.span) :=
  ⟨operatorSelector_validFor context,
    operatorSelector_preservesTokenWindow context,
    operatorSelector_preservesTokensOnSuccess context,
    operatorSelector_cursorMonotoneOnSuccess context,
    operatorSelector_startsAtCurrentTokenOnSuccess context⟩

example (context : ParseContext) :
    (selectorName context).ValidFor SelectorName.ValidFor ∧
      Parser.PreservesTokenWindow (selectorName context) ∧
      Parser.PreservesTokensOnSuccess (selectorName context) ∧
      Parser.CursorMonotoneOnSuccess (selectorName context) ∧
      Parser.StartsAtCurrentTokenOnSuccess (selectorName context) (·.span) :=
  ⟨selectorName_validFor context,
    selectorName_preservesTokenWindow context,
    selectorName_preservesTokensOnSuccess context,
    selectorName_cursorMonotoneOnSuccess context,
    selectorName_startsAtCurrentTokenOnSuccess context⟩

example (file : SourceFile) (span : SourceSpan) (name : Identifier)
    (valid : SelectorName.ValidFor file {
      span
      value := .identifier name
    }) :
    span.ValidFor file ∧ name.span.ValidFor file :=
  valid

example (context : ParseContext) :
    (delimited .leftBrace .rightBrace true (selectorName context)
      context .topLevel).ValidFor
        (DelimitedList.ValidFor SelectorName.ValidFor) :=
  delimited_validFor SelectorName.ValidFor .leftBrace .rightBrace true
    (selectorName context) context .topLevel
    (selectorName_validFor context)
    (selectorName_preservesTokensOnSuccess context)

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserOperatorTotalityProperties
/-! External consumers for operator-selector totality contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserOperatorTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.OperatorInternals

example := @operatorParts_ordinary_of_remainingCount_lt
example := @operatorParts_ne_invariant_of_remainingCount_lt
example := @operatorParts_production_ordinary
example := @operatorParts_production_ne_invariant
example := @operatorSelector_ordinary
example := @operatorSelector_ne_invariant
example := @selectorName_ordinary
example := @selectorName_ne_invariant
example := @operatorSelector_elementTotalityContract
example := @selectorName_elementTotalityContract

example (context : ParseContext) :
    ElementTotalityContract (selectorName context) :=
  selectorName_elementTotalityContract context

end Solcore.Test.SyntaxParserOperatorTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserRecovery
/-! Recovery, totality, and resource-bound regressions for canonical parsing. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def parserSource : SourceId := {
  origin := .main
  path := "parser-recovery.sol"
}

private def assertEqual_variant {α : Type} [BEq α] [Repr α]
    (actual expected : α) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def checkedParse_variant (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := parserSource, content }
  match Parser.parse file with
  | .error error =>
      throw (IO.userError s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual_variant output.parsed.source file.id s!"{label} source"
      unless output.parsed.span.isValidFor file do
        throw (IO.userError s!"{label}: invalid file span")
      pure output

private def aliasDecl? (item : TopItem) : Option TypeAliasDecl :=
  match item.value with
  | .typeAlias declaration => some declaration
  | _ => none

private def testTypeRecovery : IO Unit := do
  let output ← checkedParse_variant "type recovery"
    "type A = + - *; type B = word;"
  match output.parsed.items with
  | [first, second] =>
      match aliasDecl? first, aliasDecl? second with
      | some recovered, some valid =>
          match recovered.value.value.value with
          | .error => pure ()
          | value => throw (IO.userError
              s!"type recovery: expected error type, got {reprStr value}")
          assertEqual_variant (byteRange recovered.value.value.span) (9, 14)
            "type recovery error span"
          assertEqual_variant valid.value.name.value "B"
            "type recovery following alias"
      | _, _ => throw (IO.userError "type recovery: expected two aliases")
  | items => throw (IO.userError
      s!"type recovery: expected two items, got {items.length}")
  match output.parseDiagnostics with
  | [unexpected, recovered] =>
      assertEqual_variant (byteRange unexpected.span) (9, 10)
        "type recovery unexpected span"
      assertEqual_variant (byteRange recovered.span) (9, 14)
        "type recovery consumed span"
      match recovered.kind with
      | .recovered .typeAliasValue => pure ()
      | kind => throw (IO.userError
          s!"type recovery: wrong recovery diagnostic {reprStr kind}")
  | diagnostics => throw (IO.userError
      s!"type recovery: expected two diagnostics, got {diagnostics.length}")

private def testUnrecoverableAliases : IO Unit := do
  let empty ← checkedParse_variant "empty alias RHS"
    "type A = ; type B = word;"
  assertEqual_variant empty.parsed.items.length 0 "empty alias item count"
  assertEqual_variant empty.parseDiagnostics.length 1 "empty alias diagnostics"

  let prefixOutput ← checkedParse_variant "prefix-success alias"
    "type A = word garbage; type B = word;"
  assertEqual_variant prefixOutput.parsed.items.length 0 "prefix-success item count"
  match prefixOutput.parseDiagnostics with
  | [diagnostic] =>
      assertEqual_variant (byteRange diagnostic.span) (14, 21)
        "prefix-success failure span"
  | diagnostics => throw (IO.userError
      s!"prefix-success: expected one diagnostic, got {diagnostics.length}")

private def testTopLevelRecovery : IO Unit := do
  let output ← checkedParse_variant "top-level recovery" "+ -; type B = word;"
  match output.parsed.items with
  | [errorItem, aliasItem] =>
      match errorItem.value, aliasDecl? aliasItem with
      | .error, some alias =>
          assertEqual_variant (byteRange errorItem.span) (0, 4)
            "top-level recovery span"
          assertEqual_variant alias.value.name.value "B"
            "top-level recovery following alias"
      | _, _ => throw (IO.userError
          "top-level recovery: wrong recovered item shapes")
  | items => throw (IO.userError
      s!"top-level recovery: expected two items, got {items.length}")
  match output.parseDiagnostics with
  | [{ span, kind := .recovered .topItem }] =>
      assertEqual_variant (byteRange span) (0, 4)
        "top-level recovery diagnostic span"
  | diagnostics => throw (IO.userError
      s!"top-level recovery: wrong diagnostics {reprStr diagnostics}")

private def nestedNamed : Nat → String
  | 0 => "word"
  | depth + 1 => "Box<" ++ nestedNamed depth ++ ">"

private def testNestingGuards : IO Unit := do
  let openings := String.ofList (List.replicate 129 '(')
  let closings := String.ofList (List.replicate 129 ')')
  let overflow ← checkedParse_variant "delimiter nesting"
    ("type A = " ++ openings ++ "word" ++ closings ++ ";")
  assertEqual_variant overflow.parsed.items.length 0 "nesting overflow items"
  match overflow.parseDiagnostics with
  | [{ span, kind := .nestingExceeded .delimiter 128 }] =>
      assertEqual_variant (byteRange span) (137, 138) "nesting overflow span"
  | diagnostics => throw (IO.userError
      s!"nesting overflow: wrong diagnostics {reprStr diagnostics}")

  let angleDeep ← checkedParse_variant "angle depth"
    ("type A = " ++ nestedNamed 129 ++ ";")
  assertEqual_variant angleDeep.parsed.items.length 1 "angle depth item count"
  assertEqual_variant angleDeep.parseDiagnostics [] "angle depth diagnostics"

private def testValidatedLexedInput : IO Unit := do
  let first : SourceFile := {
    id := parserSource
    content := "type A = word;"
  }
  let second : SourceFile := {
    id := { origin := .external "other", path := "other.sol" }
    content := first.content
  }
  let lexed ← match Lexer.lex first with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"validation lex failed: {reprStr error}")
  match Parser.parseLexed second lexed with
  | .error (.invalidLexedSource expected actual) =>
      assertEqual_variant expected second.id "invalid source expected owner"
      assertEqual_variant actual first.id "invalid source actual owner"
  | result => throw (IO.userError
      s!"invalid source: unexpected result {reprStr result}")

  let invalid : LexedFile := {
    source := first.id
    tokens := [{
      span := { source := first.id, startByte := 0, endByte := 99 }
      value := .identifier "bad"
    }]
    comments := []
    diagnostics := []
  }
  match Parser.parseLexed first invalid with
  | .error (.invalidTokenSpan 0 _) => pure ()
  | result => throw (IO.userError
      s!"invalid token span: unexpected result {reprStr result}")

/-- Run canonical parser recovery and totality regressions. -/
def testSyntaxParserRecovery : IO Unit := do
  testTypeRecovery
  testUnrecoverableAliases
  testTopLevelRecovery
  testNestingGuards
  testValidatedLexedInput

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserSingleRecoveryTraceProperties
/-! Compile-time consumers of grammar-derived single-recovery file traces. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSingleRecoveryTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals
open Solcore.Syntax.DeclarativeGrammar

example := @atTopItemStart_eq_false_of_topItemStartAbsent
example := @parseItemsItem_eq_rejectAt_of_topItemStartAbsent
example := @recoveredTopItem_eq_error
example := @parseItems_singleRecoveryToEnd_exact
example := @parseItems_production_singleRecoveryToEnd_exact
example := @sourceFile_singleRecoveryToEnd_exact

example (comments : List Comment)
    {input : State} {item : TopItem} {after : Remainder}
    (startsAbsent : TopItemKindsAbsentAt input.declarativeRemainder
      ImportTerminatorTopItemStartKinds)
    (recovered : TopItemRecoveryParses input.declarativeRemainder item after)
    (atEnd : after.cursor = input.window.endIndex) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := [attachTopItemComments input.file comments item]
        comments
      } output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++
        [{ span := item.span, kind := .recovered .topItem }] :=
  sourceFile_singleRecoveryToEnd_exact comments startsAbsent recovered atEnd

private def exampleFile : SourceFile := {
  id := { origin := .main, path := "single-recovery.sol" }
  content := ";"
}

private def exampleSpan : SourceSpan := SourceSpan.fullFile exampleFile

private def exampleInput (priorRev : List ParseDiagnostic) : State := {
  file := exampleFile
  tokens := #[{ span := exampleSpan, value := .symbol .semicolon }]
  cursor := 0
  window := { endIndex := 1, endByte := 1 }
  diagnosticsRev := priorRev
}

private theorem exampleStartsAbsent (priorRev : List ParseDiagnostic) :
    TopItemKindsAbsentAt (exampleInput priorRev).declarativeRemainder
      ImportTerminatorTopItemStartKinds := by
  simp [TopItemKindsAbsentAt, ImportTerminatorTopItemStartKinds, TokenKindAbsentAt,
    State.declarativeRemainder, exampleInput, TokenAt]

private theorem exampleRecovers (priorRev : List ParseDiagnostic) :
    TopItemRecoveryParses (exampleInput priorRev).declarativeRemainder
      (recoveredTopItemValue exampleSpan exampleSpan)
      { (exampleInput priorRev).declarativeRemainder with cursor := 1 } := by
  apply TopItemRecoveryParses.recovered
    (token := { span := exampleSpan, value := .symbol .semicolon })
  · simp [TokenAt, State.declarativeRemainder, exampleInput]
  · exact .stop (.windowEnd (by simp [State.declarativeRemainder, exampleInput]))

/-- A real non-start token derives the exact result without an execution
hypothesis, including arbitrary retained diagnostics and supplied comments. -/
example (priorRev : List ParseDiagnostic) (comments : List Comment) :
    ∃ output, sourceFile comments (exampleInput priorRev) = .ok {
        source := exampleFile.id
        span := SourceSpan.fullFile exampleFile
        items := [attachTopItemComments exampleFile comments
          (recoveredTopItemValue exampleSpan exampleSpan)]
        comments
      } output ∧
      output.cursor = 1 ∧
      output.diagnostics = priorRev.reverse ++
        [{ span := exampleSpan, kind := .recovered .topItem }] := by
  rcases sourceFile_singleRecoveryToEnd_exact comments (exampleStartsAbsent priorRev)
      (exampleRecovers priorRev) rfl with ⟨output, result, after, trace⟩
  refine ⟨output, result, congrArg Remainder.cursor after, ?_⟩
  simpa [exampleInput, State.diagnostics, recoveredTopItemValue, SourceSpan.cover]
    using trace

end Solcore.Test.SyntaxParserSingleRecoveryTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserSingleSuccessTraceProperties
/-! Consumers of executable single-success composition. These deliberately
assume the item reply and do not present it as an independent grammar proof. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSingleSuccessTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example (fuel : Nat) (itemsRev : List TopItem)
    {input next : State} {item : TopItem}
    (parsed : parseItemsItem input = .ok item next)
    (atEnd : next.cursor = input.window.endIndex) :
    ∃ output, parseItems (fuel + 2) itemsRev input =
        .ok (itemsRev.reverse ++ [item]) output ∧
      output.declarativeRemainder = next.declarativeRemainder ∧
      output.diagnostics = next.diagnostics :=
  parseItems_singleSuccessToEnd_exact fuel itemsRev parsed atEnd

example (itemsRev : List TopItem) {input next : State} {item : TopItem}
    (parsed : parseItemsItem input = .ok item next)
    (atEnd : next.cursor = input.window.endIndex) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ [item]) output ∧
      output.declarativeRemainder = next.declarativeRemainder ∧
      output.diagnostics = next.diagnostics :=
  parseItems_production_singleSuccessToEnd_exact itemsRev parsed atEnd

example (comments : List Comment) {input next : State} {item : TopItem}
    (parsed : parseItemsItem input = .ok item next)
    (atEnd : next.cursor = input.window.endIndex) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := [attachTopItemComments input.file comments item]
        comments
      } output ∧
      output.declarativeRemainder = next.declarativeRemainder ∧
      output.diagnostics = next.diagnostics :=
  sourceFile_singleSuccessToEnd_exact comments parsed atEnd

example (comments : List Comment) (trace : List ParseDiagnostic)
    {input next : State} {item : TopItem}
    (parsed : parseItemsItem input = .ok item next)
    (atEnd : next.cursor = input.window.endIndex)
    (childTrace : next.diagnostics = input.diagnostics ++ trace) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := [attachTopItemComments input.file comments item]
        comments
      } output ∧
      output.declarativeRemainder = next.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases sourceFile_singleSuccessToEnd_exact comments parsed atEnd with
    ⟨output, result, remainderEq, traceEq⟩
  exact ⟨output, result, remainderEq, traceEq.trans childTrace⟩

end Solcore.Test.SyntaxParserSingleSuccessTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserSyntaxExactnessProperties
/-! Consumers of unconditional independent complete-file syntax exactness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSyntaxExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.PlainTopItemOrdinaryParses DeclarativeGrammar.PlainTopItemRejects :=
  plainTopItem_exactOutcomeSpec

example {input output : State} {actual expected : TopItem}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : plainTopItem input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.PlainTopItemOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  plainTopItem_exactOutcomeSpec.successResultUnique
    (plainTopItem_success_ordinaryOutcome_sound result) expectedParsed

example := @plainTopItem_success_result_unique
example := @plainTopItem_reject_output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects :=
  topItem_exactOutcomeSpec

example {input output : State} {actual expected : TopItem}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : topItem input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.TopItemOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  topItem_exactOutcomeSpec.successResultUnique
    (topItem_success_ordinaryOutcome_sound result) expectedParsed

example := @topItem_success_result_unique
example := @topItem_reject_output_unique

example := @parseItems_exactOutcomeSpec
example := @parseItems_success_result_unique
example := @sourceFile_success_result_unique
example := @parseLexed_ok_parsed_value_unique
example := @parse_ok_parsed_value_unique

example (file : SourceFile) (comments : List Comment) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.SourceFileOrdinaryParses file comments)
      DeclarativeGrammar.SourceFileRejects :=
  sourceFile_exactOutcomeSpec file comments

example (comments : List Comment) {input output : State} {actual expected : ParsedFile}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : sourceFile comments input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (sourceFile_exactOutcomeSpec input.file comments).successResultUnique
    (sourceFile_success_ordinaryOutcome_sound result) expectedParsed

example {file : SourceFile} {lexed : LexedFile} {output : ParseOutput} {expected : ParsedFile}
    (result : parseLexed file lexed = .ok output)
    (expectedParsed : DeclarativeGrammar.PublicSourceFileOrdinaryParses
      file lexed.tokens lexed.comments expected) : output.parsed = expected :=
  DeclarativeGrammar.PublicSourceFileOrdinaryParses.value_unique
    (parseLexed_ok_publicSourceFileOrdinary_sound result) expectedParsed

example {file : SourceFile} {output : ParseOutput} {expected : ParsedFile}
    (result : parse file = .ok output)
    (expectedParsed : DeclarativeGrammar.PublicSourceFileOrdinaryParses
      file output.tokens output.parsed.comments expected) : output.parsed = expected :=
  DeclarativeGrammar.PublicSourceFileOrdinaryParses.value_unique
    (parse_ok_publicSourceFileOrdinary_sound result) expectedParsed

end Solcore.Test.SyntaxParserSyntaxExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTotality
/-!
Deterministic resource and totality regressions corresponding to the pinned
`solcore-rs` parser property tests.  The corpus is generated locally so the
test remains reproducible and does not require a property-testing runtime.
-/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def totalitySource : SourceId := {
  origin := .main
  path := "parser-totality.sol"
}

private def assertValidOutput (label content : String)
    (output : ParseOutput) : IO Unit := do
  let file : SourceFile := { id := totalitySource, content }
  assertEqual output.parsed.source file.id s!"{label} parsed source"
  assertEqual output.parsed.span (SourceSpan.fullFile file)
    s!"{label} parsed file span"
  unless output.tokens.all (fun token => token.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid token span")
  unless output.parsed.comments.all
      (fun comment => comment.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid comment span")
  unless output.parsed.items.all (fun item => item.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid top-item span")
  unless output.lexicalDiagnostics.all
      (fun diagnostic => diagnostic.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid lexical diagnostic span")
  unless output.parseDiagnostics.all
      (fun diagnostic => diagnostic.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid parse diagnostic span")

private def parseTotal (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := totalitySource, content }
  match Parser.parse file with
  | .ok output =>
      assertValidOutput label content output
      pure output
  | .error error => throw (IO.userError
      s!"{label}: public parser exposed an executor invariant: {reprStr error}")

private def nextSeed (state : Nat) : Nat :=
  (state * 1664525 + 1013904223) % 4294967291

private def nul : Char := Char.ofNat 0

private def characterAlphabet : List Char :=
  ("abcXYZ_019 #$@{}[]()<>+-*/%&|^!~=?:;,.\"\\\n\r\t").toList ++
    [nul, 'λ', 'δ', 'é', 'ß', '漢', '界', '🦀', '🙂', '́']

private def generatedCharacters : Nat → Nat → List Char
  | 0, _ => []
  | length + 1, state =>
      let next := nextSeed state
      let character :=
        characterAlphabet[next % characterAlphabet.length]?.getD nul
      character :: generatedCharacters length next

private def generatedSource (index : Nat) : String :=
  let length := (index * 37 + 11) % 97
  String.ofList (generatedCharacters length (index + 1))

private def edgeSources : List String := [
  "",
  "\n\r\t",
  String.ofList [nul],
  String.ofList ['a', nul, 'b', '\n', 'λ'],
  "§§§",
  "λ δ é ß 漢字 🦀 🙂",
  "́́́",
  "\\ \" ' # $ @",
  "/* unterminated λ",
  "// comment without newline",
  "\"bad\\qescape\"",
  "0x 0b 0o 123_ 1e+",
  "(((([[{{ ?? :: ;;;",
  "}}]]) ) else default return",
  "function nul() { let x = " ++ String.ofList [nul] ++ "; }"
]

private def testGeneratedUtf8Totality : IO Unit := do
  for (source, index) in edgeSources.zipIdx do
    let _ ← parseTotal s!"UTF-8 edge {index}" source
  for index in List.range 192 do
    let source := generatedSource index
    let _ ← parseTotal s!"generated UTF-8 {index}" source

private def fixture (lines : List String) : String :=
  String.intercalate "\n" lines ++ "\n"

private def corpusSeeds : List (String × String) := [
  ("valid function", "function ok() {}\n"),
  ("valid contract", fixture [
    "contract Modifiers {",
    "  constructor() {}",
    "  function ping() public {}",
    "  function deposit() public payable returns (uint256) { return 0; }",
    "  fallback() payable {}",
    "}"
  ]),
  ("valid match", fixture [
    "function main(foo: (word, word)) returns (word) {",
    "  let res: word;",
    "  match (foo) { case (v0, v1) {",
    "    { let x: word = v1; res = x; }",
    "  } }",
    "  return res;",
    "}"
  ]),
  ("invalid signature", "function main( -> word { return 0; }\n"),
  ("invalid body", "function broken() { let x = ; return pair(+ -, 0);\n"),
  ("invalid comment", "contract C { /* unclosed\n")
]

private def mutations : List String := [
  "",
  "§",
  String.ofList [nul],
  "/*",
  "\"bad\\q\"",
  " ? : ",
  "\nreturn;\n",
  "λ🦀",
  "((((([",
  "}}];"
]

private def insertMutation (source mutation : String)
    (position : Nat) : String :=
  let characters := source.toList
  let offset := position % (characters.length + 1)
  String.ofList
    (characters.take offset ++ mutation.toList ++ characters.drop offset)

private def insertionPositions (seedIndex mutationIndex length : Nat) : List Nat :=
  [0, length / 2, length,
    (seedIndex * 31 + mutationIndex * 17 + 7) % (length + 1)]

private def testCorpusMutationTotality : IO Unit := do
  for ((seedName, source), seedIndex) in corpusSeeds.zipIdx do
    for (mutation, mutationIndex) in mutations.zipIdx do
      for (position, positionIndex) in
          (insertionPositions seedIndex mutationIndex source.length).zipIdx do
        let mutated := insertMutation source mutation position
        let label :=
          s!"mutation {seedName}/{mutationIndex}/{positionIndex}"
        let _ ← parseTotal label mutated

private def repeatText (count : Nat) (text : String) : String :=
  (List.replicate count text).foldl (· ++ ·) ""

private def rightNestedTernary (depth : Nat) : String :=
  "function main() returns (word) { return " ++
    repeatText depth "true ? 0 : " ++ "0; }"

private def nestedType (depth : Nat) : String :=
  "type Deep = " ++ String.ofList (List.replicate depth '(') ++ "word" ++
    String.ofList (List.replicate depth ')') ++ ";"

private def testResourceBoundaries : IO Unit := do
  -- As upstream intends, syntax parsing of this chain completes before a later
  -- HIR expression-depth policy is applied.
  let ternary ← parseTotal "right-nested ternary depth 96"
    (rightNestedTernary 96)
  assertEqual ternary.lexicalDiagnostics [] "ternary lexical diagnostics"
  assertEqual ternary.parseDiagnostics [] "ternary parse diagnostics"
  assertEqual ternary.parsed.items.length 1 "ternary item count"

  let ternaryBoundary ← parseTotal "right-nested ternary at syntax limit"
    (rightNestedTernary Parser.maxSyntaxNesting)
  assertEqual ternaryBoundary.lexicalDiagnostics []
    "ternary boundary lexical diagnostics"
  assertEqual ternaryBoundary.parseDiagnostics []
    "ternary boundary parse diagnostics"
  assertEqual ternaryBoundary.parsed.items.length 1
    "ternary boundary item count"

  let boundary ← parseTotal "delimiter nesting at limit"
    (nestedType Parser.maxSyntaxNesting)
  assertEqual boundary.lexicalDiagnostics [] "boundary lexical diagnostics"
  assertEqual boundary.parseDiagnostics [] "boundary parse diagnostics"
  assertEqual boundary.parsed.items.length 1 "boundary item count"

  let overflow ← parseTotal "delimiter nesting above limit"
    (nestedType (Parser.maxSyntaxNesting + 1))
  assertEqual overflow.parsed.items.length 0 "overflow item count"
  match overflow.parseDiagnostics with
  | [{ kind := .nestingExceeded .delimiter limit, .. }] =>
      assertEqual limit Parser.maxSyntaxNesting "reported nesting limit"
  | diagnostics => throw (IO.userError
      s!"overflow diagnostics changed: {reprStr diagnostics}")

/-- Run deterministic arbitrary-source, mutation, and resource regressions. -/
def testSyntaxParserTotality : IO Unit := do
  testGeneratedUtf8Totality
  testCorpusMutationTotality
  testResourceBoundaries

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxProvenanceProperties
/-! External compile consumers for canonical syntax provenance laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example (file : SourceFile) (lexed : LexedFile)
    (result : Lexer.lex file = .ok lexed) :
    lexed.source = file.id :=
  Lexer.lex_ok_source file lexed result

example (file : SourceFile) (diagnostic : LexicalDiagnostic)
    (result : Lexer.lex file = .error diagnostic) :
    diagnostic.span.source = file.id :=
  Lexer.lex_error_source file diagnostic result

example (file : SourceFile) (output : ParseOutput)
    (result : Parser.parse file = .ok output) :
    output.parsed.source = file.id :=
  Parser.parse_ok_source file output result

example (file : SourceFile) (output : ParseOutput)
    (result : Parser.parse file = .ok output) :
    output.parsed.span = SourceSpan.fullFile file :=
  Parser.parse_ok_span file output result

example (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (result : Parser.parseLexed file lexed = .ok output) :
    output.tokens = lexed.tokens ∧
      output.lexicalDiagnostics = lexed.diagnostics ∧
      output.parsed.comments = lexed.comments :=
  Parser.parseLexed_ok_retention file lexed output result

example (file : SourceFile) (output : ParseOutput)
    (result : Parser.parse file = .ok output) :
    ∃ lexed,
      Lexer.lex file = .ok lexed ∧
      Parser.parseLexed file lexed = .ok output ∧
      output.tokens = lexed.tokens ∧
      output.lexicalDiagnostics = lexed.diagnostics ∧
      output.parsed.comments = lexed.comments :=
  Parser.parse_ok_lexed_provenance file output result

end Tests
end
