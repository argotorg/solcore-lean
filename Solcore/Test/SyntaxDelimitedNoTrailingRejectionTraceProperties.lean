import Solcore.Syntax.Parser.DelimitedNoTrailingRejectionTraceCorrespondenceProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingRejectionTraceProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties

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
