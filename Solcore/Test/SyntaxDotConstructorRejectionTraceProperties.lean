import Solcore.Syntax.Parser.DotConstructorRejectionTraceProperties
import Solcore.Syntax.DeclarativeDotConstructorRejectionTraceProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties

/-! Raw leading-dot rejection consumers. The nonempty example uses explicit
token carriers and actual checked-name expression children, not a general
expression parser or a canonical lexer claim. Parser decision is not used. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxDotConstructorRejectionTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Raw invocation needs no dispatcher guard: an absent dot produces its
complete uncommitted primitive failure without invoking any nested parser. -/
theorem unselected_missing_dot_rejects_without_child (nested : Parser Expr)
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .dot))
    (reported : RejectAtReports input.file.id input.window.endByte { head := .symbol .dot, tail := [] }
      .expression input.declarativeRemainder failure.toDiagnostic) :
    dotConstructor nested input = .reject failure input := by
  rcases (symbol_reject_reports_iff .dot .expression).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [dotConstructor, bind, result]

/-- Name rejection also bypasses every argument parser and propagates the
entire rejected state, rather than committing or rewriting the name report. -/
theorem name_rejection_bypasses_all_arguments (nested : Parser Expr)
    {input afterDot rejected : State} {dot : Token} {failure : Failure}
    (dotResult : symbol .dot .expression input = .ok dot afterDot)
    (nameResult : expressionName afterDot = .reject failure rejected) :
    dotConstructor nested input = .reject failure rejected := by
  simp only [dotConstructor, bind, dotResult, nameResult]

/-- The optional wrapper neither recovers nor changes any field of a selected
argument-list failure state, even when the nested parser has changed that state. -/
theorem optional_arguments_keep_whole_failure_state (nested : Parser Expr)
    {input rejected : State} {failure : Failure} {openingSpan : SourceSpan}
    (selected : TokenAt input.tokens input.window.endIndex input.cursor {
      span := openingSpan, value := .symbol .leftParen })
    (result : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input =
      .reject failure rejected) : optionalDotConstructorArguments nested input = .reject failure rejected := by
  have guard := DelimitedTraceInternals.symbol_present .leftParen (input := input)
    (after := { input.declarativeRemainder with cursor := input.cursor + 1 }) ⟨selected, rfl⟩
  exact optionalDotConstructorArguments_reject_iff_list.mpr ⟨guard, result⟩

theorem argument_rejection_keeps_whole_failure_state (nested : Parser Expr)
    {input afterDot afterName rejected : State} {dot : Token} {name : Identifier} {failure : Failure}
    (dotResult : symbol .dot .expression input = .ok dot afterDot)
    (nameResult : expressionName afterDot = .ok name afterName)
    (argumentsResult : optionalDotConstructorArguments nested afterName = .reject failure rejected) :
    dotConstructor nested input = .reject failure rejected := by
  simp only [dotConstructor, bind, dotResult, nameResult, argumentsResult]

private def source : SourceId := { origin := .main, path := "dot-rejection-trace.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def nameA : Identifier := { span := span 1 4, value := "a-b" }
private def nameC : Identifier := { span := span 5 8, value := "c-d" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def hyphen (name : Identifier) : ParseDiagnostic := {
  span := name.span, kind := .invalidIdentifierHyphen name.value
}
private def tokens : Array Token := #[
  { span := span 0 1, value := .symbol .dot }, nameToken nameA,
  { span := span 4 5, value := .symbol .leftParen }, nameToken nameC,
  { span := span 8 9, value := .symbol .comma },
  { span := span 9 10, value := .symbol .plus },
  { span := span 10 11, value := .symbol .rightParen },
  { span := span 12 16, value := .identifier "tail" }]
private def rem (cursor : Nat) : Remainder := { tokens, endIndex := 8, cursor }
private def initial (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := ".a-b(c-d,+) tail" }, tokens, cursor := 0
  window := { endIndex := 8, endByte := 16 }, diagnosticsRev := prior.reverse
}
private def plusFailure : Failure := {
  span := span 9 10, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .expression
}

private theorem name_trace {input : Remainder} (name : Identifier)
    (token : TokenAt input.tokens input.endIndex input.cursor (nameToken name))
    (spelling : IdentifierHyphenSpelling name.value) :
    ExpressionNameTraceParses source 16 input name { input with cursor := input.cursor + 1 } [hyphen name] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨otherSpan, other⟩ <;>
      have impossible := token.token_unique other <;> cases impossible
  exact .identifier absent (.parsed ⟨token, rfl, rfl, rfl⟩ (.hyphen spelling))

private theorem argumentsRejected : OptionalDotConstructorArgumentsTraceRejects
    IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 16 (rem 2)
      (rem 5) plusFailure.toDiagnostic [hyphen nameC] := by
  have tail : NoTrailingDelimitedTailTraceRejects .rightParen .expression IdentifierExpressionTraceParses
      IdentifierExpressionTraceRejects source 16 (rem 4) (rem 5) plusFailure.toDiagnostic [] :=
    .elementRejected (span 8 9) (afterComma := rem 5) ⟨⟨by decide, rfl⟩, rfl⟩
      ⟨by simp [BooleanPatternAbsentAt, TokenKindAbsentAt, TokenAt, rem, tokens],
        .absent (by simp [IdentifierAbsentAt, TokenAt, rem, tokens]),
        .reported (.token (current := { span := span 9 10, value := .symbol .plus }) ⟨by decide, rfl⟩), rfl⟩
  have listRejected : NoTrailingDelimitedListTraceRejects .leftParen .rightParen true .expression
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 16 (rem 2) (rem 5)
      plusFailure.toDiagnostic [hyphen nameC] :=
    .tailRejected (span 4 5) (afterOpening := rem 3) (afterFirst := rem 4)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (.absent (by simp [TokenKindAbsentAt, TokenAt, rem, tokens, nameToken]))
      (.parsed (name_trace (input := rem 3) nameC ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameC; decide)))
      (by decide) tail
  exact .present (span 4 5) ⟨by decide, rfl⟩ listRejected

/-- Constructor-name events come before successful argument-name events;
the rejecting next argument supplies its full report without committing it. -/
theorem name_and_argument_events_precede_uncommitted_failure (prior : List ParseDiagnostic) :
    ∃ output, dotConstructor identifierExpression (initial prior) = .reject plusFailure output ∧
      output.declarativeRemainder = rem 5 ∧ output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] := by
  have rejected : DotConstructorTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source 16 (rem 0) (rem 5) plusFailure.toDiagnostic [hyphen nameA, hyphen nameC] :=
    .argumentsRejected (span 0 1) (afterDot := rem 1) (afterName := rem 2)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (name_trace (input := rem 1) nameA ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameA; decide))
      argumentsRejected
  simpa only [initial, State.diagnostics, List.reverse_reverse] using
    (dotConstructor_trace_reject_failure_iff identifierExpression_trace_success_sound
      identifierExpression_trace_reject_sound identifierExpression_trace_success_complete
      identifierExpression_trace_reject_complete identifierExpression_success_context (input := initial prior)).mp rejected

end Solcore.Test.SyntaxDotConstructorRejectionTraceProperties
