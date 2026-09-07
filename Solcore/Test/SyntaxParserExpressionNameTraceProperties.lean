import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties
import Solcore.Syntax.Parser.ReturnStatementSuccessTraceProperties

/-! Real Boolean and checked-name expressions, including exact hyphen events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionNameTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @expressionNameTrace_outcome_total
example := @identifierExpressionTrace_exactOutcomeSpec
example := @identifierExpressionTrace_outcomeExists
example := @identifierExpression_trace_reject_sound
example := @identifierExpression_trace_reject_complete

theorem boolean_true_has_priority_and_is_silent {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .keyword .trueKw }) :
    expressionName input = .ok { span, value := "true" } { input with cursor := input.cursor + 1 } := by
  simpa only [List.reverse_nil, List.nil_append] using
    expressionName_eq_ok_of_trace (.boolean ⟨.trueKeyword token, rfl⟩)

theorem boolean_false_expression_is_identifier_shaped {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .keyword .falseKw }) :
    identifierExpression input = .ok {
      span, value := .identifier { span, value := "false" }
    } { input with cursor := input.cursor + 1 } := by
  simpa only [List.reverse_nil, List.nil_append] using
    identifierExpression_eq_ok_of_trace (.parsed (.boolean ⟨.falseKeyword token, rfl⟩))

private theorem boolean_absent_of_identifier {input : Remainder} {name : Identifier}
    (token : TokenAt input.tokens input.endIndex input.cursor
      { span := name.span, value := .identifier name.value }) : BooleanPatternAbsentAt input := by
  constructor
  · rintro ⟨span, current⟩; cases TokenAt.token_unique token current
  · rintro ⟨span, current⟩; cases TokenAt.token_unique token current

/-- Multiple hyphens still contribute exactly one checked-spelling event,
after all earlier events; the full output state and identifier AST are fixed. -/
theorem multiple_hyphens_emit_once {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .identifier "a-b-c" }) :
    identifierExpression input = .ok {
      span, value := .identifier { span, value := "a-b-c" }
    } { input with
      cursor := input.cursor + 1
      diagnosticsRev := { span, kind := .invalidIdentifierHyphen "a-b-c" } :: input.diagnosticsRev } := by
  have parsed : IdentifierParses input.declarativeRemainder { span, value := "a-b-c" }
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨token, rfl, rfl, rfl⟩
  have traced : IdentifierExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder { span, value := .identifier { span, value := "a-b-c" } }
      { input.declarativeRemainder with cursor := input.cursor + 1 }
      [{ span, kind := .invalidIdentifierHyphen "a-b-c" }] :=
    .parsed (.identifier (boolean_absent_of_identifier (name := { span, value := "a-b-c" }) token)
      (.parsed parsed (.hyphen (by change '-' ∈ "a-b-c".toList; decide))))
  exact identifierExpression_eq_ok_of_trace traced

theorem clean_name_keeps_every_prior_event {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .identifier "plain" }) :
    expressionName input = .ok { span, value := "plain" } { input with cursor := input.cursor + 1 } := by
  have parsed : IdentifierParses input.declarativeRemainder { span, value := "plain" }
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨token, rfl, rfl, rfl⟩
  simpa only [List.reverse_nil, List.nil_append] using expressionName_eq_ok_of_trace (input := input)
    (.identifier (boolean_absent_of_identifier (name := { span, value := "plain" }) token)
      (.parsed parsed (.clean (by change ¬ '-' ∈ "plain".toList; decide))))

/-- Failure after Boolean guards expects an identifier, not the Boolean
primitive's expression category, and retains the complete input state. -/
theorem non_name_reports_identifier_expectation {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    identifierExpression input = .reject {
      span, found := some (.symbol .semicolon)
      expected := { head := .identifier, tail := [] }, context := .expression
    } input := by
  have noBoolean : BooleanPatternAbsentAt input.declarativeRemainder := by
    constructor
    · rintro ⟨otherSpan, current⟩; cases TokenAt.token_unique token current
    · rintro ⟨otherSpan, current⟩; cases TokenAt.token_unique token current
  have noName : IdentifierAbsentAt input.declarativeRemainder := by
    rintro ⟨otherSpan, text, current⟩; cases TokenAt.token_unique token current
  have current : CurrentInputAt input.file.id input.window.endByte input.declarativeRemainder
      span (some (.symbol .semicolon)) :=
    .token (current := { span, value := .symbol .semicolon }) token
  exact (identifierExpression_trace_reject_failure_iff.mp
    ⟨noBoolean, .absent noName, .reported current, rfl⟩).1

/-- The actual identifier-expression leaf closes the nonempty return trace
without a caller-supplied expression contract, including its single hyphen report. -/
theorem real_name_return_keeps_hyphen_event
    {input : State} {afterMarker afterValue after : Remainder} {name : Identifier}
    {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (nameParsed : IdentifierParses afterMarker name afterValue)
    (hyphen : IdentifierHyphenSpelling name.value)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterValue semicolonSpan after) :
    ∃ output, returnStatement identifierExpression input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan
        value := .returnStmt (some { span := name.span, value := .identifier name })
      } output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] := by
  have notSemicolon : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon) := by
    rintro ⟨span, current⟩; cases TokenAt.token_unique nameParsed.1 current
  exact returnStatement_trace_success_complete identifierExpression_trace_success_complete
    (.parsed markerSpan semicolonSpan marker
      (.present notSemicolon (.parsed (.identifier (boolean_absent_of_identifier nameParsed.1)
        (.parsed nameParsed (.hyphen hyphen))))) semicolon)

end Solcore.Test.SyntaxParserExpressionNameTraceProperties
