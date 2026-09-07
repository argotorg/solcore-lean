import Solcore.Syntax.Parser.BooleanIdentifierRejectionTraceProperties
import Solcore.Syntax.Parser.LiteralExpressionTraceProperties
import Solcore.Syntax.Parser.ReturnStatementSuccessTraceProperties

/-! Real literal/Boolean leaves preserve exact payloads and distinct failures.
The real literal-expression contracts also close one nonempty return instance. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserLiteralDiagnosticTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @coreLiteralTrace_outcome_total
example := @booleanIdentifierTrace_outcome_total
example := @CoreLiteralTraceRejects.disjoint_success
example := @BooleanIdentifierTraceRejects.disjoint_success
example := @literalExpression_trace_reject_sound
example := @literalExpression_trace_reject_complete

theorem decimal_keeps_spelling (spelling : String) {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .decimalLiteral spelling }) :
    coreLiteral input = .ok { span, value := .decimal spelling }
      { input with cursor := input.cursor + 1 } :=
  coreLiteral_eq_ok_of_ordinary (.decimal token)

theorem hexadecimal_keeps_spelling (spelling : String) {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .hexadecimalLiteral spelling }) :
    coreLiteral input = .ok { span, value := .hexadecimal spelling }
      { input with cursor := input.cursor + 1 } :=
  coreLiteral_eq_ok_of_ordinary (.hexadecimal token)

theorem string_keeps_spelling (spelling : String) {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .stringLiteral spelling }) :
    coreLiteral input = .ok { span, value := .string spelling }
      { input with cursor := input.cursor + 1 } :=
  coreLiteral_eq_ok_of_ordinary (.string token)

theorem true_keeps_identifier_shape {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .keyword .trueKw }) :
    booleanIdentifier input = .ok { span, value := "true" }
      { input with cursor := input.cursor + 1 } :=
  booleanIdentifier_eq_ok_of_ordinary (.trueKeyword token)

theorem false_keeps_identifier_shape {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .keyword .falseKw }) :
    booleanIdentifier input = .ok { span, value := "false" }
      { input with cursor := input.cursor + 1 } :=
  booleanIdentifier_eq_ok_of_ordinary (.falseKeyword token)

/-- The same offending semicolon has two different required expectations.
Both failures preserve every state field and leave their report uncommitted. -/
theorem same_token_retains_distinct_literal_and_boolean_expectations
    {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    coreLiteral input = .reject {
      span, found := some (.symbol .semicolon)
      expected := { head := .coreLiteral, tail := [] }, context := .expression } input ∧
    booleanIdentifier input = .reject {
      span, found := some (.symbol .semicolon)
      expected := { head := .expression, tail := [] }, context := .expression } input := by
  have literalAbsent : CoreLiteralAbsentAt input.declarativeRemainder := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨otherSpan, spelling, current⟩; cases TokenAt.token_unique token current
    · rintro ⟨otherSpan, spelling, current⟩; cases TokenAt.token_unique token current
    · rintro ⟨otherSpan, spelling, current⟩; cases TokenAt.token_unique token current
  have booleanAbsent : BooleanPatternAbsentAt input.declarativeRemainder := by
    constructor
    · rintro ⟨otherSpan, current⟩; cases TokenAt.token_unique token current
    · rintro ⟨otherSpan, current⟩; cases TokenAt.token_unique token current
  have current : CurrentInputAt input.file.id input.window.endByte input.declarativeRemainder
      span (some (.symbol .semicolon)) :=
    .token (current := { span, value := .symbol .semicolon }) token
  exact ⟨(coreLiteral_trace_reject_failure_iff.mp
      ⟨.absent literalAbsent, .reported current, rfl⟩).1,
    (booleanIdentifier_trace_reject_failure_iff.mp
      ⟨booleanAbsent, rfl, .reported current, rfl⟩).1⟩

/-- No physical carrier token can be consumed beyond the active window. The
literal failure uses the explicit byte boundary, not a token past that window. -/
theorem window_end_literal_failure_keeps_full_state {input : State}
    (atEnd : input.window.endIndex ≤ input.cursor) :
    coreLiteral input = .reject {
      span := { source := input.file.id
                startByte := input.window.endByte
                endByte := input.window.endByte }
      found := none, expected := { head := .coreLiteral, tail := [] }, context := .expression
    } input := by
  have absent : CoreLiteralAbsentAt input.declarativeRemainder := by
    refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨span, spelling, inside, _⟩ <;>
      change input.cursor < input.window.endIndex at inside <;> omega
  exact (coreLiteral_trace_reject_failure_iff.mp
    ⟨.absent absent, .reported (.windowEnd atEnd), rfl⟩).1

/-- A nonempty return with the real literal-expression parser needs no abstract
expression contract from its caller; the literal and both marker spans survive. -/
theorem real_literal_return_keeps_prior_events
    {input : State} {afterMarker afterValue after : Remainder} {literal : CoreLiteral}
    {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (valueParsed : CoreLiteralParses afterMarker literal afterValue)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterValue semicolonSpan after) :
    ∃ output, returnStatement literalExpression input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan
        value := .returnStmt (some { span := literal.span, value := .literal literal })
      } output ∧ output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  have notSemicolon : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon) := by
    rintro ⟨span, current⟩
    cases valueParsed with
    | decimal token => cases TokenAt.token_unique token current
    | hexadecimal token => cases TokenAt.token_unique token current
    | string token => cases TokenAt.token_unique token current
  simpa only [List.append_nil] using
    returnStatement_trace_success_complete literalExpression_trace_success_complete
      (.parsed markerSpan semicolonSpan marker
        (.present notSemicolon ⟨.parsed valueParsed, rfl⟩) semicolon)

end Solcore.Test.SyntaxParserLiteralDiagnosticTraceProperties
