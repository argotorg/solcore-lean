import Solcore.Test.SyntaxPostfixTailTraceSupport

/-! Reverse consumers derive actual complete postfix replies from independent
token/trace witnesses. The literal child supplies the production fuel bound;
the arbitrary block is unused. These are maximal tails, not full expressions. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxPostfixTailTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals SyntaxPostfixTailTraceSupport

private def successfulSuffix : List Token := [sym 11 12 .semicolon]
private def finished (prior : List ParseDiagnostic) : State :=
  { state successfulSuffix 8 prior with diagnosticsRev := nameEvent :: prior.reverse }

private theorem successful_trace :
    PostfixTailTraceParses LiteralExpressionTraceParses source 99 (rem successfulSuffix 0)
      base callValue (rem successfulSuffix 8) [nameEvent] :=
  prefix_success successfulSuffix (.done (by
    simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, successfulSuffix, rem, tokens, sym]))

/-- One warning precedes the silent index and call. The semicolon is unread,
and every complete State field, including arbitrary prior diagnostics, is fixed. -/
theorem mixed_suffixes_return_exact_state (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail literalExpression block 10 base (state successfulSuffix 0 prior) =
      .ok callValue (finished prior) ∧
    (finished prior).diagnostics = prior ++ [nameEvent] ∧
    (finished prior).cursor = 8 ∧ (finished prior).peek? = some (sym 11 12 .semicolon) := by
  refine ⟨success_of_trace block (input := state successfulSuffix 0 prior) successful_trace, ?_, rfl, rfl⟩
  simp only [finished, State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- The nested AST retains separate base, field-dot, bracket, and call spans. -/
theorem mixed_suffix_ast_is_fully_located :
    callValue = {
      span := span 0 11
      value := .call {
        span := span 0 8
        value := .index {
          span := span 0 5
          value := .field base (span 1 2) name
        } (span 5 8) (literal 6 7 "1")
      } { span := span 8 11, elements := [literal 9 10 "2"] }
    } := rfl

theorem duplicate_prior_names_are_not_deduplicated (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail literalExpression block 10 base (state successfulSuffix 0 (prior ++ [nameEvent, nameEvent])) =
      .ok callValue (finished (prior ++ [nameEvent, nameEvent])) ∧
    (finished (prior ++ [nameEvent, nameEvent])).diagnostics = prior ++ [nameEvent, nameEvent, nameEvent] := by
  have result := mixed_suffixes_return_exact_state block (prior ++ [nameEvent, nameEvent])
  exact ⟨result.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

private def terminal (boolean : Bool) : Token :=
  if boolean then { span := span 12 16, value := .keyword .trueKw } else sym 12 13 .semicolon
private def rejectedSuffix (boolean : Bool) : List Token := [sym 11 12 .dot, terminal boolean]
private def terminalFailure (boolean : Bool) : Failure := {
  span := (terminal boolean).span, found := some (terminal boolean).value
  expected := { head := .identifier, tail := [] }, context := .expression
}
private def rejectedState (boolean : Bool) (prior : List ParseDiagnostic) : State :=
  { state (rejectedSuffix boolean) 9 prior with diagnosticsRev := nameEvent :: prior.reverse }

private theorem later_field_rejection (boolean : Bool) :
    PostfixTailTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects source 99
      (rem (rejectedSuffix boolean) 0) base (rem (rejectedSuffix boolean) 9)
      (terminalFailure boolean).toDiagnostic [nameEvent] := by
  apply prefix_rejected (trace := []) (rejectedSuffix boolean)
  apply PostfixTailTraceRejects.fieldNameRejected (afterDot := rem (rejectedSuffix boolean) 9) (span 11 12)
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, rejectedSuffix, sym]
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, rejectedSuffix, sym]
  · exact ⟨⟨by simp [rem, tokens, rejectedSuffix], rfl⟩, rfl⟩
  · cases boolean <;> simp [IdentifierAbsentAt, TokenAt, rem, tokens, rejectedSuffix, terminal, sym]
  · exact .reported (.token (current := terminal boolean) ⟨by simp [rem, tokens, rejectedSuffix], rfl⟩)

/-- The terminal identifier Failure is not appended to the earlier hyphen
event, including when the offending token is the Boolean keyword `true`. -/
theorem later_field_failure_preserves_prefix_only (boolean : Bool) (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail literalExpression block 11 base (state (rejectedSuffix boolean) 0 prior) =
      .reject (terminalFailure boolean) (rejectedState boolean prior) ∧
    (rejectedState boolean prior).diagnostics = prior ++ [nameEvent] ∧
    (rejectedState boolean prior).peek? = some (terminal boolean) := by
  refine ⟨reject_of_trace block (input := state (rejectedSuffix boolean) 0 prior)
    (later_field_rejection boolean), ?_, rfl⟩
  simp only [rejectedState, State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- The raw Boolean name grammar succeeds here, but postfix field parsing uses
the stricter checked-identifier grammar and rejects the very same token. -/
theorem boolean_name_is_not_a_field_identifier :
    ExpressionNameTraceParses source 99 (rem (rejectedSuffix true) 9)
      { span := span 12 16, value := "true" } (rem (rejectedSuffix true) 10) [] ∧
    IdentifierAbsentAt (rem (rejectedSuffix true) 9) := by
  constructor
  · exact .boolean ⟨.trueKeyword ⟨by decide, rfl⟩, rfl⟩
  · simp [IdentifierAbsentAt, TokenAt, rem, tokens, rejectedSuffix, terminal]

theorem boundary_done_keeps_arbitrary_base_and_events (block : Parser Block) (value : Expr) (prior : List ParseDiagnostic) :
    postfixTail literalExpression block 2 value (state successfulSuffix 8 prior) =
      .ok value (state successfulSuffix 8 prior) :=
  success_of_trace block (input := state successfulSuffix 8 prior) (.done (by
    simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, successfulSuffix, tokens, sym,
      state, State.declarativeRemainder]))

private def hidden (prior : List ParseDiagnostic) : State :=
  { state successfulSuffix 0 prior with window := { endIndex := 0, endByte := 99 } }
private def missing (prior : List ParseDiagnostic) : State :=
  { state successfulSuffix 0 prior with tokens := #[], window := { endIndex := 99, endByte := 99 } }

/-- A stored dot outside the visible window and an absent backing slot both
end the tail silently; neither authorizes consuming the hidden/unavailable dot. -/
theorem hidden_and_missing_suffixes_finish_silently (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail literalExpression block 1 base (hidden prior) = .ok base (hidden prior) ∧
    postfixTail literalExpression block 100 base (missing prior) = .ok base (missing prior) ∧
    (hidden prior).tokens[0]? = some (sym 1 2 .dot) ∧ (hidden prior).peek? = none ∧
    (missing prior).atEnd = false ∧ (missing prior).peek? = none := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact success_of_trace block (input := hidden prior) (.done (by
      simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, hidden, state, State.declarativeRemainder]))
  · exact success_of_trace block (input := missing prior) (.done (by
      simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, missing, state, State.declarativeRemainder]))

end Solcore.Test.SyntaxPostfixTailTraceProperties
