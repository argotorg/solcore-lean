import Solcore.Test.SyntaxExpressionUnaryTraceSupport

/-! Canonical prefix order, complete postfix operands, and silent scanner
boundaries are consumed in the reverse direction from independent judgments.
The actual block is the explicitly supplied rejecting test leaf, not a general
recursive block parser. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionUnaryTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals ExpressionInternals SyntaxExpressionUnaryTraceSupport

private def source : SourceId := { origin := .main, path := "unary-trace.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (kind : Symbol) : Token := { span := span first last, value := .symbol kind }
private def name : Identifier := { span := span 2 5, value := "a-b" }
private def nameValue : Expr := { span := name.span, value := .identifier name }
private def nameEvent : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def one : Expr := { span := span 6 7, value := .literal { span := span 6 7, value := .decimal "1" } }
private def args : DelimitedList Expr := { span := span 5 8, elements := [one] }
private def callValue : Expr := postfixCallTraceValue nameValue args
private def fieldName : Identifier := { span := span 9 10, value := "c" }
private def fieldValue : Expr := postfixFieldTraceValue callValue (span 8 9) fieldName
private def operators : List (Located UnaryOp) := [⟨span 0 1, .logicalNot⟩, ⟨span 1 2, .bitNot⟩]
private def wrapped : Expr := DeclarativeGrammar.applyUnaryOperators operators fieldValue
private def tokens (suffix : List Token) : List Token :=
  [sym 0 1 .bang, sym 1 2 .tilde, { span := name.span, value := .identifier name.value },
    sym 5 6 .leftParen, { span := span 6 7, value := .decimalLiteral "1" }, sym 7 8 .rightParen] ++ suffix
private def rem (suffix : List Token) (cursor : Nat) : Remainder :=
  { tokens := (tokens suffix).toArray, endIndex := (tokens suffix).length, cursor }
private def state (suffix : List Token) (cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := (tokens suffix).toArray, cursor
  window := { endIndex := (tokens suffix).length, endByte := 99 }, diagnosticsRev := prior.reverse
}

private theorem prefix_trace (suffix : List Token) : UnaryOperatorsParses (rem suffix 0) operators (rem suffix 2) :=
  .next (afterOperator := rem suffix 1) ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
    (.next ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
      (.done (by simp [UnaryOperatorAbsentAt, TokenKindAbsentAt, TokenAt, rem, tokens])))

private theorem atom_name (suffix : List Token) :
    ExpressionAtomLayerTraceParses LiteralExpressionTraceParses LiteralExpressionTraceRejects blockTrace blockRejects
      source 99 (rem suffix 2) nameValue (rem suffix 3) [nameEvent] := by
  apply ExpressionAtomTraceParses.core
  apply ExpressionAtomDispatchTraceParses.selected .name
  · exact .name (by simp [CoreLiteralStartsAt, TokenAt, rem, tokens])
      (.inr (.inr ⟨name.span, name.value, ⟨by simp [rem, tokens], rfl⟩⟩))
  · exact .parsed (.identifier (by simp [BooleanPatternAbsentAt, TokenKindAbsentAt, TokenAt, rem, tokens])
      (.parsed ⟨⟨by simp [rem, tokens], rfl⟩, rfl, rfl, rfl⟩
        (.hyphen (by unfold IdentifierHyphenSpelling name; decide))))

private theorem arguments_trace (suffix : List Token) :
    NoTrailingDelimitedListTraceParses .leftParen .rightParen true LiteralExpressionTraceParses source 99
      (rem suffix 3) args (rem suffix 6) [] := by
  apply NoTrailingDelimitedListTraceParses.nonempty (afterOpening := rem suffix 4) (afterFirst := rem suffix 5)
    (first := one) (rest := []) (firstEvents := []) (tailEvents := []) (span 5 6) (span 7 8)
  · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
  · exact .absent (by simp [TokenKindAbsentAt, TokenAt, rem, tokens])
  · exact ⟨.parsed (.decimal ⟨by simp [rem, tokens], rfl⟩), rfl⟩
  · change 4 < 5; decide
  · exact .close (by simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym])
      ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩

private def successSuffix : List Token :=
  [sym 8 9 .dot, { span := fieldName.span, value := .identifier fieldName.value }, sym 10 11 .semicolon]
private def successState (prior : List ParseDiagnostic) : State :=
  { state successSuffix 8 prior with diagnosticsRev := nameEvent :: prior.reverse }

private theorem success_trace : ExpressionUnaryTraceParses postfixTrace source 99
    (rem successSuffix 0) wrapped (rem successSuffix 8) [nameEvent] := by
  apply ExpressionUnaryTraceParses.parsed (prefix_trace successSuffix)
  apply ExpressionPostfixTraceParses.parsed (tailEvents := []) (atom_name successSuffix)
  apply PostfixTailTraceParses.call (afterArguments := rem successSuffix 6) (argumentEvents := []) (tailEvents := [])
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · exact arguments_trace successSuffix
  · apply PostfixTailTraceParses.field (afterDot := rem successSuffix 7) (afterName := rem successSuffix 8)
      (nameEvents := []) (tailEvents := []) (span 8 9)
    · simp [TokenKindAbsentAt, TokenAt, rem, tokens, successSuffix, sym]
    · simp [TokenKindAbsentAt, TokenAt, rem, tokens, successSuffix, sym]
    · exact ⟨⟨by decide, rfl⟩, rfl⟩
    · exact .parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.clean (by unfold IdentifierHyphenSpelling fieldName; decide))
    · exact .done (by simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, rem, tokens, successSuffix, sym])

/-- Bang is outermost and tilde wraps the complete call/field operand. Exactly
one checked-name event follows all prior diagnostics; the semicolon is unread. -/
theorem source_order_prefix_wraps_maximal_postfix (prior : List ParseDiagnostic) :
    expressionUnary literalExpression blockParser (state successSuffix 0 prior) = .ok wrapped (successState prior) ∧
    (successState prior).diagnostics = prior ++ [nameEvent] ∧
    (successState prior).peek? = some (sym 10 11 .semicolon) := by
  refine ⟨success_of_trace (input := state successSuffix 0 prior) success_trace, ?_, rfl⟩
  simp only [successState, State.diagnostics, List.reverse_cons, List.reverse_reverse]

theorem unary_ast_order_and_spans :
    wrapped = { span := span 0 10, value := .unary ⟨span 0 1, .logicalNot⟩ {
      span := span 1 10, value := .unary ⟨span 1 2, .bitNot⟩ {
        span := span 2 10, value := .field {
          span := span 2 8, value := .call nameValue args
        } (span 8 9) fieldName
      }
    }} := rfl

theorem duplicate_prior_diagnostics_survive_unary (prior : List ParseDiagnostic) :
    expressionUnary literalExpression blockParser (state successSuffix 0 (prior ++ [nameEvent, nameEvent])) =
      .ok wrapped (successState (prior ++ [nameEvent, nameEvent])) ∧
    (successState (prior ++ [nameEvent, nameEvent])).diagnostics = prior ++ [nameEvent, nameEvent, nameEvent] := by
  have result := source_order_prefix_wraps_maximal_postfix (prior ++ [nameEvent, nameEvent])
  exact ⟨result.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

private def rejectSuffix : List Token := [sym 8 9 .dot, sym 9 10 .semicolon]
private def failure : Failure := {
  span := span 9 10, found := some (.symbol .semicolon)
  expected := { head := .identifier, tail := [] }, context := .expression
}
private def failedState (prior : List ParseDiagnostic) : State :=
  { state rejectSuffix 7 prior with diagnosticsRev := nameEvent :: prior.reverse }
private theorem rejection_trace : ExpressionUnaryTraceRejects postfixRejects source 99
    (rem rejectSuffix 0) (rem rejectSuffix 7) failure.toDiagnostic [nameEvent] := by
  apply ExpressionUnaryTraceRejects.postfixRejected (prefix_trace rejectSuffix)
  apply ExpressionPostfixTraceRejects.tailRejected (tailEvents := []) (atom_name rejectSuffix)
  apply PostfixTailTraceRejects.callLaterRejected (afterArguments := rem rejectSuffix 6)
    (argumentEvents := []) (tailEvents := [])
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · exact arguments_trace rejectSuffix
  · apply PostfixTailTraceRejects.fieldNameRejected (afterDot := rem rejectSuffix 7) (span 8 9)
    · simp [TokenKindAbsentAt, TokenAt, rem, tokens, rejectSuffix, sym]
    · simp [TokenKindAbsentAt, TokenAt, rem, tokens, rejectSuffix, sym]
    · exact ⟨⟨by decide, rfl⟩, rfl⟩
    · simp [IdentifierAbsentAt, TokenAt, rem, tokens, rejectSuffix, sym]
    · exact .reported (.token (current := sym 9 10 .semicolon) ⟨by decide, rfl⟩)

/-- Prefix operators emit nothing, the checked name remains emitted, and the
terminal field report remains uncommitted even after a successful call suffix. -/
theorem postfix_failure_after_prefix_preserves_only_prior_events (prior : List ParseDiagnostic) :
    expressionUnary literalExpression blockParser (state rejectSuffix 0 prior) = .reject failure (failedState prior) ∧
    (failedState prior).diagnostics = prior ++ [nameEvent] ∧
    (failedState prior).peek? = some (sym 9 10 .semicolon) := by
  refine ⟨reject_of_trace (input := state rejectSuffix 0 prior) rejection_trace, ?_, rfl⟩
  simp only [failedState, State.diagnostics, List.reverse_cons, List.reverse_reverse]

private def minusInput (prior : List ParseDiagnostic) : State :=
  { state [] 0 prior with tokens := #[sym 0 1 .minus, sym 1 2 .bang], window := { endIndex := 2, endByte := 99 } }
private def hiddenInput (prior : List ParseDiagnostic) : State :=
  { state [] 0 prior with window := { endIndex := 0, endByte := 99 } }
private def missingInput (prior : List ParseDiagnostic) : State :=
  { state [] 0 prior with tokens := #[], window := { endIndex := 3, endByte := 99 } }

/-- Leading minus is not a canonical unary token, so it and the following bang
remain untouched. The independent absent guard drives the exact silent result. -/
theorem minus_stops_prefix_scanning (prior : List ParseDiagnostic) :
    unaryOperators 3 [] (minusInput prior) = .ok [] (minusInput prior) ∧
    (minusInput prior).peek? = some (sym 0 1 .minus) ∧
    (minusInput prior).tokens[1]? = some (sym 1 2 .bang) := by
  refine ⟨unaryOperators_trace_success_complete (input := minusInput prior) (.done ?_), rfl, rfl⟩
  simp [UnaryOperatorAbsentAt, TokenKindAbsentAt, TokenAt, minusInput, state, State.declarativeRemainder, sym]

theorem hidden_and_missing_prefixes_are_silent (prior : List ParseDiagnostic) :
    unaryOperators 1 [] (hiddenInput prior) = .ok [] (hiddenInput prior) ∧
    unaryOperators 4 [] (missingInput prior) = .ok [] (missingInput prior) ∧
    (hiddenInput prior).tokens[0]? = some (sym 0 1 .bang) ∧
    (hiddenInput prior).peek? = none ∧ (missingInput prior).atEnd = false := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · exact unaryOperators_trace_success_complete (input := hiddenInput prior) (.done (by
      simp [UnaryOperatorAbsentAt, TokenKindAbsentAt, TokenAt, hiddenInput, State.declarativeRemainder]))
  · exact unaryOperators_trace_success_complete (input := missingInput prior) (.done (by
      simp [UnaryOperatorAbsentAt, TokenKindAbsentAt, TokenAt, missingInput, State.declarativeRemainder]))

end Solcore.Test.SyntaxExpressionUnaryTraceProperties
