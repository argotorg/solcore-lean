import Solcore.Syntax.Parser.TupleTailTraceCompletenessProperties

/-! Complete actual parenthesized success. In the tuple branch production
fuel is afterFirst.remainingCount + 1, exactly as in the implementation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DelimitedTraceInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem parenthesized_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceSuccessComplete (parenthesized nested)
      (DeclarativeGrammar.ParenthesizedExpressionTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | empty openingSpan closingSpan opening finish =>
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      have closingPresent := symbol_present .rightParen
        (input := { input with cursor := input.cursor + 1 }) finish
      rcases (closeTuple_trace_success_iff { span := openingSpan, value := .symbol .leftParen } []
          (input := { input with cursor := input.cursor + 1 })).mp ⟨⟨closingSpan, finish, rfl⟩, rfl⟩ with
        ⟨output, result, afterEq, diagnostics⟩
      exact ⟨output, by simpa only [parenthesized, openingResult, closingPresent, if_true, List.reverse_nil] using result,
        afterEq, diagnostics⟩
  | group openingSpan closingSpan opening absent child progress noComma finish =>
      rename_i afterOpening afterElement element
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨next, childResult, afterEq, childEq⟩
      have nextProgress : input.cursor + 1 < next.cursor := by
        simpa only [← afterEq, State.declarativeRemainder] using progress
      have noCommaNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
          next.cursor (.symbol .comma) := by simpa only [← afterEq, State.declarativeRemainder] using noComma
      have finishNext : DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
          next.declarativeRemainder closingSpan after := by simpa only [afterEq] using finish
      rcases (closeTuple_trace_success_iff { span := openingSpan, value := .symbol .leftParen } [element]).mp
          ⟨⟨closingSpan, finishNext, rfl⟩, rfl⟩ with ⟨output, result, finalEq, diagnostics⟩
      refine ⟨output, ?_, finalEq, ?_⟩
      · simpa only [parenthesized, openingResult, symbol_absent .rightParen
          (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
          childResult, Nat.not_le_of_gt nextProgress, symbol_absent .comma noCommaNext,
          List.reverse_cons, List.reverse_nil, List.nil_append] using result
      · rw [diagnostics, List.append_nil]; exact childEq
  | tuple openingSpan closingSpan opening absent child progress tail =>
      rename_i afterOpening afterFirst first rest headEvents tailEvents
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨next, childResult, afterEq, childEq⟩
      have frame := contextFrame childResult
      have nextProgress : input.cursor + 1 < next.cursor := by
        simpa only [← afterEq, State.declarativeRemainder] using progress
      have tailAtNext : DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace
          next.file.id next.window.endByte next.declarativeRemainder rest closingSpan after tailEvents := by
        simpa only [frame.1, frame.2, afterEq] using tail
      rcases tupleTail_production_trace_success_complete successComplete contextFrame
          { span := openingSpan, value := .symbol .leftParen } [first] tailAtNext with
        ⟨output, result, finalEq, diagnostics⟩
      refine ⟨output, ?_, finalEq, ?_⟩
      · simp only [parenthesized, openingResult, symbol_absent .rightParen
          (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
          childResult, Nat.not_le_of_gt nextProgress, tupleTailTrace_comma_present tailAtNext, if_true]
        simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] using result
      · rw [diagnostics, childEq]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser.ExpressionAtomInternals
