import Solcore.Syntax.Parser.ParenthesizedRejectionTraceSoundnessProperties
import Solcore.Syntax.Parser.TupleTailRejectionTraceCompletenessProperties

/-! Raw parenthesized rejection execution. The production tail fuel is exactly
the remaining count after the first successful child, plus one. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DelimitedTraceInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parenthesized_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceRejectComplete (parenthesized nested)
      (DeclarativeGrammar.ParenthesizedExpressionTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | openingMissing absent reported =>
      rcases (symbol_reject_reports_iff .leftParen .expression).mp ⟨absent, reported⟩ with ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [parenthesized, result], rfl, reportEq, by simp⟩
  | firstRejected openingSpan opening absent child =>
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
      exact ⟨failure, rejected, by
        simp only [parenthesized, openingResult, symbol_absent .rightParen
          (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false, result],
        afterEq, reportEq, diagnostics⟩
  | closingMissing openingSpan opening absent child progress noComma noClosing reported =>
      rename_i afterOpening value
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨next, childResult, afterEq, childEq⟩
      have frame := contextFrame childResult
      have nextProgress : ¬ next.cursor ≤ input.cursor + 1 := by
        have : input.cursor + 1 < next.cursor := by
          simpa only [← afterEq, State.declarativeRemainder] using progress
        omega
      have noCommaNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
          next.cursor (.symbol .comma) := by simpa only [← afterEq, State.declarativeRemainder] using noComma
      have noClosingNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
          next.cursor (.symbol .rightParen) := by simpa only [← afterEq, State.declarativeRemainder] using noClosing
      have reportNext : DeclarativeGrammar.RejectAtReports next.file.id next.window.endByte
          { head := .symbol .rightParen, tail := [] } .expression next.declarativeRemainder report := by
        simpa only [frame.1, frame.2, afterEq] using reported
      rcases (closeTuple_reject_reports_iff { span := openingSpan, value := .symbol .leftParen } [value]).mp
          ⟨noClosingNext, reportNext⟩ with ⟨failure, result, reportEq⟩
      exact ⟨failure, next, by
        simp only [parenthesized, openingResult, symbol_absent .rightParen
          (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
          childResult, nextProgress, symbol_absent .comma noCommaNext, result],
        afterEq, reportEq, childEq⟩
  | tailRejected openingSpan commaSpan opening absent child progress comma tail =>
      rename_i afterOpening afterFirst first childEvents tailEvents
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨next, childResult, afterEq, childEq⟩
      have frame := contextFrame childResult
      have nextProgress : ¬ next.cursor ≤ input.cursor + 1 := by
        have : input.cursor + 1 < next.cursor := by
          simpa only [← afterEq, State.declarativeRemainder] using progress
        omega
      have commaToken : DeclarativeGrammar.TokenAt next.tokens next.window.endIndex next.cursor
          { span := commaSpan, value := .symbol .comma } := by
        simpa only [← afterEq, State.declarativeRemainder] using comma
      have commaPresent := symbol_present .comma
        (after := { next.declarativeRemainder with cursor := next.cursor + 1 }) ⟨commaToken, rfl⟩
      have tailAtNext : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
          next.file.id next.window.endByte next.declarativeRemainder after report tailEvents := by
        simpa only [frame.1, frame.2, afterEq] using tail
      rcases tupleTail_production_trace_reject_complete successComplete rejectComplete contextFrame
          { span := openingSpan, value := .symbol .leftParen } [first] tailAtNext with
        ⟨failure, rejected, result, finalEq, reportEq, diagnostics⟩
      refine ⟨failure, rejected, ?_, finalEq, reportEq, ?_⟩
      · simp only [parenthesized, openingResult, symbol_absent .rightParen
          (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
          childResult, nextProgress, commaPresent, if_true]
        exact result
      · rw [diagnostics, childEq, List.append_assoc]
        rfl

end Solcore.Syntax.Parser.ExpressionAtomInternals
