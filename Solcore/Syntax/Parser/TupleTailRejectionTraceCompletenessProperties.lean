import Solcore.Syntax.Parser.TupleTailRejectionTraceSoundnessProperties

/-! Independent raw tuple rejection derivations execute with adequate fuel.
Only strict cursor progress and the successful full-window frame bound the
recursive calls; neither token preservation nor input validity is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DelimitedTraceInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem tupleTail_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace)
    (adequate : input.remainingCount < fuel) :
    ∃ failure rejected, tupleTail nested opening fuel elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing elementsRev input after report trace with
  | zero => omega
  | succ fuel ih =>
      cases rejection with
      | commaMissing absent reported =>
          rcases (symbol_reject_reports_iff .comma .expression).mp ⟨absent, reported⟩ with ⟨failure, result, reportEq⟩
          exact ⟨failure, input, by simp only [tupleTail, result], rfl, reportEq, by simp⟩
      | elementRejected commaSpan comma absent child =>
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨_, rfl⟩
          rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) child with
            ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
          exact ⟨failure, rejected, by
            simp only [tupleTail, commaResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false, result],
            afterEq, reportEq, diagnostics⟩
      | closingMissing commaSpan comma absent child progress noComma noClosing reported =>
          rename_i afterComma value
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨_, rfl⟩
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
            ⟨next, childResult, afterEq, childEq⟩
          have frame := contextFrame childResult
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have noCommaNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
              next.cursor (.symbol .comma) := by simpa only [← afterEq, State.declarativeRemainder] using noComma
          have noClosingNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
              next.cursor (.symbol .rightParen) := by simpa only [← afterEq, State.declarativeRemainder] using noClosing
          have reportNext : DeclarativeGrammar.RejectAtReports next.file.id next.window.endByte
              { head := .symbol .rightParen, tail := [] } .expression next.declarativeRemainder report := by
            simpa only [frame.1, frame.2, afterEq] using reported
          rcases (closeTuple_reject_reports_iff opening (value :: elementsRev)).mp ⟨noClosingNext, reportNext⟩ with
            ⟨failure, result, reportEq⟩
          exact ⟨failure, next, by
            simp only [tupleTail, commaResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
              childResult, nextProgress, if_true, symbol_absent .comma noCommaNext, result],
            afterEq, reportEq, childEq⟩
      | laterRejected commaSpan nextSpan comma absent child progress nextComma tail =>
          rename_i afterComma afterElement value childEvents tailEvents
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨commaToken, rfl⟩
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
            ⟨next, childResult, afterEq, childEq⟩
          have frame := contextFrame childResult
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have nextCommaToken : DeclarativeGrammar.TokenAt next.tokens next.window.endIndex next.cursor
              { span := nextSpan, value := .symbol .comma } := by
            simpa only [← afterEq, State.declarativeRemainder] using nextComma
          have nextCommaPresent := symbol_present .comma
            (after := { next.declarativeRemainder with cursor := next.cursor + 1 }) ⟨nextCommaToken, rfl⟩
          have tailAtNext : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
              next.file.id next.window.endByte next.declarativeRemainder after report tailEvents := by
            simpa only [frame.1, frame.2, afterEq] using tail
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := commaToken.1
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          rcases ih (value :: elementsRev) tailAtNext nextAdequate with
            ⟨failure, rejected, result, finalEq, reportEq, diagnostics⟩
          refine ⟨failure, rejected, ?_, finalEq, reportEq, ?_⟩
          · simp only [tupleTail, commaResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
              childResult, nextProgress, if_true, nextCommaPresent]
            exact result
          · rw [diagnostics, childEq, List.append_assoc]
            rfl

theorem tupleTail_production_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (elementsRev : List Expr)
    {input : State} {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace) :
    ∃ failure rejected, tupleTail nested opening (input.remainingCount + 1) elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  tupleTail_trace_reject_complete successComplete rejectComplete contextFrame opening
    (input.remainingCount + 1) elementsRev rejection (by omega)

end Solcore.Syntax.Parser.ExpressionAtomInternals
