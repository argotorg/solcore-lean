import Solcore.Syntax.Parser.PostfixTailRejectionTraceSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingTraceCompletenessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingRejectionTraceCompletenessProperties

/-! Every finite independent rejection executes at all sufficiently large
postfix fuels. The threshold counts derivation steps, not cursor distance;
successful index children may rewind and failed children need no frame law. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar DelimitedTraceInternals

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem complete_at
    (successComplete : ParserTraceSuccessComplete nested nestedTrace)
    (rejectComplete : ParserTraceRejectComplete nested nestedRejects)
    (contextFrame : ParserSuccessContext nested) (block : Parser Block)
    {source : SourceId} {endByte : Nat} {before after : Remainder} {base : Expr}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : PostfixTailTraceRejects nestedTrace nestedRejects source endByte before base after report trace) :
    ∀ input : State, input.file.id = source → input.window.endByte = endByte →
      input.declarativeRemainder = before →
      ∃ bound, ∀ fuel, bound ≤ fuel → ∃ failure rejected,
        postfixTail nested block fuel base input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  induction rejection with
  | indexNestedRejected openingSpan opening child =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftBracket .expression opening
      have openingPresent := symbol_present .leftBracket opening
      rcases opening with ⟨_, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      refine ⟨1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨failure, rejected, by simp only [postfixTail, openingPresent, if_true, openingResult, result],
            afterEq, reportEq, events⟩
  | indexClosingMissing openingSpan opening child absent reported =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftBracket .expression opening
      have openingPresent := symbol_present .leftBracket opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨next, childResult, nextAfter, childEvents⟩
      have frame := contextFrame childResult
      have absentAt := absent
      rw [← nextAfter] at absentAt
      have reportedAt := reported
      rw [← nextAfter, ← frame.1, ← frame.2] at reportedAt
      rcases (symbol_reject_reports_iff .rightBracket .expression).mp ⟨absentAt, reportedAt⟩ with
        ⟨failure, result, reportEq⟩
      refine ⟨1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨failure, next, by simp only [postfixTail, openingPresent, if_true, openingResult, childResult, result],
            nextAfter, reportEq, childEvents⟩
  | indexLaterRejected openingSpan closingSpan opening child closing tail ih =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftBracket .expression opening
      have openingPresent := symbol_present .leftBracket opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨next, childResult, nextAfter, childEvents⟩
      have frame := contextFrame childResult
      have closingAt := closing
      rw [← nextAfter] at closingAt
      have closingResult := symbol_eq_ok_of_exactTokenParses .rightBracket .expression closingAt
      rcases ih { next with cursor := next.cursor + 1 }
          (by simp only [frame.1]) (by simp only [frame.2]) closingAt.2.symm with ⟨bound, tailComplete⟩
      refine ⟨bound + 1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          rcases tailComplete fuel (by omega) with ⟨failure, rejected, result, afterEq, reportEq, events⟩
          refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
          · simpa only [postfixTail, openingPresent, if_true, openingResult, childResult,
              closingResult, postfixIndexTraceValue] using result
          · rw [events]
            change next.diagnostics ++ _ = _
            rw [childEvents]
            exact List.append_assoc _ _ _
  | callArgumentsRejected openingSpan indexAbsent opening child =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have openingParsed : ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan
          { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨opening, rfl⟩
      have callPresent := symbol_present .leftParen openingParsed
      rcases delimitedNoTrailing_trace_reject_complete successComplete rejectComplete contextFrame
          .leftParen .rightParen true .expression .expression child with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      refine ⟨1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨failure, rejected, by simp only [postfixTail, symbol_absent .leftBracket indexAbsent,
            Bool.false_eq_true, if_false, callPresent, if_true, result], afterEq, reportEq, events⟩
  | callLaterRejected indexAbsent arguments tail ih =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      rcases delimitedNoTrailing_trace_success_complete successComplete contextFrame
          .leftParen .rightParen true .expression .expression arguments with
        ⟨next, argumentResult, nextAfter, argumentEvents⟩
      have frame := delimitedNoTrailing_success_context contextFrame
        .leftParen .rightParen true .expression .expression argumentResult
      have callPresent : isSymbol input .leftParen = true := by
        cases arguments with
        | empty _ _ _ opening _ | nonempty _ _ opening _ _ _ _ => exact symbol_present .leftParen opening
      rcases ih next (congrArg SourceFile.id frame.1) (congrArg TokenWindow.endByte frame.2) nextAfter with
        ⟨bound, tailComplete⟩
      refine ⟨bound + 1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          rcases tailComplete fuel (by omega) with ⟨failure, rejected, result, afterEq, reportEq, events⟩
          refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
          · simpa only [postfixTail, symbol_absent .leftBracket indexAbsent, Bool.false_eq_true,
              if_false, callPresent, if_true, argumentResult, postfixCallTraceValue] using result
          · rw [events, argumentEvents]
            exact List.append_assoc _ _ _
  | fieldNameRejected dotSpan indexAbsent callAbsent dot nameAbsent reported =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have dotResult := symbol_eq_ok_of_exactTokenParses .dot .expression dot
      have dotPresent := symbol_present .dot dot
      rcases dot with ⟨_, rfl⟩
      rcases (identifier_reject_reports_iff .expression (input := { input with cursor := input.cursor + 1 })).mp
          ⟨nameAbsent, reported⟩ with ⟨failure, result, reportEq⟩
      refine ⟨1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨failure, { input with cursor := input.cursor + 1 }, by
            simp only [postfixTail, symbol_absent .leftBracket indexAbsent, symbol_absent .leftParen callAbsent,
              Bool.false_eq_true, if_false, dotPresent, if_true, dotResult, result],
            rfl, reportEq, (List.append_nil _).symm⟩
  | fieldLaterRejected dotSpan indexAbsent callAbsent dot name tail ih =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have dotResult := symbol_eq_ok_of_exactTokenParses .dot .expression dot
      have dotPresent := symbol_present .dot dot
      rcases dot with ⟨_, rfl⟩
      rcases (identifier_trace_success_iff .expression (input := { input with cursor := input.cursor + 1 })).mp name with
        ⟨next, nameResult, nextAfter, nameEvents⟩
      have frame := identifier_success_context_eq .expression nameResult
      rcases ih next (by simp only [frame.1]) (by simp only [frame.2]) nextAfter with ⟨bound, tailComplete⟩
      refine ⟨bound + 1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          rcases tailComplete fuel (by omega) with ⟨failure, rejected, result, afterEq, reportEq, events⟩
          refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
          · simpa only [postfixTail, symbol_absent .leftBracket indexAbsent, symbol_absent .leftParen callAbsent,
              Bool.false_eq_true, if_false, dotPresent, if_true, dotResult, nameResult, postfixFieldTraceValue] using result
          · rw [events, nameEvents]
            exact List.append_assoc _ _ _

theorem postfixTail_trace_reject_complete_eventually
    (successComplete : ParserTraceSuccessComplete nested nestedTrace)
    (rejectComplete : ParserTraceRejectComplete nested nestedRejects)
    (contextFrame : ParserSuccessContext nested) (block : Parser Block)
    {input : State} {base : Expr} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after report trace) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ failure rejected,
      postfixTail nested block fuel base input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  complete_at successComplete rejectComplete contextFrame block rejection input rfl rfl rfl

end Solcore.Syntax.Parser.ExpressionAtomInternals
