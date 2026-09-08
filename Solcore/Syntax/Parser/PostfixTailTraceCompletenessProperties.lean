import Solcore.Syntax.Parser.PostfixTailSuccessTraceSoundnessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingTraceCompletenessProperties

/-! Finite independent postfix successes execute above a derivation-dependent
fuel threshold. Index children may rewind, so this threshold is deliberately
not bounded by remainingCount. No child progress or carrier law is introduced. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar DelimitedTraceInternals

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}

private theorem complete_at
    (successComplete : ParserTraceSuccessComplete nested nestedTrace)
    (contextFrame : ParserSuccessContext nested) (block : Parser Block)
    {source : SourceId} {endByte : Nat} {before after : Remainder} {base value : Expr}
    {trace : List ParseDiagnostic}
    (parsed : PostfixTailTraceParses nestedTrace source endByte before base value after trace) :
    ∀ input : State, input.file.id = source → input.window.endByte = endByte →
      input.declarativeRemainder = before →
      ∃ bound, ∀ fuel, bound ≤ fuel → ∃ output,
        postfixTail nested block fuel base input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  induction parsed with
  | done absent =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      refine ⟨1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨input, by simp only [postfixTail, symbol_absent .leftBracket absent.1,
            symbol_absent .leftParen absent.2.1, symbol_absent .dot absent.2.2,
            Bool.false_eq_true, if_false], rfl, (List.append_nil _).symm⟩
  | index openingSpan closingSpan opening child closing tail ih =>
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
          rcases tailComplete fuel (by omega) with ⟨output, result, afterEq, events⟩
          refine ⟨output, ?_, afterEq, ?_⟩
          · simpa only [postfixTail, openingPresent, if_true, openingResult, childResult,
              closingResult, postfixIndexTraceValue] using result
          · change output.diagnostics = _ at events
            rw [events]
            change next.diagnostics ++ _ = _
            rw [childEvents]
            exact List.append_assoc _ _ _
  | call indexAbsent arguments tail ih =>
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
          rcases tailComplete fuel (by omega) with ⟨output, result, afterEq, events⟩
          refine ⟨output, ?_, afterEq, ?_⟩
          · simpa only [postfixTail, symbol_absent .leftBracket indexAbsent, Bool.false_eq_true,
              if_false, callPresent, if_true, argumentResult, postfixCallTraceValue] using result
          · rw [events, argumentEvents]
            exact List.append_assoc _ _ _
  | field dotSpan indexAbsent callAbsent dot name tail ih =>
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
          rcases tailComplete fuel (by omega) with ⟨output, result, afterEq, events⟩
          refine ⟨output, ?_, afterEq, ?_⟩
          · simpa only [postfixTail, symbol_absent .leftBracket indexAbsent, symbol_absent .leftParen callAbsent,
              Bool.false_eq_true, if_false, dotPresent, if_true, dotResult, nameResult, postfixFieldTraceValue] using result
          · rw [events, nameEvents]
            exact List.append_assoc _ _ _

theorem postfixTail_trace_success_complete_eventually
    (successComplete : ParserTraceSuccessComplete nested nestedTrace)
    (contextFrame : ParserSuccessContext nested) (block : Parser Block)
    {input : State} {base value : Expr} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder base value after trace) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ output,
      postfixTail nested block fuel base input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  complete_at successComplete contextFrame block parsed input rfl rfl rfl

end Solcore.Syntax.Parser.ExpressionAtomInternals
