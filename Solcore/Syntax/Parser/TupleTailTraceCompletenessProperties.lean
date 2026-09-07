import Solcore.Syntax.Parser.ParenthesizedTraceSoundnessProperties
import Solcore.Syntax.DeclarativeParenthesizedTraceProperties

/-! Successful tuple suffixes execute with sufficient remaining-token fuel.
Only successful source/full-window preservation and strict grammar progress
bound recursion; neither source validity nor a token-carrier law is needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DelimitedTraceInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem tupleTailTrace_comma_present {input : State} {values : List Expr} {closingSpan : SourceSpan}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder values closingSpan after trace) : isSymbol input .comma = true := by
  rcases parsed.comma_present with ⟨span, token⟩
  exact symbol_present .comma (after := { input.declarativeRemainder with cursor := input.cursor + 1 }) ⟨token, rfl⟩

theorem tupleTail_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} {suffix : List Expr} {closingSpan : SourceSpan}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder suffix closingSpan after trace)
    (adequate : input.remainingCount < fuel) :
    ∃ output, tupleTail nested opening fuel elementsRev input = .ok
        (DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan (elementsRev.reverse ++ suffix)) output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing elementsRev input suffix closingSpan after trace with
  | zero => omega
  | succ fuel ih =>
      cases parsed with
      | trailing commaSpan closingSpan comma finish =>
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨_, rfl⟩
          have closingPresent := symbol_present .rightParen
            (input := { input with cursor := input.cursor + 1 }) finish
          rcases (closeTuple_trace_success_iff opening elementsRev
              (input := { input with cursor := input.cursor + 1 })).mp ⟨⟨closingSpan, finish, rfl⟩, rfl⟩ with
            ⟨output, result, afterEq, diagnostics⟩
          exact ⟨output, by simpa only [tupleTail, commaResult, closingPresent, if_true, List.append_nil] using result,
            afterEq, diagnostics⟩
      | final commaSpan closingSpan comma absent child progress noComma finish =>
          rename_i afterComma afterElement value
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨_, rfl⟩
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
            ⟨next, childResult, afterEq, childEq⟩
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have noCommaNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
              next.cursor (.symbol .comma) := by simpa only [← afterEq, State.declarativeRemainder] using noComma
          have finishNext : DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
              next.declarativeRemainder closingSpan after := by simpa only [afterEq] using finish
          rcases (closeTuple_trace_success_iff opening (value :: elementsRev)).mp
              ⟨⟨closingSpan, finishNext, rfl⟩, rfl⟩ with ⟨output, result, finalEq, diagnostics⟩
          refine ⟨output, ?_, finalEq, ?_⟩
          · simp only [tupleTail, commaResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true,
              if_false, childResult, nextProgress, if_true, symbol_absent .comma noCommaNext]
            simpa only [List.reverse_cons] using result
          · rw [diagnostics, List.append_nil]
            exact childEq
      | next commaSpan closingSpan comma absent child progress tail =>
          rename_i afterComma afterElement value rest headEvents tailEvents
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨commaToken, rfl⟩
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
            ⟨next, childResult, afterEq, childEq⟩
          have frame := contextFrame childResult
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have tailAtNext : DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace
              next.file.id next.window.endByte next.declarativeRemainder rest closingSpan after tailEvents := by
            simpa only [frame.1, frame.2, afterEq] using tail
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := commaToken.1
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          rcases ih (value :: elementsRev) tailAtNext nextAdequate with ⟨output, result, finalEq, diagnostics⟩
          refine ⟨output, ?_, finalEq, ?_⟩
          · simp only [tupleTail, commaResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true,
              if_false, childResult, nextProgress, if_true, tupleTailTrace_comma_present tailAtNext]
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using result
          · rw [diagnostics, childEq]; exact List.append_assoc _ _ _

theorem tupleTail_production_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (elementsRev : List Expr)
    {input : State} {suffix : List Expr} {closingSpan : SourceSpan}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder suffix closingSpan after trace) :
    ∃ output, tupleTail nested opening (input.remainingCount + 1) elementsRev input = .ok
        (DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan (elementsRev.reverse ++ suffix)) output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  tupleTail_trace_success_complete successComplete contextFrame opening (input.remainingCount + 1) elementsRev parsed (by omega)

end Solcore.Syntax.Parser.ExpressionAtomInternals
