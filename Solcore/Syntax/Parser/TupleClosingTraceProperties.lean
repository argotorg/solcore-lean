import Solcore.Syntax.DeclarativeParenthesizedTraceGrammar
import Solcore.Syntax.Parser.DelimitedClosingTraceProperties
import Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts
import Solcore.Syntax.Parser.Expression.Atom

/-! Exact silent tuple closing. Forward elements determine group versus tuple;
the closing span is supplied by the token, never recovered by inverting cover. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem closing_forward_reverse (opening closing : SourceSpan) (elementsRev : List Expr) :
    (match elementsRev with
      | [only] => ({ span := SourceSpan.cover opening closing, value := .group only } : Expr)
      | _ => {
          span := SourceSpan.cover opening closing
          value := .tuple { span := SourceSpan.cover opening closing, elements := elementsRev.reverse } }) =
      DeclarativeGrammar.closeParenthesizedExpression opening closing elementsRev.reverse := by
  cases elementsRev with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          dsimp only
          unfold DeclarativeGrammar.closeParenthesizedExpression
          split
          · rename_i only same
            have length := congrArg List.length same
            simp at length
          · rfl

theorem closeTuple_eq_of_symbol (opening : Token) (elementsRev : List Expr) (input : State) :
    closeTuple opening elementsRev input = match symbol .rightParen .expression input with
      | .ok closing output => .ok (DeclarativeGrammar.closeParenthesizedExpression
          opening.span closing.span elementsRev.reverse) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  unfold closeTuple
  cases result : symbol .rightParen .expression input <;> simp only [bind, result, pure]
  case ok closing output =>
    have shape := closing_forward_reverse opening.span closing.span elementsRev
    cases elementsRev with
    | nil => rfl
    | cons first rest => cases rest <;> simpa only using congrArg (fun value => Reply.ok value output) shape

theorem closeTuple_success_trace_sound (opening : Token) (elementsRev : List Expr)
    {input output : State} {value : Expr}
    (result : closeTuple opening elementsRev input = .ok value output) :
    ∃ closingSpan, DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
      input.declarativeRemainder closingSpan output.declarativeRemainder ∧
      value = DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan elementsRev.reverse ∧
      output = { input with cursor := input.cursor + 1 } := by
  rw [closeTuple_eq_of_symbol] at result
  cases closingResult : symbol .rightParen .expression input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok closing next =>
      simp only [closingResult] at result
      cases result
      exact ⟨closing.span, symbol_success_exactTokenParses .rightParen .expression closingResult,
        rfl, (symbol_ok_tokenAt .rightParen .expression closingResult).2⟩

theorem closeTuple_trace_success_iff (opening : Token) (elementsRev : List Expr)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    ((∃ closingSpan, DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
      input.declarativeRemainder closingSpan after ∧
      value = DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan elementsRev.reverse) ∧ trace = []) ↔
    ∃ output, closeTuple opening elementsRev input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨⟨closingSpan, parsed, rfl⟩, rfl⟩
    have result := symbol_eq_ok_of_exactTokenParses .rightParen .expression parsed
    exact ⟨{ input with cursor := input.cursor + 1 }, by rw [closeTuple_eq_of_symbol, result],
      parsed.2.symm, by simp only [State.diagnostics, List.append_nil]⟩
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases closeTuple_success_trace_sound opening elementsRev result with ⟨closingSpan, parsed, valueEq, stateEq⟩
    refine ⟨⟨closingSpan, afterEq ▸ parsed, valueEq⟩, ?_⟩
    have : input.diagnostics ++ [] = input.diagnostics ++ trace := by
      simpa only [stateEq, State.diagnostics, List.append_nil] using diagnostics
    exact (List.append_cancel_left this).symm

end Solcore.Syntax.Parser.ExpressionAtomInternals
