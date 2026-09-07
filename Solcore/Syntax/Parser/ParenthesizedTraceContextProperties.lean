import Solcore.Syntax.Parser.ParenthesizedTraceCompletenessProperties

/-! Source/full-window context follows successful children independently of
diagnostic traces and token-carrier preservation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}

theorem tupleTail_success_context (contextFrame : ExpressionSuccessContext nested) (opening : Token) :
    ∀ fuel elementsRev input value output, tupleTail nested opening fuel elementsRev input = .ok value output →
      output.file = input.file ∧ output.window = input.window := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input value output result; simp [tupleTail] at result
  | succ fuel ih =>
      intro elementsRev input value output result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          have commaState := (symbol_ok_tokenAt .comma .expression commaResult).2
          subst afterComma
          simp only [commaResult] at result
          split at result
          · rcases closeTuple_success_trace_sound opening elementsRev result with ⟨_, _, _, stateEq⟩
            rw [stateEq]; exact ⟨rfl, rfl⟩
          · cases childResult : nested { input with cursor := input.cursor + 1 } with
            | invariant error => simp [childResult] at result
            | reject failure rejected => simp [childResult] at result
            | ok child next =>
                simp only [childResult] at result
                split at result
                · have frame := contextFrame childResult
                  split at result
                  · have tail := ih (child :: elementsRev) next value output result
                    exact ⟨tail.1.trans frame.1, tail.2.trans frame.2⟩
                  · rcases closeTuple_success_trace_sound opening (child :: elementsRev) result with ⟨_, _, _, stateEq⟩
                    rw [stateEq]; exact frame
                · contradiction

theorem parenthesized_success_context (contextFrame : ExpressionSuccessContext nested) :
    ExpressionSuccessContext (parenthesized nested) := by
  intro input output value result
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      have openingState := (symbol_ok_tokenAt .leftParen .expression openingResult).2
      subst afterOpening
      simp only [openingResult] at result
      split at result
      · rcases closeTuple_success_trace_sound opening [] result with ⟨_, _, _, stateEq⟩
        rw [stateEq]; exact ⟨rfl, rfl⟩
      · cases childResult : nested { input with cursor := input.cursor + 1 } with
        | invariant error => simp [childResult] at result
        | reject failure rejected => simp [childResult] at result
        | ok first next =>
            simp only [childResult] at result
            split at result
            · contradiction
            · have frame := contextFrame childResult
              split at result
              · have tail := tupleTail_success_context contextFrame opening (next.remainingCount + 1)
                  [first] next value output result
                exact ⟨tail.1.trans frame.1, tail.2.trans frame.2⟩
              · rcases closeTuple_success_trace_sound opening [first] result with ⟨_, _, _, stateEq⟩
                rw [stateEq]; exact frame

end Solcore.Syntax.Parser.ExpressionAtomInternals
