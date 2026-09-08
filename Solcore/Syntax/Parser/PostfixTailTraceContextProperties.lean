import Solcore.Syntax.Parser.DelimitedNoTrailingTraceContextProperties
import Solcore.Syntax.Parser.PragmaItemsContextProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Postfix context laws for every fuel and arbitrary states. Success retains
the full window under the successful child frame. Rejection retains the file
and any explicit window observation under separate successful/rejected child
frames. No carrier, progress, ordinary, validity, or block contract is used. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}

theorem postfixTail_success_context (success : ParserSuccessContext nested)
    (block : Parser Block) : ∀ fuel base, ParserSuccessContext (postfixTail nested block fuel base) := by
  intro fuel
  induction fuel with
  | zero => intro base input output value result; simp [postfixTail] at result
  | succ fuel ih =>
      intro base input output value result
      unfold postfixTail at result
      split at result
      · cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject failure rejected => simp [openingResult] at result
        | ok opening afterOpening =>
            simp only [openingResult] at result
            have openingShape := (symbol_ok_tokenAt .leftBracket .expression openingResult).2
            subst afterOpening
            cases childResult : nested { input with cursor := input.cursor + 1 } with
            | invariant error => simp [childResult] at result
            | reject failure rejected => simp [childResult] at result
            | ok index next =>
                simp only [childResult] at result
                have frame := success childResult
                cases closingResult : symbol .rightBracket .expression next with
                | invariant error => simp [closingResult] at result
                | reject failure rejected => simp [closingResult] at result
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    have held := ih _ result
                    rw [(symbol_ok_tokenAt .rightBracket .expression closingResult).2] at held
                    exact ⟨held.1.trans frame.1, held.2.trans frame.2⟩
      · split at result
        · cases argumentsResult : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments next =>
              simp only [argumentsResult] at result
              have frame := delimitedNoTrailing_success_context success .leftParen .rightParen true .expression .expression argumentsResult
              have held := ih _ result
              exact ⟨held.1.trans frame.1, held.2.trans frame.2⟩
        · split at result
          · cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject failure rejected => simp [dotResult] at result
            | ok dot afterDot =>
                simp only [dotResult] at result
                have dotShape := (symbol_ok_tokenAt .dot .expression dotResult).2
                subst afterDot
                cases nameResult : identifier .expression { input with cursor := input.cursor + 1 } with
                | invariant error => simp [nameResult] at result
                | reject failure rejected => simp [nameResult] at result
                | ok name next =>
                    simp only [nameResult] at result
                    have frame := identifier_success_context_eq .expression nameResult
                    have held := ih _ result
                    exact ⟨held.1.trans frame.1, held.2.trans frame.2⟩
          · cases result; exact ⟨rfl, rfl⟩

variable {β : Type} {view : TokenWindow → β}

private theorem callTail_reject_frame (success : ParserSuccessContext nested)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window) (opening : Token) :
    ∀ fuel values input failure rejected,
      afterDelimitedElement nested .rightParen false .expression .expression opening fuel values input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window := by
  intro fuel
  induction fuel with
  | zero => intro values input failure rejected result; simp [afterDelimitedElement] at result
  | succ fuel ih =>
      intro values input failure rejected result
      unfold afterDelimitedElement at result
      split at result
      · rename_i commaPresent
        rcases symbol_eq_ok_of_isSymbol_eq_true .comma .expression commaPresent with ⟨comma, commaResult⟩
        simp only [commaResult, Bool.false_and, Bool.false_eq_true, if_false] at result
        cases childResult : nested { input with cursor := input.cursor + 1 } with
        | invariant error => simp [childResult] at result
        | reject actual next =>
            simp only [childResult] at result; cases result
            exact reject (input := { input with cursor := input.cursor + 1 }) childResult
        | ok value next =>
            simp only [childResult] at result
            split at result
            · have frame := success childResult
              have held := ih (value :: values) next failure rejected result
              exact ⟨held.1.trans frame.1, held.2.trans (congrArg view frame.2)⟩
            · contradiction
      · split at result
        · rename_i closingPresent
          rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .expression closingPresent with ⟨closing, closingResult⟩
          simp [closeDelimited, closingResult] at result
        · unfold rejectAt at result; cases result; exact ⟨rfl, rfl⟩

private theorem call_reject_frame (success : ParserSuccessContext nested)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure}
    (result : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject actual next =>
      simp only [openingResult] at result; cases result
      rw [symbol_reject_state_eq .leftParen .expression openingResult]; exact ⟨rfl, rfl⟩
  | ok opening afterOpening =>
      have openingShape := (symbol_ok_tokenAt .leftParen .expression openingResult).2
      subst afterOpening
      simp only [openingResult, Bool.true_and] at result
      split at result
      · rename_i closingPresent
        rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .expression closingPresent with ⟨closing, closingResult⟩
        simp [closeDelimited, closingResult] at result
      · cases childResult : nested { input with cursor := input.cursor + 1 } with
        | invariant error => simp [childResult] at result
        | reject actual next =>
            simp only [childResult] at result; cases result
            exact reject (input := { input with cursor := input.cursor + 1 }) childResult
        | ok value next =>
            simp only [childResult] at result
            split at result
            · have frame := success childResult
              have held := callTail_reject_frame success reject opening _ [value] next failure rejected result
              exact ⟨held.1.trans frame.1, held.2.trans (congrArg view frame.2)⟩
            · contradiction

theorem postfixTail_reject_context_of_windowProjection (success : ParserSuccessContext nested)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    (block : Parser Block) : ∀ fuel base {input rejected : State} {failure : Failure},
      postfixTail nested block fuel base input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window := by
  intro fuel
  induction fuel with
  | zero => intro base input rejected failure result; simp [postfixTail] at result
  | succ fuel ih =>
      intro base input rejected failure result
      unfold postfixTail at result
      split at result
      · cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject actual next =>
            simp only [openingResult] at result; cases result
            rw [symbol_reject_state_eq .leftBracket .expression openingResult]; exact ⟨rfl, rfl⟩
        | ok opening afterOpening =>
            simp only [openingResult] at result
            have openingShape := (symbol_ok_tokenAt .leftBracket .expression openingResult).2
            subst afterOpening
            cases childResult : nested { input with cursor := input.cursor + 1 } with
            | invariant error => simp [childResult] at result
            | reject actual next =>
                simp only [childResult] at result; cases result
                exact reject (input := { input with cursor := input.cursor + 1 }) childResult
            | ok index next =>
                simp only [childResult] at result
                have frame := success childResult
                cases closingResult : symbol .rightBracket .expression next with
                | invariant error => simp [closingResult] at result
                | reject actual afterClosing =>
                    simp only [closingResult] at result; cases result
                    rw [symbol_reject_state_eq .rightBracket .expression closingResult]
                    exact ⟨frame.1, congrArg view frame.2⟩
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    have held := ih _ result
                    rw [(symbol_ok_tokenAt .rightBracket .expression closingResult).2] at held
                    exact ⟨held.1.trans frame.1, held.2.trans (congrArg view frame.2)⟩
      · split at result
        · cases argumentsResult : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject actual next => simp only [argumentsResult] at result; cases result; exact call_reject_frame success reject argumentsResult
          | ok arguments next =>
              simp only [argumentsResult] at result
              have frame := delimitedNoTrailing_success_context success .leftParen .rightParen true .expression .expression argumentsResult
              have held := ih _ result
              exact ⟨held.1.trans frame.1, held.2.trans (congrArg view frame.2)⟩
        · split at result
          · cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject actual next =>
                simp only [dotResult] at result; cases result
                rw [symbol_reject_state_eq .dot .expression dotResult]; exact ⟨rfl, rfl⟩
            | ok dot afterDot =>
                simp only [dotResult] at result
                have dotShape := (symbol_ok_tokenAt .dot .expression dotResult).2
                subst afterDot
                cases nameResult : identifier .expression { input with cursor := input.cursor + 1 } with
                | invariant error => simp [nameResult] at result
                | reject actual next =>
                    simp only [nameResult] at result; cases result
                    rw [identifier_reject_state_eq .expression nameResult]; exact ⟨rfl, rfl⟩
                | ok name next =>
                    simp only [nameResult] at result
                    have frame := identifier_success_context_eq .expression nameResult
                    have held := ih _ result
                    exact ⟨held.1.trans frame.1, held.2.trans (congrArg view frame.2)⟩
          · contradiction

theorem postfixTail_reject_context (success : ParserSuccessContext nested)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    (block : Parser Block) (fuel : Nat) (base : Expr) {input rejected : State} {failure : Failure}
    (result : postfixTail nested block fuel base input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window :=
  postfixTail_reject_context_of_windowProjection (view := id) success reject block fuel base result

theorem postfixTail_reject_source_endByte (success : ParserSuccessContext nested)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (block : Parser Block) (fuel : Nat) (base : Expr) {input rejected : State} {failure : Failure}
    (result : postfixTail nested block fuel base input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte :=
  postfixTail_reject_context_of_windowProjection (view := TokenWindow.endByte) success reject block fuel base result

end Solcore.Syntax.Parser.ExpressionAtomInternals
