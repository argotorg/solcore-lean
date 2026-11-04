import Solcore.Syntax.Parser.Internal.DelimitedTrace
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.ExpressionAtomProofs
import Solcore.Syntax.Parser.Internal.BlockTrace
import Solcore.Syntax.Internal.DotConstructorTrace
import Solcore.Syntax.Parser.Internal.TypeTrace
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.Internal.OperatorSoundness
import Solcore.Syntax.Parser.Internal.ExpressionTotality
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.ExpressionTrace
import Solcore.Syntax.Parser.Internal.DelimitedTotality

/-!
Parser side of the traces of postfix tails and operators: the parsers produce exactly the
events of the trace grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.PostfixTailUnrestrictedFuelTotalityProperties
/-! Bounded postfix-tail execution on arbitrary States. Real suffix markers
pay loop fuel before nested work. Successful children need only endIndex
preservation and strict progress; rejected carriers and all source, span,
diagnostic, and token-storage validity properties remain unconstrained. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem postfixTail_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel) :
    ∀ loopFuel base input,
      input.remainingCount < loopFuel → input.remainingCount < nestedFuel + 1 →
      (∃ value next, postfixTail nested block loopFuel base input = .ok value next) ∨
      (∃ failure next, postfixTail nested block loopFuel base input = .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero => intro base input loopAdequate nestedAdequate; omega
  | succ loopFuel ih =>
      intro base input loopAdequate nestedAdequate
      unfold postfixTail
      by_cases indexed : isSymbol input .leftBracket = true
      · simp only [indexed, if_true]
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => exact False.elim (symbol_ne_invariant .leftBracket .expression input error openingResult)
        | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
        | ok opening afterOpening =>
            have openingLoop := symbol_remainingCount_lt_of_success .leftBracket .expression openingResult loopAdequate
            have openingNested := symbol_remainingCount_lt_of_success .leftBracket .expression openingResult nestedAdequate
            simp only
            cases indexResult : nested afterOpening with
            | invariant error => exact False.elim (contract.ne_invariant afterOpening openingNested error indexResult)
            | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
            | ok index afterIndex =>
                have indexLoop := contract.remainingCount_lt_of_success indexResult openingLoop
                have indexNested := contract.remainingCount_lt_of_success indexResult openingNested
                simp only
                cases closingResult : symbol .rightBracket .expression afterIndex with
                | invariant error => exact False.elim (symbol_ne_invariant .rightBracket .expression afterIndex error closingResult)
                | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
                | ok closing afterClosing =>
                    have closingLoop : afterClosing.remainingCount < loopFuel :=
                      symbol_remainingCount_lt_of_success .rightBracket .expression closingResult (by omega)
                    have closingNested : afterClosing.remainingCount < nestedFuel + 1 :=
                      symbol_remainingCount_lt_of_success .rightBracket .expression closingResult (by omega)
                    exact ih {
                      span := SourceSpan.cover base.span closing.span
                      value := .index base (SourceSpan.cover opening.span closing.span) index
                    } afterClosing closingLoop closingNested
      · have indexedFalse := Bool.eq_false_iff.mpr indexed
        simp only [indexedFalse, Bool.false_eq_true, if_false]
        by_cases called : isSymbol input .leftParen = true
        · simp only [called, if_true]
          rcases delimitedWithPolicy_ordinary_of_unrestrictedElementFuel .leftParen .rightParen true false
              nested .expression .expression nestedFuel contract input nestedAdequate with
            ⟨arguments, next, argumentsResult⟩ | ⟨failure, rejected, argumentsResult⟩
          · have endIndexEq := delimitedWithPolicy_endIndex_onSuccess contract.endIndexOnSuccess
              .leftParen .rightParen true false .expression .expression argumentsResult
            have progress := delimitedWithPolicy_cursor_lt_onSuccess .leftParen .rightParen true false
              nested .expression .expression argumentsResult
            rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression called with ⟨opening, openingResult⟩
            have beforeEnd := State.cursor_lt_endIndex_of_peek?_eq_some
              (symbol_ok_state_shape .leftParen .expression openingResult).1
            have nextLoop : next.remainingCount < loopFuel := by
              simp only [State.remainingCount, endIndexEq] at loopAdequate ⊢
              omega
            have nextNested := remainingCount_lt_of_endIndex_eq endIndexEq (Nat.le_of_lt progress) nestedAdequate
            rcases ih {
                span := SourceSpan.cover base.span arguments.span, value := .call base arguments
              } next nextLoop nextNested with ⟨value, final, result⟩ | ⟨failure, final, result⟩
            · exact .inl ⟨value, final, by simp only [delimitedNoTrailing, argumentsResult, result]⟩
            · exact .inr ⟨failure, final, by simp only [delimitedNoTrailing, argumentsResult, result]⟩
          · exact .inr ⟨failure, rejected, by simp only [delimitedNoTrailing, argumentsResult]⟩
        · have calledFalse := Bool.eq_false_iff.mpr called
          simp only [calledFalse, Bool.false_eq_true, if_false]
          by_cases field : isSymbol input .dot = true
          · simp only [field, if_true]
            cases dotResult : symbol .dot .expression input with
            | invariant error => exact False.elim (symbol_ne_invariant .dot .expression input error dotResult)
            | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
            | ok dot afterDot =>
                have dotLoop := symbol_remainingCount_lt_of_success .dot .expression dotResult loopAdequate
                have dotNested := symbol_remainingCount_lt_of_success .dot .expression dotResult nestedAdequate
                simp only
                cases nameResult : identifier .expression afterDot with
                | invariant error => exact False.elim (identifier_ne_invariant .expression afterDot error nameResult)
                | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
                | ok name next =>
                    have window := identifier_preservesTokenWindow .expression afterDot
                    rw [nameResult] at window
                    have progress := identifier_cursorMonotoneOnSuccess .expression afterDot name next nameResult
                    have nextLoop := remainingCount_lt_of_endIndex_eq
                      (congrArg TokenWindow.endIndex window.2) progress dotLoop
                    have nextNested := remainingCount_lt_of_endIndex_eq
                      (congrArg TokenWindow.endIndex window.2) progress dotNested
                    exact ih {
                      span := SourceSpan.cover base.span name.span, value := .field base dot.span name
                    } next nextLoop (by omega)
          · have fieldFalse := Bool.eq_false_iff.mpr field
            exact .inl ⟨base, input, by simp only [fieldFalse, Bool.false_eq_true, if_false]⟩

theorem postfixTail_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel loopFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (base : Expr) (input : State) (loopAdequate : input.remainingCount < loopFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    postfixTail nested block loopFuel base input ≠ .invariant error := by
  intro failed
  rcases postfixTail_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract loopFuel
      base input loopAdequate nestedAdequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

theorem postfixTail_production_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (base : Expr) (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, postfixTail nested block (input.remainingCount + 1) base input = .ok value next) ∨
    (∃ failure next, postfixTail nested block (input.remainingCount + 1) base input = .reject failure next) :=
  postfixTail_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract
    (input.remainingCount + 1) base input (Nat.lt_succ_self _) adequate

theorem postfixTail_production_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (base : Expr) (input : State) (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    postfixTail nested block (input.remainingCount + 1) base input ≠ .invariant error :=
  postfixTail_ne_invariant_of_unrestrictedElementFuel nested block nestedFuel
    (input.remainingCount + 1) contract base input (Nat.lt_succ_self _) adequate error

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionPostfixUnrestrictedFuelTotalityProperties
/-! Bounded ordinary execution for the actual atom-plus-postfix composition.
The pointwise form only constrains successful atom remaining counts; a stronger
corollary consumes a separately supplied atom contract. This file does not
construct that contract or establish recursive expression/block totality. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open ExpressionAtomInternals

/-- No atom source, token, diagnostic, or rejected-state frame is needed.
Only its ordinary outcome here and the bound at each successful endpoint matter. -/
theorem expressionPostfix_ordinary_of_atomOutcome_bound
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel) (input : State)
    (atomOrdinary :
      (∃ base next, expressionAtom nested block input = .ok base next) ∨
      (∃ failure rejected, expressionAtom nested block input = .reject failure rejected))
    (afterAtomBound : ∀ {base next}, expressionAtom nested block input = .ok base next →
      next.remainingCount < nestedFuel + 1) :
    (∃ value output, expressionPostfix nested block input = .ok value output) ∨
    (∃ failure rejected, expressionPostfix nested block input = .reject failure rejected) := by
  rcases atomOrdinary with ⟨base, next, atomResult⟩ | ⟨failure, rejected, atomResult⟩
  · rcases postfixTail_production_ordinary_of_unrestrictedElementFuel nested block nestedFuel
        nestedContract base next (afterAtomBound atomResult) with
      ⟨value, output, tailResult⟩ | ⟨failure, rejected, tailResult⟩
    · exact .inl ⟨value, output, by simp only [expressionPostfix, atomResult, tailResult]⟩
    · exact .inr ⟨failure, rejected, by simp only [expressionPostfix, atomResult, tailResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [expressionPostfix, atomResult]⟩

theorem expressionPostfix_ne_invariant_of_atomOutcome_bound
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel) (input : State)
    (atomOrdinary :
      (∃ base next, expressionAtom nested block input = .ok base next) ∨
      (∃ failure rejected, expressionAtom nested block input = .reject failure rejected))
    (afterAtomBound : ∀ {base next}, expressionAtom nested block input = .ok base next →
      next.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    expressionPostfix nested block input ≠ .invariant error := by
  intro failed
  rcases expressionPostfix_ordinary_of_atomOutcome_bound nested block nestedFuel nestedContract
      input atomOrdinary afterAtomBound with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- The actual atom contract is an explicit premise, not a consequence of the
nested contract. Its strict progress and unchanged endIndex transfer the second
input bound to the atom's successful endpoint on arbitrary numerical States. -/
theorem expressionPostfix_ordinary_of_unrestrictedElementFuels
    (nested : Parser Expr) (block : Parser Block) (atomFuel nestedFuel : Nat)
    (atomContract : UnrestrictedFuelElementContract (expressionAtom nested block) atomFuel)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel) (input : State)
    (atomAdequate : input.remainingCount < atomFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) :
    (∃ value output, expressionPostfix nested block input = .ok value output) ∨
    (∃ failure rejected, expressionPostfix nested block input = .reject failure rejected) :=
  expressionPostfix_ordinary_of_atomOutcome_bound nested block nestedFuel nestedContract input
    (atomContract.ordinary input atomAdequate)
    (fun result => atomContract.remainingCount_lt_of_success result nestedAdequate)

theorem expressionPostfix_ne_invariant_of_unrestrictedElementFuels
    (nested : Parser Expr) (block : Parser Block) (atomFuel nestedFuel : Nat)
    (atomContract : UnrestrictedFuelElementContract (expressionAtom nested block) atomFuel)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel) (input : State)
    (atomAdequate : input.remainingCount < atomFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    expressionPostfix nested block input ≠ .invariant error :=
  expressionPostfix_ne_invariant_of_atomOutcome_bound nested block nestedFuel nestedContract input
    (atomContract.ordinary input atomAdequate)
    (fun result => atomContract.remainingCount_lt_of_success result nestedAdequate) error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PostfixTailTraceContextProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionPostfixTraceContextProperties
/-! Separate source/window frames for atom-plus-postfix composition. Rejected
token carriers need not be preserved; a caller chooses the window observation.
No trace, progress, validity, or ordinary-execution premise is introduced. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}

theorem expressionPostfix_trace_success_context
    (atomContext : ParserSuccessContext (expressionAtom nested block))
    (nestedContext : ParserSuccessContext nested) :
    ParserSuccessContext (expressionPostfix nested block) := by
  intro input output value result
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject failure rejected => simp [atomResult] at result
  | ok base next =>
      simp only [atomResult] at result
      have atomFrame := atomContext atomResult
      have tailFrame := postfixTail_success_context nestedContext block _ base result
      exact ⟨tailFrame.1.trans atomFrame.1, tailFrame.2.trans atomFrame.2⟩

theorem expressionPostfix_reject_context_of_windowProjection {β : Type} {view : TokenWindow → β}
    (atomContext : ParserSuccessContext (expressionAtom nested block))
    (nestedContext : ParserSuccessContext nested)
    (atomReject : ∀ {input rejected failure}, expressionAtom nested block input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure}
    (result : expressionPostfix nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject actual next => simp only [atomResult] at result; cases result; exact atomReject atomResult
  | ok base next =>
      simp only [atomResult] at result
      have atomFrame := atomContext atomResult
      have tailFrame := postfixTail_reject_context_of_windowProjection nestedContext nestedReject block _ base result
      exact ⟨tailFrame.1.trans atomFrame.1, tailFrame.2.trans (congrArg view atomFrame.2)⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PostfixTailSuccessTraceSoundnessProperties
/-! Every successful actual postfix tail retains the exact maximal suffix AST
and ordered nested/name events. Soundness holds for every fuel without a child
progress or ordinary contract; only successful source/full-window context is used. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}

theorem postfixTail_trace_success_sound
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (contextFrame : ParserSuccessContext nested) (block : Parser Block) :
    ∀ fuel base input value output,
      postfixTail nested block fuel base input = .ok value output →
      ∃ trace, PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
        input.declarativeRemainder base value output.declarativeRemainder trace ∧
        output.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro base input value output result; simp [postfixTail] at result
  | succ fuel ih =>
      intro base input value output result
      unfold postfixTail at result
      split at result
      · cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject failure rejected => simp [openingResult] at result
        | ok opening afterOpening =>
            simp only [openingResult] at result
            have openingParsed := symbol_success_exactTokenParses .leftBracket .expression openingResult
            have openingShape := (symbol_ok_tokenAt .leftBracket .expression openingResult).2
            subst afterOpening
            cases indexResult : nested { input with cursor := input.cursor + 1 } with
            | invariant error => simp [indexResult] at result
            | reject failure rejected => simp [indexResult] at result
            | ok index afterIndex =>
                simp only [indexResult] at result
                rcases successSound indexResult with ⟨indexTrace, indexParsed, indexEvents⟩
                have frame := contextFrame indexResult
                cases closingResult : symbol .rightBracket .expression afterIndex with
                | invariant error => simp [closingResult] at result
                | reject failure rejected => simp [closingResult] at result
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    have closingParsed := symbol_success_exactTokenParses .rightBracket .expression closingResult
                    have closingShape := (symbol_ok_tokenAt .rightBracket .expression closingResult).2
                    rcases ih (postfixIndexTraceValue base index opening.span closing.span) afterClosing value output result with
                      ⟨tailTrace, tailParsed, tailEvents⟩
                    refine ⟨indexTrace ++ tailTrace, .index opening.span closing.span openingParsed indexParsed closingParsed ?_, ?_⟩
                    · simpa only [closingShape, frame.1, frame.2] using tailParsed
                    · rw [tailEvents, closingShape]
                      change afterIndex.diagnostics ++ tailTrace = _
                      rw [indexEvents]
                      exact List.append_assoc _ _ _
      · rename_i indexFalse
        have indexAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftBracket (Bool.eq_false_iff.mpr indexFalse)
        split at result
        · cases argumentsResult : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              rcases delimitedNoTrailing_success_trace_sound successSound contextFrame
                  .leftParen .rightParen true .expression .expression argumentsResult with
                ⟨argumentTrace, argumentsParsed, argumentEvents⟩
              have frame := delimitedNoTrailing_success_context contextFrame
                .leftParen .rightParen true .expression .expression argumentsResult
              rcases ih (postfixCallTraceValue base arguments) afterArguments value output result with
                ⟨tailTrace, tailParsed, tailEvents⟩
              refine ⟨argumentTrace ++ tailTrace, .call indexAbsent argumentsParsed ?_, ?_⟩
              · simpa only [frame.1, frame.2] using tailParsed
              · rw [tailEvents, argumentEvents]; exact List.append_assoc _ _ _
        · rename_i callFalse
          have callAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftParen (Bool.eq_false_iff.mpr callFalse)
          split at result
          · cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject failure rejected => simp [dotResult] at result
            | ok dot afterDot =>
                simp only [dotResult] at result
                have dotParsed := symbol_success_exactTokenParses .dot .expression dotResult
                have dotShape := (symbol_ok_tokenAt .dot .expression dotResult).2
                subst afterDot
                cases nameResult : identifier .expression { input with cursor := input.cursor + 1 } with
                | invariant error => simp [nameResult] at result
                | reject failure rejected => simp [nameResult] at result
                | ok name afterName =>
                    simp only [nameResult] at result
                    rcases identifier_success_trace_sound .expression nameResult with ⟨nameTrace, nameParsed, nameEvents⟩
                    have frame := identifier_success_context_eq .expression nameResult
                    rcases ih (postfixFieldTraceValue base dot.span name) afterName value output result with
                      ⟨tailTrace, tailParsed, tailEvents⟩
                    refine ⟨nameTrace ++ tailTrace, .field dot.span indexAbsent callAbsent dotParsed nameParsed ?_, ?_⟩
                    · simpa only [frame.1, frame.2] using tailParsed
                    · rw [tailEvents, nameEvents]; exact List.append_assoc _ _ _
          · rename_i fieldFalse
            cases result
            exact ⟨[], .done ⟨indexAbsent, callAbsent,
              symbolAbsentAt_of_isSymbol_eq_false .dot (Bool.eq_false_iff.mpr fieldFalse)⟩, (List.append_nil _).symm⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PostfixTailTraceCompletenessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.PostfixTailRejectionTraceSoundnessProperties
/-! Every ordinary postfix-tail rejection retains the exact first report and
ordered child/name events. The selected opening symbols are silent and cannot
reject. Successful child context is explicit; no child rejection frame,
progress, totality, validity, or fuel-adequacy premise is required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem postfixTail_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested) (block : Parser Block) :
    ∀ fuel base input failure rejected,
      postfixTail nested block fuel base input = .reject failure rejected →
      ∃ trace, PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
        input.declarativeRemainder base rejected.declarativeRemainder failure.toDiagnostic trace ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro base input failure rejected result; simp [postfixTail] at result
  | succ fuel ih =>
      intro base input failure rejected result
      unfold postfixTail at result
      by_cases indexed : isSymbol input .leftBracket = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .leftBracket .expression indexed with
          ⟨opening, openingResult⟩
        have openingParsed := symbol_success_exactTokenParses .leftBracket .expression openingResult
        simp only [indexed, if_true, openingResult] at result
        cases indexResult : nested { input with cursor := input.cursor + 1 } with
        | invariant error => simp [indexResult] at result
        | reject actual next =>
            simp only [indexResult] at result
            cases result
            rcases rejectSound indexResult with ⟨trace, rejection, events⟩
            exact ⟨trace, .indexNestedRejected opening.span openingParsed rejection, events⟩
        | ok index next =>
            simp only [indexResult] at result
            rcases successSound indexResult with ⟨indexEvents, indexParsed, indexEq⟩
            have frame := contextFrame indexResult
            cases closingResult : symbol .rightBracket .expression next with
            | invariant error => simp [closingResult] at result
            | reject actual afterClosing =>
                simp only [closingResult] at result
                cases result
                have same := symbol_reject_state_eq .rightBracket .expression closingResult
                subst rejected
                have reported := (symbol_reject_reports_iff .rightBracket .expression).mpr
                  ⟨failure, closingResult, rfl⟩
                refine ⟨indexEvents, .indexClosingMissing opening.span openingParsed indexParsed reported.1 ?_, indexEq⟩
                simpa only [frame.1, frame.2] using reported.2
            | ok closing afterClosing =>
                simp only [closingResult] at result
                have closingParsed := symbol_success_exactTokenParses .rightBracket .expression closingResult
                have closingShape := (symbol_ok_tokenAt .rightBracket .expression closingResult).2
                rcases ih (postfixIndexTraceValue base index opening.span closing.span)
                    afterClosing failure rejected result with ⟨tailEvents, tail, tailEq⟩
                refine ⟨indexEvents ++ tailEvents,
                  .indexLaterRejected opening.span closing.span openingParsed indexParsed closingParsed ?_, ?_⟩
                · simpa only [closingShape, frame.1, frame.2] using tail
                · have closingEvents : afterClosing.diagnostics = next.diagnostics := by rw [closingShape]; rfl
                  rw [tailEq, closingEvents, indexEq]
                  exact List.append_assoc _ _ _
      · have indexedFalse := Bool.eq_false_iff.mpr indexed
        simp only [indexedFalse, Bool.false_eq_true, if_false] at result
        have indexAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftBracket indexedFalse
        by_cases called : isSymbol input .leftParen = true
        · simp only [called, if_true] at result
          cases argumentsResult : delimitedNoTrailing .leftParen .rightParen true nested
              .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject actual next =>
              simp only [argumentsResult] at result
              cases result
              rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression called with
                ⟨opening, openingResult⟩
              rcases delimitedNoTrailing_reject_trace_sound successSound rejectSound contextFrame
                  .leftParen .rightParen true .expression .expression argumentsResult with
                ⟨trace, rejection, events⟩
              exact ⟨trace, .callArgumentsRejected opening.span indexAbsent
                (symbol_success_exactTokenParses .leftParen .expression openingResult).1 rejection, events⟩
          | ok arguments next =>
              simp only [argumentsResult] at result
              rcases delimitedNoTrailing_success_trace_sound successSound contextFrame
                  .leftParen .rightParen true .expression .expression argumentsResult with
                ⟨argumentEvents, argumentsParsed, argumentsEq⟩
              have frame := delimitedNoTrailing_success_context contextFrame
                .leftParen .rightParen true .expression .expression argumentsResult
              rcases ih (postfixCallTraceValue base arguments) next failure rejected result with
                ⟨tailEvents, tail, tailEq⟩
              refine ⟨argumentEvents ++ tailEvents, .callLaterRejected indexAbsent argumentsParsed ?_, ?_⟩
              · simpa only [frame.1, frame.2] using tail
              · rw [tailEq, argumentsEq]; exact List.append_assoc _ _ _
        · have calledFalse := Bool.eq_false_iff.mpr called
          simp only [calledFalse, Bool.false_eq_true, if_false] at result
          have callAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftParen calledFalse
          by_cases field : isSymbol input .dot = true
          · rcases symbol_eq_ok_of_isSymbol_eq_true .dot .expression field with ⟨dot, dotResult⟩
            have dotParsed := symbol_success_exactTokenParses .dot .expression dotResult
            simp only [field, if_true, dotResult] at result
            cases nameResult : identifier .expression { input with cursor := input.cursor + 1 } with
            | invariant error => simp [nameResult] at result
            | reject actual next =>
                simp only [nameResult] at result
                cases result
                have same := identifier_reject_state_eq .expression nameResult
                subst rejected
                have reported := (identifier_reject_reports_iff .expression).mpr ⟨failure, nameResult, rfl⟩
                exact ⟨[], .fieldNameRejected dot.span indexAbsent callAbsent dotParsed reported.1 reported.2,
                  by simp only [List.append_nil]; rfl⟩
            | ok name next =>
                simp only [nameResult] at result
                rcases identifier_success_trace_sound .expression nameResult with ⟨nameEvents, nameParsed, nameEq⟩
                have frame := identifier_success_context_eq .expression nameResult
                rcases ih (postfixFieldTraceValue base dot.span name) next failure rejected result with
                  ⟨tailEvents, tail, tailEq⟩
                refine ⟨nameEvents ++ tailEvents,
                  .fieldLaterRejected dot.span indexAbsent callAbsent dotParsed nameParsed ?_, ?_⟩
                · simpa only [frame.1, frame.2] using tail
                · rw [tailEq, nameEq]; exact List.append_assoc _ _ _
          · have fieldFalse := Bool.eq_false_iff.mpr field
            simp [fieldFalse] at result

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionPostfixTraceSoundnessProperties
/-! The actual atom-plus-postfix parser retains atom events before every
maximal suffix event. Its production tail budget does not need adequacy for
soundness of observed ordinary replies. Atom and nested contracts stay explicit. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {atomTrace nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {atomRejects nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionPostfix_trace_success_sound
    (atomSound : ParserTraceSuccessSound (expressionAtom nested block) atomTrace)
    (atomContext : ParserSuccessContext (expressionAtom nested block))
    (nestedSound : ParserTraceSuccessSound nested nestedTrace)
    (nestedContext : ParserSuccessContext nested) :
    ParserTraceSuccessSound (expressionPostfix nested block)
      (ExpressionPostfixTraceParses atomTrace nestedTrace) := by
  intro input output value result
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject failure rejected => simp [atomResult] at result
  | ok base next =>
      simp only [atomResult] at result
      rcases atomSound atomResult with ⟨atomEvents, atomParsed, atomEq⟩
      have frame := atomContext atomResult
      rcases postfixTail_trace_success_sound nestedSound nestedContext block
          (next.remainingCount + 1) base next value output result with
        ⟨tailEvents, tailParsed, tailEq⟩
      refine ⟨atomEvents ++ tailEvents, .parsed atomParsed ?_, ?_⟩
      · simpa only [frame.1, frame.2] using tailParsed
      · rw [tailEq, atomEq]; exact List.append_assoc _ _ _

theorem expressionPostfix_reject_trace_sound
    (atomSound : ParserTraceSuccessSound (expressionAtom nested block) atomTrace)
    (atomRejectSound : ParserTraceRejectSound (expressionAtom nested block) atomRejects)
    (atomContext : ParserSuccessContext (expressionAtom nested block))
    (nestedSound : ParserTraceSuccessSound nested nestedTrace)
    (nestedRejectSound : ParserTraceRejectSound nested nestedRejects)
    (nestedContext : ParserSuccessContext nested) :
    ParserTraceRejectSound (expressionPostfix nested block)
      (ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects) := by
  intro input rejected failure result
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject actual next =>
      simp only [atomResult] at result; cases result
      rcases atomRejectSound atomResult with ⟨trace, rejection, events⟩
      exact ⟨trace, .atomRejected rejection, events⟩
  | ok base next =>
      simp only [atomResult] at result
      rcases atomSound atomResult with ⟨atomEvents, atomParsed, atomEq⟩
      have frame := atomContext atomResult
      rcases postfixTail_reject_trace_sound nestedSound nestedRejectSound nestedContext block
          (next.remainingCount + 1) base next failure rejected result with
        ⟨tailEvents, tailRejected, tailEq⟩
      refine ⟨atomEvents ++ tailEvents, .tailRejected atomParsed ?_, ?_⟩
      · simpa only [frame.1, frame.2] using tailRejected
      · rw [tailEq, atomEq]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionPostfixTraceExistenceProperties
/-! Separate non-vacuous postfix outcomes follow bounded ordinary execution
and soundness. The atom contract remains explicit; joint exactness and child
completeness are neither assumed nor substituted for runtime totality. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {atomTrace nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {atomRejects nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (atomSound : ParserTraceSuccessSound (expressionAtom nested block) atomTrace)
  (atomRejectSound : ParserTraceRejectSound (expressionAtom nested block) atomRejects)
  (atomContext : ParserSuccessContext (expressionAtom nested block))
  (nestedSound : ParserTraceSuccessSound nested nestedTrace)
  (nestedRejectSound : ParserTraceRejectSound nested nestedRejects)
  (nestedContext : ParserSuccessContext nested)
  (atomFuel nestedFuel : Nat)
  (atomContract : UnrestrictedFuelElementContract (expressionAtom nested block) atomFuel)
  (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)

include atomSound atomRejectSound atomContext nestedSound nestedRejectSound nestedContext
  atomContract nestedContract

theorem expressionPostfix_exists_trace_outcome_of_unrestrictedElementFuels
    (input : State) (atomAdequate : input.remainingCount < atomFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) :
    (∃ value output trace,
      expressionPostfix nested block input = .ok value output ∧
      ExpressionPostfixTraceParses atomTrace nestedTrace input.file.id input.window.endByte
        input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionPostfix nested block input = .reject failure rejected ∧
      ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
        input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionPostfix_ordinary_of_unrestrictedElementFuels nested block atomFuel nestedFuel
      atomContract nestedContract input atomAdequate nestedAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionPostfix_trace_success_sound atomSound atomContext nestedSound nestedContext result with
      ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionPostfix_reject_trace_sound atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionPostfixTrace_outcome_exists_of_unrestrictedElementFuels
    (source : SourceId) (endByte : Nat) (input : Remainder)
    (atomAdequate : input.endIndex - input.cursor < atomFuel)
    (nestedAdequate : input.endIndex - input.cursor < nestedFuel + 1) :
    (∃ value after trace, ExpressionPostfixTraceParses atomTrace nestedTrace source endByte input value after trace) ∨
    (∃ rejected report trace, ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  rcases expressionPostfix_exists_trace_outcome_of_unrestrictedElementFuels atomSound atomRejectSound
      atomContext nestedSound nestedRejectSound nestedContext atomFuel nestedFuel atomContract nestedContract
      state atomAdequate nestedAdequate with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, rejection⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionPostfixTraceCorrespondenceProperties
/-! Pointwise correspondence for the actual production-fuel postfix parser.
Independent atom/nested exactness and observed soundness require a separate
actual no-invariant premise for completeness. Child completeness or context
alone cannot supply the production tail's remaining-count fuel adequacy. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {atomTrace nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {atomRejects nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (atomSound : ParserTraceSuccessSound (expressionAtom nested block) atomTrace)
  (atomRejectSound : ParserTraceRejectSound (expressionAtom nested block) atomRejects)
  (atomContext : ParserSuccessContext (expressionAtom nested block))
  (nestedSound : ParserTraceSuccessSound nested nestedTrace)
  (nestedRejectSound : ParserTraceRejectSound nested nestedRejects)
  (nestedContext : ParserSuccessContext nested) {input : State}
  (atoms : TraceExactOutcomeSpec atomTrace atomRejects input.file.id input.window.endByte)
  (nestedOutcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
  (invariantFree : ∀ error, expressionPostfix nested block input ≠ .invariant error)
  {value : Expr} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}

include atomSound atomRejectSound atomContext nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree

theorem expressionPostfix_trace_success_complete_of_ne_invariant
    (parsed : ExpressionPostfixTraceParses atomTrace nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    ∃ output, expressionPostfix nested block input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  trace_success_exists_ok_of_sound
    (expressionPostfix_trace_success_sound atomSound atomContext nestedSound nestedContext)
    (expressionPostfix_reject_trace_sound atomSound atomRejectSound atomContext nestedSound nestedRejectSound nestedContext)
    (expressionPostfixTraceExactOutcomeSpec atoms nestedOutcomes) invariantFree parsed

theorem expressionPostfix_trace_reject_complete_of_ne_invariant
    (rejection : ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace) :
    ∃ failure rejected, expressionPostfix nested block input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  trace_reject_exists_reject_of_sound
    (expressionPostfix_trace_success_sound atomSound atomContext nestedSound nestedContext)
    (expressionPostfix_reject_trace_sound atomSound atomRejectSound atomContext nestedSound nestedRejectSound nestedContext)
    (expressionPostfixTraceExactOutcomeSpec atoms nestedOutcomes) invariantFree rejection

theorem expressionPostfix_trace_success_iff_of_ne_invariant :
    ExpressionPostfixTraceParses atomTrace nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, expressionPostfix nested block input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionPostfix_trace_success_complete_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree
  · rintro ⟨output, result, afterEq, events⟩
    rcases expressionPostfix_trace_success_sound atomSound atomContext nestedSound nestedContext result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem expressionPostfix_trace_reject_iff_of_ne_invariant :
    ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
    ∃ failure rejected, expressionPostfix nested block input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionPostfix_trace_reject_complete_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases expressionPostfix_reject_trace_sound atomSound atomRejectSound atomContext nestedSound
        nestedRejectSound nestedContext result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem expressionPostfix_trace_reject_failure_iff_of_ne_invariant {failure : Failure} :
    ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, expressionPostfix nested block input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [expressionPostfix_trace_reject_iff_of_ne_invariant atomSound atomRejectSound atomContext
    nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionPostfixTraceStateProperties
/-! Whole-State correspondence for actual atom-plus-postfix execution at an
explicit invariant-free input. Rejected child frames preserve only file and
endByte; the exact remainder retains replacement tokens and numeric endIndex.
No child progress, validity, or hidden production-fuel completeness is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {atomTrace nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {atomRejects nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (atomSound : ParserTraceSuccessSound (expressionAtom nested block) atomTrace)
  (atomRejectSound : ParserTraceRejectSound (expressionAtom nested block) atomRejects)
  (atomContext : ParserSuccessContext (expressionAtom nested block))
  (nestedSound : ParserTraceSuccessSound nested nestedTrace)
  (nestedRejectSound : ParserTraceRejectSound nested nestedRejects)
  (nestedContext : ParserSuccessContext nested) {input : State}
  (atoms : TraceExactOutcomeSpec atomTrace atomRejects input.file.id input.window.endByte)
  (nestedOutcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
  (invariantFree : ∀ error, expressionPostfix nested block input ≠ .invariant error)

include atomSound atomRejectSound atomContext nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree

theorem expressionPostfix_trace_success_state_iff_of_ne_invariant
    {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionPostfixTraceParses atomTrace nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      expressionPostfix nested block input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases (expressionPostfix_trace_success_iff_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree).mp parsed with
        ⟨output, result, afterEq, events⟩
    have frame := expressionPostfix_trace_success_context atomContext nestedContext result
    have same := State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact (expressionPostfix_trace_success_iff_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionPostfix_trace_reject_failure_state_iff_of_ne_invariant
    (atomRejectFrame : ∀ {input rejected failure}, expressionAtom nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
      expressionPostfix nested block input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (expressionPostfix_trace_reject_failure_iff_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree).mp rejection with
        ⟨rejected, result, afterEq, events⟩
    have frame := expressionPostfix_reject_context_of_windowProjection (view := TokenWindow.endByte)
      atomContext nestedContext atomRejectFrame nestedRejectFrame result
    have same := State.eq_traceResult_of_fields frame.1 frame.2 afterEq events
    exact same ▸ result
  · intro result
    exact (expressionPostfix_trace_reject_failure_iff_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionPostfix_trace_reject_state_iff_of_ne_invariant
    (atomRejectFrame : ∀ {input rejected failure}, expressionAtom nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, expressionPostfix nested block input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases (expressionPostfix_trace_reject_iff_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree).mp rejection with
        ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (expressionPostfix_trace_reject_failure_state_iff_of_ne_invariant atomSound atomRejectSound
      atomContext nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree
      atomRejectFrame nestedRejectFrame).mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (expressionPostfix_trace_reject_failure_state_iff_of_ne_invariant atomSound atomRejectSound
      atomContext nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree
      atomRejectFrame nestedRejectFrame).mpr result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PostfixTailTraceCorrespondenceProperties
/-! Pointwise postfix correspondence separates deterministic independent
outcomes from actual invariant exclusion. No fuel bound, child progress,
rejected carrier frame, or unconditional existence is hidden in these laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound nested nestedTrace)
  (rejectSound : ParserTraceRejectSound nested nestedRejects)
  (contextFrame : ParserSuccessContext nested) (block : Parser Block) (fuel : Nat) (base : Expr)
  {input : State}
  (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
  (invariantFree : ∀ error, postfixTail nested block fuel base input ≠ .invariant error)
  {value : Expr} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}

include successSound rejectSound contextFrame outcomes invariantFree

theorem postfixTail_trace_success_complete_of_ne_invariant
    (parsed : PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder base value after trace) :
    ∃ output, postfixTail nested block fuel base input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  trace_success_exists_ok_of_sound
    (parser := postfixTail nested block fuel base)
    (fun result => postfixTail_trace_success_sound successSound contextFrame block fuel base _ _ _ result)
    (fun result => postfixTail_reject_trace_sound successSound rejectSound contextFrame block fuel base _ _ _ result)
    (postfixTailTraceExactOutcomeSpec outcomes base) invariantFree parsed

theorem postfixTail_trace_reject_complete_of_ne_invariant
    (rejection : PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after report trace) :
    ∃ failure rejected, postfixTail nested block fuel base input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  trace_reject_exists_reject_of_sound
    (parser := postfixTail nested block fuel base)
    (fun result => postfixTail_trace_success_sound successSound contextFrame block fuel base _ _ _ result)
    (fun result => postfixTail_reject_trace_sound successSound rejectSound contextFrame block fuel base _ _ _ result)
    (postfixTailTraceExactOutcomeSpec outcomes base) invariantFree rejection

theorem postfixTail_trace_success_iff_of_ne_invariant :
    PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder base value after trace ↔
    ∃ output, postfixTail nested block fuel base input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact postfixTail_trace_success_complete_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree
  · rintro ⟨output, result, afterEq, events⟩
    rcases postfixTail_trace_success_sound successSound contextFrame block fuel base _ _ _ result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem postfixTail_trace_reject_iff_of_ne_invariant :
    PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after report trace ↔
    ∃ failure rejected, postfixTail nested block fuel base input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact postfixTail_trace_reject_complete_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases postfixTail_reject_trace_sound successSound rejectSound contextFrame block fuel base _ _ _ result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem postfixTail_trace_reject_failure_iff_of_ne_invariant {failure : Failure} :
    PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after failure.toDiagnostic trace ↔
    ∃ rejected, postfixTail nested block fuel base input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [postfixTail_trace_reject_iff_of_ne_invariant successSound rejectSound contextFrame
    block fuel base outcomes invariantFree]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PostfixTailTraceStateProperties
/-! Fixed-fuel postfix trace correspondence reconstructs every State field.
The explicit no-invariant premise is retained: independent trace uniqueness
does not supply fuel adequacy. Rejection needs only file/endByte preservation,
so its traced token carrier and numeric end index may differ from the input. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem postfixTail_trace_success_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested) (block : Parser Block) (fuel : Nat) (base : Expr)
    {input : State}
    (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, postfixTail nested block fuel base input ≠ .invariant error)
    {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder base value after trace ↔
      postfixTail nested block fuel base input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases (postfixTail_trace_success_iff_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree).mp parsed with ⟨output, result, afterEq, events⟩
    have frame := postfixTail_success_context contextFrame block fuel base result
    have same := State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact (postfixTail_trace_success_iff_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem postfixTail_trace_reject_failure_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (rejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (block : Parser Block) (fuel : Nat) (base : Expr) {input : State}
    (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, postfixTail nested block fuel base input ≠ .invariant error)
    {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after failure.toDiagnostic trace ↔
      postfixTail nested block fuel base input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (postfixTail_trace_reject_failure_iff_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree).mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := postfixTail_reject_source_endByte contextFrame rejectFrame block fuel base result
    have same := State.eq_traceResult_of_fields frame.1 frame.2 afterEq events
    exact same ▸ result
  · intro result
    exact (postfixTail_trace_reject_failure_iff_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem postfixTail_trace_reject_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (rejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (block : Parser Block) (fuel : Nat) (base : Expr) {input : State}
    (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, postfixTail nested block fuel base input ≠ .invariant error)
    {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after report trace ↔
      ∃ failure, postfixTail nested block fuel base input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases (postfixTail_trace_reject_iff_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree).mp rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (postfixTail_trace_reject_failure_state_iff_of_ne_invariant successSound rejectSound
      contextFrame rejectFrame block fuel base outcomes invariantFree).mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (postfixTail_trace_reject_failure_state_iff_of_ne_invariant successSound rejectSound
      contextFrame rejectFrame block fuel base outcomes invariantFree).mpr result

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PostfixTailBoundedTraceProperties
/-! Explicit loop and child budgets discharge pointwise invariant exclusion.
Completeness uses independent uniqueness/disjointness; non-vacuous outcome
existence instead uses ordinary execution and soundness alone. These claims
hold on arbitrary numerical States, not only valid token carriers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound nested nestedTrace)
  (rejectSound : ParserTraceRejectSound nested nestedRejects)
  (contextFrame : ParserSuccessContext nested) (block : Parser Block)
  (nestedFuel loopFuel : Nat) (contract : UnrestrictedFuelElementContract nested nestedFuel)
  (base : Expr) {input : State} (loopAdequate : input.remainingCount < loopFuel)
  (nestedAdequate : input.remainingCount < nestedFuel + 1)

include successSound rejectSound contextFrame contract loopAdequate nestedAdequate
include block

theorem postfixTail_trace_success_complete_of_unrestrictedElementFuel
    (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
    {value : Expr} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder base value after trace) :
    ∃ output, postfixTail nested block loopFuel base input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  postfixTail_trace_success_complete_of_ne_invariant successSound rejectSound contextFrame
    block loopFuel base outcomes
    (postfixTail_ne_invariant_of_unrestrictedElementFuel nested block nestedFuel loopFuel
      contract base input loopAdequate nestedAdequate) parsed

theorem postfixTail_trace_reject_complete_of_unrestrictedElementFuel
    (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
    {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after report trace) :
    ∃ failure rejected, postfixTail nested block loopFuel base input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  postfixTail_trace_reject_complete_of_ne_invariant successSound rejectSound contextFrame
    block loopFuel base outcomes
    (postfixTail_ne_invariant_of_unrestrictedElementFuel nested block nestedFuel loopFuel
      contract base input loopAdequate nestedAdequate) rejection

/-- Unlike joint exactness, this supplies an actual traced outcome. -/
theorem postfixTail_exists_trace_outcome_of_unrestrictedElementFuel :
    (∃ value output trace,
      postfixTail nested block loopFuel base input = .ok value output ∧
      PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
        input.declarativeRemainder base value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      postfixTail nested block loopFuel base input = .reject failure rejected ∧
      PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
        input.declarativeRemainder base rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases postfixTail_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract
      loopFuel base input loopAdequate nestedAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases postfixTail_trace_success_sound successSound contextFrame block loopFuel base _ _ _ result with
      ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases postfixTail_reject_trace_sound successSound rejectSound contextFrame block loopFuel base _ _ _ result with
      ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

omit loopAdequate nestedAdequate in
theorem postfixTailTrace_outcome_exists_of_unrestrictedElementFuel
    (source : SourceId) (endByte : Nat) (input : Remainder)
    (adequate : input.endIndex - input.cursor < nestedFuel + 1) :
    (∃ value output trace, PostfixTailTraceParses nestedTrace source endByte input base value output trace) ∨
    (∃ rejected report trace, PostfixTailTraceRejects nestedTrace nestedRejects
      source endByte input base rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  rcases postfixTail_exists_trace_outcome_of_unrestrictedElementFuel successSound rejectSound contextFrame
      block nestedFuel (state.remainingCount + 1) contract base (Nat.lt_succ_self _) adequate with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, rejection⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PostfixTailRejectionTraceCompletenessProperties
/-! Every finite independent rejection executes at all sufficiently large
postfix fuels. The threshold counts derivation steps, not cursor distance;
successful index children may rewind and failed children need no frame law. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar DelimitedTraceInternals

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem complete_at_variant
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
  complete_at_variant successComplete rejectComplete contextFrame block rejection input rfl rfl rfl

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.UnaryOperatorsTraceProperties
/-! Prefix unary scanning is silent on every successful fuel/accumulator
combination and can never reject. Production fuel is adequate on arbitrary
States. Exact initial-scan correspondence fixes the complete operator list,
visible remainder, and every State field without a validity premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

theorem unaryOperators_success_state_shape :
    ∀ fuel operatorsRev {input output : State} {operators : List (Located UnaryOp)},
      unaryOperators fuel operatorsRev input = .ok operators output →
      output = { input with cursor := output.cursor } := by
  intro fuel
  induction fuel with
  | zero => intro operatorsRev input output operators result; simp [unaryOperators] at result
  | succ fuel ih =>
      intro operatorsRev input output operators result
      unfold unaryOperators at result
      cases found : input.peek? with
      | none => simp only [found] at result; cases result; rfl
      | some token =>
          simp only [found] at result
          cases decoded : unaryOp? token.value with
          | none => simp only [decoded] at result; cases result; rfl
          | some operator =>
              simp only [decoded] at result
              exact ih ({ span := token.span, value := operator } :: operatorsRev)
                (input := { input with cursor := input.cursor + 1 }) result

theorem unaryOperators_success_context (fuel : Nat) (operatorsRev : List (Located UnaryOp)) :
    ParserSuccessContext (unaryOperators fuel operatorsRev) := by
  intro input output operators result
  have shape := unaryOperators_success_state_shape fuel operatorsRev result
  rw [shape]
  exact ⟨rfl, rfl⟩

theorem unaryOperators_diagnostics_eq_onSuccess (fuel : Nat) (operatorsRev : List (Located UnaryOp))
    {input output : State} {operators : List (Located UnaryOp)}
    (result : unaryOperators fuel operatorsRev input = .ok operators output) :
    output.diagnostics = input.diagnostics := by
  rw [unaryOperators_success_state_shape fuel operatorsRev result]
  rfl

theorem unaryOperators_ne_reject :
    ∀ fuel operatorsRev input failure rejected,
      unaryOperators fuel operatorsRev input ≠ .reject failure rejected := by
  intro fuel
  induction fuel with
  | zero => intro operatorsRev input failure rejected result; simp [unaryOperators] at result
  | succ fuel ih =>
      intro operatorsRev input failure rejected result
      unfold unaryOperators at result
      cases found : input.peek? with
      | none => simp [found] at result
      | some token =>
          simp only [found] at result
          cases decoded : unaryOp? token.value with
          | none => simp [decoded] at result
          | some operator =>
              simp only [decoded] at result
              exact ih ({ span := token.span, value := operator } :: operatorsRev)
                { input with cursor := input.cursor + 1 } failure rejected result

theorem unaryOperators_trace_success_sound {fuel : Nat} {input output : State}
    {operators : List (Located UnaryOp)} (result : unaryOperators fuel [] input = .ok operators output) :
    UnaryOperatorsParses input.declarativeRemainder operators output.declarativeRemainder ∧
      output = input.traceResult output.declarativeRemainder [] := by
  have frame := unaryOperators_success_context fuel [] result
  exact ⟨unaryOperators_success_sound result, State.eq_traceResult_of_fields frame.1
    (congrArg TokenWindow.endByte frame.2) rfl (by
      simpa only [List.append_nil] using unaryOperators_diagnostics_eq_onSuccess fuel [] result)⟩

theorem unaryOperators_trace_success_complete {input : State} {operators : List (Located UnaryOp)}
    {after : Remainder} (parsed : UnaryOperatorsParses input.declarativeRemainder operators after) :
    unaryOperators (input.remainingCount + 1) [] input = .ok operators (input.traceResult after []) := by
  rcases unaryOperators_production_exists_ok [] input with ⟨actual, output, result⟩
  have sound := unaryOperators_trace_success_sound result
  rcases sound.1.result_unique parsed with ⟨rfl, afterEq⟩
  have same := sound.2.trans (congrArg (fun remainder => input.traceResult remainder []) afterEq)
  exact same ▸ result

theorem unaryOperators_trace_success_state_iff {input : State} {operators : List (Located UnaryOp)}
    {after : Remainder} :
    UnaryOperatorsParses input.declarativeRemainder operators after ↔
      unaryOperators (input.remainingCount + 1) [] input = .ok operators (input.traceResult after []) := by
  constructor
  · exact unaryOperators_trace_success_complete
  · intro result
    simpa only [State.traceResult_declarativeRemainder] using unaryOperators_success_sound result

theorem unaryOperators_exists_exact_trace_outcome (input : State) :
    ∃ operators after, UnaryOperatorsParses input.declarativeRemainder operators after ∧
      unaryOperators (input.remainingCount + 1) [] input = .ok operators (input.traceResult after []) := by
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, output, result⟩
  have sound := unaryOperators_trace_success_sound result
  exact ⟨operators, output.declarativeRemainder, sound.1, sound.2 ▸ result⟩

/-- Independent maximal prefixes actually exist; their uniqueness alone was
not used as a substitute for the scanner's successful production execution. -/
theorem unaryOperatorsTrace_outcome_exists (input : Remainder) :
    ∃ operators after, UnaryOperatorsParses input operators after := by
  let state : State := {
    file := { id := { origin := .main, path := "" }, content := "" }, tokens := input.tokens
    cursor := input.cursor, window := { endIndex := input.endIndex, endByte := 0 }, diagnosticsRev := []
  }
  rcases unaryOperators_exists_exact_trace_outcome state with ⟨operators, after, parsed, _⟩
  exact ⟨operators, after, parsed⟩

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionUnaryTraceProperties
/-! Maximal unary scanning is unconditionally successful and silent, so each
postfix trace contract independently lifts to the actual unary layer. No
postfix progress, source/window frame, joint exactness, or totality premise is
needed for the four trace laws. Successful context is a separate fifth law. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {postfixTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionUnary_trace_success_sound
    (successSound : ParserTraceSuccessSound (expressionPostfix nested block) postfixTrace) :
    ParserTraceSuccessSound (expressionUnary nested block) (ExpressionUnaryTraceParses postfixTrace) := by
  intro input output value result
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, afterOperators, prefixResult⟩
  unfold expressionUnary at result
  simp only [prefixResult] at result
  cases childResult : expressionPostfix nested block afterOperators with
  | invariant error => simp [childResult] at result
  | reject failure rejected => simp [childResult] at result
  | ok base next =>
      simp only [childResult] at result; cases result
      rcases successSound childResult with ⟨trace, parsed, events⟩
      have frame := unaryOperators_success_context _ [] prefixResult
      refine ⟨trace, .parsed (unaryOperators_success_sound prefixResult) ?_, ?_⟩
      · simpa only [frame.1, frame.2] using parsed
      · rw [events, unaryOperators_diagnostics_eq_onSuccess _ [] prefixResult]

theorem expressionUnary_reject_trace_sound
    (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects) :
    ParserTraceRejectSound (expressionUnary nested block) (ExpressionUnaryTraceRejects postfixRejects) := by
  intro input rejected failure result
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, afterOperators, prefixResult⟩
  unfold expressionUnary at result
  simp only [prefixResult] at result
  cases childResult : expressionPostfix nested block afterOperators with
  | invariant error => simp [childResult] at result
  | ok base next => simp [childResult] at result
  | reject actual next =>
      simp only [childResult] at result; cases result
      rcases rejectSound childResult with ⟨trace, rejection, events⟩
      have frame := unaryOperators_success_context _ [] prefixResult
      refine ⟨trace, .postfixRejected (unaryOperators_success_sound prefixResult) ?_, ?_⟩
      · simpa only [frame.1, frame.2] using rejection
      · rw [events, unaryOperators_diagnostics_eq_onSuccess _ [] prefixResult]

theorem expressionUnary_trace_success_complete
    (successComplete : ParserTraceSuccessComplete (expressionPostfix nested block) postfixTrace) :
    ParserTraceSuccessComplete (expressionUnary nested block) (ExpressionUnaryTraceParses postfixTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed prefixParsed childParsed =>
      have prefixResult := unaryOperators_trace_success_complete prefixParsed
      rcases successComplete (input := input.traceResult _ []) (by
          simpa only [State.traceResult, State.declarativeRemainder] using childParsed) with
        ⟨output, childResult, afterEq, events⟩
      refine ⟨output, ?_, afterEq, ?_⟩
      · simp only [expressionUnary, prefixResult, childResult,
          applyUnaryOperators, DeclarativeGrammar.applyUnaryOperators]
      · simpa only [State.traceResult_diagnostics, List.append_nil] using events

theorem expressionUnary_trace_reject_complete
    (rejectComplete : ParserTraceRejectComplete (expressionPostfix nested block) postfixRejects) :
    ParserTraceRejectComplete (expressionUnary nested block) (ExpressionUnaryTraceRejects postfixRejects) := by
  intro input after report trace rejection
  cases rejection with
  | postfixRejected prefixParsed childRejected =>
      have prefixResult := unaryOperators_trace_success_complete prefixParsed
      rcases rejectComplete (input := input.traceResult _ []) (by
          simpa only [State.traceResult, State.declarativeRemainder] using childRejected) with
        ⟨failure, rejected, childResult, afterEq, reportEq, events⟩
      refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
      · simp only [expressionUnary, prefixResult, childResult]
      · simpa only [State.traceResult_diagnostics, List.append_nil] using events

theorem expressionUnary_trace_success_context
    (contextFrame : ParserSuccessContext (expressionPostfix nested block)) :
    ParserSuccessContext (expressionUnary nested block) := by
  intro input output value result
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, afterOperators, prefixResult⟩
  unfold expressionUnary at result
  simp only [prefixResult] at result
  cases childResult : expressionPostfix nested block afterOperators with
  | invariant error => simp [childResult] at result
  | reject failure rejected => simp [childResult] at result
  | ok base next =>
      simp only [childResult] at result; cases result
      have prefixFrame := unaryOperators_success_context _ [] prefixResult
      have childFrame := contextFrame childResult
      exact ⟨childFrame.1.trans prefixFrame.1, childFrame.2.trans prefixFrame.2⟩

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionUnaryTraceCorrespondenceProperties
/-! Unary success and rejection correspondence use only the matching supplied
postfix soundness/completeness directions. The silent production prefix adds
no diagnostic, frame, progress, joint-exactness, or invariant-free premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {postfixTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionUnary_trace_success_iff
    (successSound : ParserTraceSuccessSound (expressionPostfix nested block) postfixTrace)
    (successComplete : ParserTraceSuccessComplete (expressionPostfix nested block) postfixTrace)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceParses postfixTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, expressionUnary nested block input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionUnary_trace_success_complete successComplete
  · rintro ⟨output, result, afterEq, events⟩
    rcases expressionUnary_trace_success_sound successSound result with ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem expressionUnary_trace_reject_iff
    (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects)
    (rejectComplete : ParserTraceRejectComplete (expressionPostfix nested block) postfixRejects)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, expressionUnary nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionUnary_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases expressionUnary_reject_trace_sound rejectSound result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem expressionUnary_trace_reject_failure_iff
    (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects)
    (rejectComplete : ParserTraceRejectComplete (expressionPostfix nested block) postfixRejects)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, expressionUnary nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [expressionUnary_trace_reject_iff rejectSound rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionUnaryTraceStateProperties
/-! Whole unary replies are reconstructed from the exact traced remainder.
Both successful and rejected postfix frames preserve only file/endByte; token
carriers, cursors, and numeric endIndex remain whatever the trace specifies.
Prefix scanning is unconditionally successful and preserves every other field. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {postfixTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {postfixRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem unary_success_frame
    (postfixFrame : ∀ {input output value}, expressionPostfix nested block input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    {input output : State} {value : Expr}
    (result : expressionUnary nested block input = .ok value output) :
    output.file = input.file ∧ output.window.endByte = input.window.endByte := by
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, next, prefixResult⟩
  have prefixFrame := unaryOperators_success_context (input.remainingCount + 1) [] prefixResult
  simp only [expressionUnary, prefixResult] at result
  cases postfixResult : expressionPostfix nested block next with
  | invariant error => simp [postfixResult] at result
  | reject failure rejected => simp [postfixResult] at result
  | ok base final =>
      simp only [postfixResult] at result
      cases result
      have frame := postfixFrame postfixResult
      exact ⟨frame.1.trans prefixFrame.1, frame.2.trans (congrArg TokenWindow.endByte prefixFrame.2)⟩

private theorem unary_reject_frame
    (postfixFrame : ∀ {input rejected failure}, expressionPostfix nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input rejected : State} {failure : Failure}
    (result : expressionUnary nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte := by
  rcases unaryOperators_production_exists_ok [] input with ⟨operators, next, prefixResult⟩
  have prefixFrame := unaryOperators_success_context (input.remainingCount + 1) [] prefixResult
  simp only [expressionUnary, prefixResult] at result
  cases postfixResult : expressionPostfix nested block next with
  | invariant error => simp [postfixResult] at result
  | ok base final => simp [postfixResult] at result
  | reject actual final =>
      simp only [postfixResult] at result
      cases result
      have frame := postfixFrame postfixResult
      exact ⟨frame.1.trans prefixFrame.1, frame.2.trans (congrArg TokenWindow.endByte prefixFrame.2)⟩

theorem expressionUnary_trace_success_state_iff
    (successSound : ParserTraceSuccessSound (expressionPostfix nested block) postfixTrace)
    (successComplete : ParserTraceSuccessComplete (expressionPostfix nested block) postfixTrace)
    (postfixFrame : ∀ {input output value}, expressionPostfix nested block input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceParses postfixTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      expressionUnary nested block input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases (expressionUnary_trace_success_iff successSound successComplete).mp parsed with
      ⟨output, result, afterEq, events⟩
    have frame := unary_success_frame postfixFrame result
    exact State.eq_traceResult_of_fields frame.1 frame.2 afterEq events ▸ result
  · intro result
    exact (expressionUnary_trace_success_iff successSound successComplete).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionUnary_trace_reject_failure_state_iff
    (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects)
    (rejectComplete : ParserTraceRejectComplete (expressionPostfix nested block) postfixRejects)
    (postfixFrame : ∀ {input rejected failure}, expressionPostfix nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      expressionUnary nested block input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (expressionUnary_trace_reject_failure_iff rejectSound rejectComplete).mp rejection with
      ⟨rejected, result, afterEq, events⟩
    have frame := unary_reject_frame postfixFrame result
    exact State.eq_traceResult_of_fields frame.1 frame.2 afterEq events ▸ result
  · intro result
    exact (expressionUnary_trace_reject_failure_iff rejectSound rejectComplete).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionUnary_trace_reject_state_iff
    (rejectSound : ParserTraceRejectSound (expressionPostfix nested block) postfixRejects)
    (rejectComplete : ParserTraceRejectComplete (expressionPostfix nested block) postfixRejects)
    (postfixFrame : ∀ {input rejected failure}, expressionPostfix nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, expressionUnary nested block input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases (expressionUnary_trace_reject_iff rejectSound rejectComplete).mp rejection with
      ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (expressionUnary_trace_reject_failure_state_iff rejectSound rejectComplete postfixFrame).mp
      (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (expressionUnary_trace_reject_failure_state_iff rejectSound rejectComplete postfixFrame).mpr result

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.LeftAssociativeTraceSoundnessProperties
/-! Exact ordinary-outcome soundness at every left-associative loop fuel.
Only successful operand file/endByte framing is needed to compose traces.
No progress, endIndex/token preservation, rejected frame, or totality premise
is silently imposed on the operand. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {operand : Parser Expr}
  {operandTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem leftAssociativeTail_trace_success_sound
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) : ∀ fuel left input value output,
      leftAssociativeTail operand precedence fuel left input = .ok value output →
      ∃ trace, LeftAssociativeTailTraceParses operandTrace precedence input.file.id input.window.endByte
        input.declarativeRemainder left value output.declarativeRemainder trace ∧
        output.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro left input value output result; simp [leftAssociativeTail] at result
  | succ fuel ih =>
      intro left input value output result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [leftAssociativeTail, operatorResult] at result
          cases result
          exact ⟨[], .done (binaryAtPrecedence?_none_absentAt operatorResult), (List.append_nil _).symm⟩
      | some operator =>
          have operatorParsed := consumeBinary_success_sound_of_binaryAtPrecedence?_some
            operatorResult (consumeBinary_ok_state_shape operator input)
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape] at result
          cases childResult : operand { input with cursor := input.cursor + operator.value.tokenCount } with
          | invariant error => simp [childResult] at result
          | reject failure rejected => simp [childResult] at result
          | ok right next =>
              simp only [childResult] at result
              rcases successSound childResult with ⟨rightEvents, rightParsed, rightEq⟩
              have frame := successFrame childResult
              rcases ih (binaryNode left operator right) next value output result with
                ⟨tailEvents, tailParsed, tailEq⟩
              refine ⟨rightEvents ++ tailEvents, .next operatorParsed rightParsed ?_, ?_⟩
              · simpa only [frame.1, frame.2, binaryNode, DeclarativeGrammar.binaryNode] using tailParsed
              · rw [tailEq, rightEq]; exact List.append_assoc _ _ _

theorem leftAssociativeTail_reject_trace_sound
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (rejectSound : ParserTraceRejectSound operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) : ∀ fuel left input failure rejected,
      leftAssociativeTail operand precedence fuel left input = .reject failure rejected →
      ∃ trace, LeftAssociativeTailTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
        input.declarativeRemainder left rejected.declarativeRemainder failure.toDiagnostic trace ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro left input failure rejected result; simp [leftAssociativeTail] at result
  | succ fuel ih =>
      intro left input failure rejected result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => simp [leftAssociativeTail, operatorResult] at result
      | some operator =>
          have operatorParsed := consumeBinary_success_sound_of_binaryAtPrecedence?_some
            operatorResult (consumeBinary_ok_state_shape operator input)
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape] at result
          cases childResult : operand { input with cursor := input.cursor + operator.value.tokenCount } with
          | invariant error => simp [childResult] at result
          | reject actual next =>
              simp only [childResult] at result; cases result
              rcases rejectSound childResult with ⟨trace, rejection, events⟩
              exact ⟨trace, .rightRejected operatorParsed rejection, events⟩
          | ok right next =>
              simp only [childResult] at result
              rcases successSound childResult with ⟨rightEvents, rightParsed, rightEq⟩
              have frame := successFrame childResult
              rcases ih (binaryNode left operator right) next failure rejected result with
                ⟨tailEvents, tailRejected, tailEq⟩
              refine ⟨rightEvents ++ tailEvents, .laterRejected operatorParsed rightParsed ?_, ?_⟩
              · simpa only [frame.1, frame.2, binaryNode, DeclarativeGrammar.binaryNode] using tailRejected
              · rw [tailEq, rightEq]; exact List.append_assoc _ _ _

theorem leftAssociative_trace_success_sound
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) :
    ParserTraceSuccessSound (leftAssociative operand precedence) (LeftAssociativeTraceParses operandTrace precedence) := by
  intro input output value result
  unfold leftAssociative at result
  cases firstResult : operand input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok left next =>
      simp only [firstResult] at result
      rcases successSound firstResult with ⟨leftEvents, leftParsed, leftEq⟩
      have frame := successFrame firstResult
      rcases leftAssociativeTail_trace_success_sound successSound successFrame precedence
          (next.remainingCount + 1) left next value output result with ⟨tailEvents, tailParsed, tailEq⟩
      refine ⟨leftEvents ++ tailEvents, .parsed leftParsed ?_, ?_⟩
      · simpa only [frame.1, frame.2] using tailParsed
      · rw [tailEq, leftEq]; exact List.append_assoc _ _ _

theorem leftAssociative_reject_trace_sound
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (rejectSound : ParserTraceRejectSound operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) : ParserTraceRejectSound (leftAssociative operand precedence)
      (LeftAssociativeTraceRejects operandTrace operandRejects precedence) := by
  intro input rejected failure result
  unfold leftAssociative at result
  cases firstResult : operand input with
  | invariant error => simp [firstResult] at result
  | reject actual next =>
      simp only [firstResult] at result; cases result
      rcases rejectSound firstResult with ⟨trace, rejection, events⟩
      exact ⟨trace, .firstRejected rejection, events⟩
  | ok left next =>
      simp only [firstResult] at result
      rcases successSound firstResult with ⟨leftEvents, leftParsed, leftEq⟩
      have frame := successFrame firstResult
      rcases leftAssociativeTail_reject_trace_sound successSound rejectSound successFrame precedence
          (next.remainingCount + 1) left next failure rejected result with ⟨tailEvents, tailRejected, tailEq⟩
      refine ⟨leftEvents ++ tailEvents, .tailRejected leftParsed ?_, ?_⟩
      · simpa only [frame.1, frame.2] using tailRejected
      · rw [tailEq, leftEq]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.LeftAssociativeTraceCorrespondenceProperties
/-! Whole left-associative correspondence uses independent operand exactness
and explicit pointwise invariant exclusion. Successful operand framing keeps
only file/endByte. Neither child completeness nor a full-window/progress law
is required, and independent uniqueness is not promoted to runtime totality. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {operand : Parser Expr}
  {operandTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound operand operandTrace)
  (rejectSound : ParserTraceRejectSound operand operandRejects)
  (successFrame : ∀ {input output value}, operand input = .ok value output →
    output.file = input.file ∧ output.window.endByte = input.window.endByte)
  (precedence : Nat) {input : State}
  (outcomes : TraceExactOutcomeSpec operandTrace operandRejects input.file.id input.window.endByte)
  (invariantFree : ∀ error, leftAssociative operand precedence input ≠ .invariant error)
  {value : Expr} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}

include successSound rejectSound successFrame outcomes invariantFree

theorem leftAssociative_trace_success_complete_of_ne_invariant
    (parsed : LeftAssociativeTraceParses operandTrace precedence input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    ∃ output, leftAssociative operand precedence input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  trace_success_exists_ok_of_sound
    (leftAssociative_trace_success_sound successSound successFrame precedence)
    (leftAssociative_reject_trace_sound successSound rejectSound successFrame precedence)
    (leftAssociativeTraceExactOutcomeSpec outcomes precedence) invariantFree parsed

theorem leftAssociative_trace_reject_complete_of_ne_invariant
    (rejection : LeftAssociativeTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder after report trace) :
    ∃ failure rejected, leftAssociative operand precedence input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  trace_reject_exists_reject_of_sound
    (leftAssociative_trace_success_sound successSound successFrame precedence)
    (leftAssociative_reject_trace_sound successSound rejectSound successFrame precedence)
    (leftAssociativeTraceExactOutcomeSpec outcomes precedence) invariantFree rejection

theorem leftAssociative_trace_success_iff_of_ne_invariant :
    LeftAssociativeTraceParses operandTrace precedence input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, leftAssociative operand precedence input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact leftAssociative_trace_success_complete_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree
  · rintro ⟨output, result, afterEq, events⟩
    rcases leftAssociative_trace_success_sound successSound successFrame precedence result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem leftAssociative_trace_reject_iff_of_ne_invariant :
    LeftAssociativeTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, leftAssociative operand precedence input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact leftAssociative_trace_reject_complete_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases leftAssociative_reject_trace_sound successSound rejectSound successFrame precedence result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem leftAssociative_trace_reject_failure_iff_of_ne_invariant {failure : Failure} :
    LeftAssociativeTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, leftAssociative operand precedence input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [leftAssociative_trace_reject_iff_of_ne_invariant successSound rejectSound successFrame precedence outcomes invariantFree]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.LeftAssociativeTraceCompletenessProperties
/-! Every finite independent left-associative tail derivation executes above
a derivation-dependent loop bound. Successful operands need only file/endByte
framing and may rewind or replace their numeric window and tokens. No bound by
remainingCount or completeness for the fixed-production whole layer follows. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

private theorem binary_none_of_absent {input : State} {precedence : Nat}
    (absent : BinaryOperatorAtPrecedenceAbsentAt precedence input.declarativeRemainder) :
    binaryAtPrecedence? input precedence = none := by
  cases selected : binaryAtPrecedence? input precedence with
  | none => rfl
  | some operator =>
      have parsed := consumeBinary_success_sound_of_binaryAtPrecedence?_some selected
        (consumeBinary_ok_state_shape operator input)
      exact False.elim (parsed.not_absent absent)

private theorem binary_some_of_parsed {input : State} {precedence : Nat} {after : Remainder}
    {operator : Located BinaryOp}
    (parsed : BinaryOperatorAtPrecedenceParses precedence input.declarativeRemainder operator after) :
    binaryAtPrecedence? input precedence = some operator := by
  rcases parsed with ⟨operatorPrecedence, decoded, _⟩
  have found : BinaryOp.at? input.tokens input.window.endIndex input.cursor = some operator :=
    decoded
  have selected : (operator.value.precedence == precedence) = true :=
    beq_iff_eq.mpr operatorPrecedence
  simp only [binaryAtPrecedence?, found, selected, if_true]

variable {operand : Parser Expr}
  {operandTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem success_complete_at
    (successComplete : ParserTraceSuccessComplete operand operandTrace)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    {precedence : Nat} {source : SourceId} {endByte : Nat} {before after : Remainder}
    {left value : Expr} {trace : List ParseDiagnostic}
    (parsed : LeftAssociativeTailTraceParses operandTrace precedence source endByte before left value after trace) :
    ∀ input : State, input.file.id = source → input.window.endByte = endByte →
      input.declarativeRemainder = before →
      ∃ bound, ∀ fuel, bound ≤ fuel → ∃ output,
        leftAssociativeTail operand precedence fuel left input = .ok value output ∧
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
          exact ⟨input, by simp only [leftAssociativeTail, binary_none_of_absent absent],
            rfl, (List.append_nil _).symm⟩
  | @next before afterOperator afterRight output left right expression operator rightEvents
      tailEvents operatorParsed rightParsed tail ih =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have operatorResult := binary_some_of_parsed operatorParsed
      rcases operatorParsed with ⟨_, _, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + operator.value.tokenCount }) rightParsed with
        ⟨next, childResult, nextAfter, childEvents⟩
      have frame := successFrame childResult
      rcases ih next (congrArg SourceFile.id frame.1) frame.2 nextAfter with ⟨bound, tailComplete⟩
      refine ⟨bound + 1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          rcases tailComplete fuel (by omega) with ⟨output, result, afterEq, events⟩
          refine ⟨output, ?_, afterEq, ?_⟩
          · simpa only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape, childResult,
              binaryNode, DeclarativeGrammar.binaryNode] using result
          · rw [events, childEvents]
            exact List.append_assoc _ _ _

private theorem reject_complete_at
    (successComplete : ParserTraceSuccessComplete operand operandTrace)
    (rejectComplete : ParserTraceRejectComplete operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    {precedence : Nat} {source : SourceId} {endByte : Nat} {before after : Remainder}
    {left : Expr} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte before left after report trace) :
    ∀ input : State, input.file.id = source → input.window.endByte = endByte →
      input.declarativeRemainder = before →
      ∃ bound, ∀ fuel, bound ≤ fuel → ∃ failure rejected,
        leftAssociativeTail operand precedence fuel left input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  induction rejection with
  | @rightRejected before afterOperator rejected left operator report trace operatorParsed
      rightRejected =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have operatorResult := binary_some_of_parsed operatorParsed
      rcases operatorParsed with ⟨_, _, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + operator.value.tokenCount }) rightRejected with
        ⟨failure, rejected, childResult, afterEq, reportEq, events⟩
      refine ⟨1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨failure, rejected, by simp only [leftAssociativeTail, operatorResult,
            consumeBinary_ok_state_shape, childResult], afterEq, reportEq, events⟩
  | @laterRejected before afterOperator afterRight rejected left right operator report
      rightEvents tailEvents operatorParsed rightParsed tail ih =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have operatorResult := binary_some_of_parsed operatorParsed
      rcases operatorParsed with ⟨_, _, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + operator.value.tokenCount }) rightParsed with
        ⟨next, childResult, nextAfter, childEvents⟩
      have frame := successFrame childResult
      rcases ih next (congrArg SourceFile.id frame.1) frame.2 nextAfter with ⟨bound, tailComplete⟩
      refine ⟨bound + 1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          rcases tailComplete fuel (by omega) with ⟨failure, rejected, result, afterEq, reportEq, events⟩
          refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
          · simpa only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape, childResult,
              binaryNode, DeclarativeGrammar.binaryNode] using result
          · rw [events, childEvents]
            exact List.append_assoc _ _ _

theorem leftAssociativeTail_trace_success_complete_eventually
    (successComplete : ParserTraceSuccessComplete operand operandTrace)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) {input : State} {left value : Expr} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : LeftAssociativeTailTraceParses operandTrace precedence input.file.id input.window.endByte
      input.declarativeRemainder left value after trace) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ output,
      leftAssociativeTail operand precedence fuel left input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  success_complete_at successComplete successFrame parsed input rfl rfl rfl

theorem leftAssociativeTail_trace_reject_complete_eventually
    (successComplete : ParserTraceSuccessComplete operand operandTrace)
    (rejectComplete : ParserTraceRejectComplete operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) {input : State} {left : Expr} {after : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder left after report trace) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ failure rejected,
      leftAssociativeTail operand precedence fuel left input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  reject_complete_at successComplete rejectComplete successFrame rejection input rfl rfl rfl

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.LeftAssociativeTraceContextProperties
/-! Left-associative execution retains source and an arbitrary window
observation under exactly the corresponding operand frames. Successful child
frames need not preserve the entire window. No token carrier, progress,
trace, ordinary-execution, or validity assumption is used. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

variable {operand : Parser Expr} {β : Type} {view : TokenWindow → β}

theorem leftAssociativeTail_success_context_of_windowProjection
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window)
    (precedence : Nat) : ∀ fuel left {input output : State} {value : Expr},
      leftAssociativeTail operand precedence fuel left input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window := by
  intro fuel
  induction fuel with
  | zero => intro left input output value result; simp [leftAssociativeTail] at result
  | succ fuel ih =>
      intro left input output value result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => simp only [leftAssociativeTail, operatorResult] at result; cases result; exact ⟨rfl, rfl⟩
      | some operator =>
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape] at result
          cases childResult : operand { input with cursor := input.cursor + operator.value.tokenCount } with
          | invariant error => simp [childResult] at result
          | reject failure rejected => simp [childResult] at result
          | ok right next =>
              simp only [childResult] at result
              have childFrame := successFrame childResult
              have tailFrame := ih (binaryNode left operator right) result
              exact ⟨tailFrame.1.trans childFrame.1, tailFrame.2.trans childFrame.2⟩

theorem leftAssociativeTail_reject_context_of_windowProjection
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window)
    (rejectFrame : ∀ {input rejected failure}, operand input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    (precedence : Nat) : ∀ fuel left {input rejected : State} {failure : Failure},
      leftAssociativeTail operand precedence fuel left input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window := by
  intro fuel
  induction fuel with
  | zero => intro left input rejected failure result; simp [leftAssociativeTail] at result
  | succ fuel ih =>
      intro left input rejected failure result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => simp [leftAssociativeTail, operatorResult] at result
      | some operator =>
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape] at result
          cases childResult : operand { input with cursor := input.cursor + operator.value.tokenCount } with
          | invariant error => simp [childResult] at result
          | reject actual next =>
              simp only [childResult] at result; cases result
              exact rejectFrame (input := { input with cursor := input.cursor + operator.value.tokenCount }) childResult
          | ok right next =>
              simp only [childResult] at result
              have childFrame := successFrame childResult
              have tailFrame := ih (binaryNode left operator right) result
              exact ⟨tailFrame.1.trans childFrame.1, tailFrame.2.trans childFrame.2⟩

theorem leftAssociative_success_context_of_windowProjection
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window)
    (precedence : Nat) {input output : State} {value : Expr}
    (result : leftAssociative operand precedence input = .ok value output) :
    output.file = input.file ∧ view output.window = view input.window := by
  unfold leftAssociative at result
  cases firstResult : operand input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok left next =>
      simp only [firstResult] at result
      have childFrame := successFrame firstResult
      have tailFrame := leftAssociativeTail_success_context_of_windowProjection successFrame
        precedence (next.remainingCount + 1) left result
      exact ⟨tailFrame.1.trans childFrame.1, tailFrame.2.trans childFrame.2⟩

theorem leftAssociative_reject_context_of_windowProjection
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window)
    (rejectFrame : ∀ {input rejected failure}, operand input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    (precedence : Nat) {input rejected : State} {failure : Failure}
    (result : leftAssociative operand precedence input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  unfold leftAssociative at result
  cases firstResult : operand input with
  | invariant error => simp [firstResult] at result
  | reject actual next => simp only [firstResult] at result; cases result; exact rejectFrame firstResult
  | ok left next =>
      simp only [firstResult] at result
      have childFrame := successFrame firstResult
      have tailFrame := leftAssociativeTail_reject_context_of_windowProjection successFrame rejectFrame
        precedence (next.remainingCount + 1) left result
      exact ⟨tailFrame.1.trans childFrame.1, tailFrame.2.trans childFrame.2⟩

theorem leftAssociativeTail_success_context (successFrame : ParserSuccessContext operand)
    (precedence fuel : Nat) (left : Expr) : ParserSuccessContext (leftAssociativeTail operand precedence fuel left) := by
  intro input output value result
  exact leftAssociativeTail_success_context_of_windowProjection (view := id) successFrame precedence fuel left result

theorem leftAssociative_success_context (successFrame : ParserSuccessContext operand)
    (precedence : Nat) : ParserSuccessContext (leftAssociative operand precedence) := by
  intro input output value result
  exact leftAssociative_success_context_of_windowProjection (view := id) successFrame precedence result

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.LeftAssociativeTraceStateProperties
/-! Whole-State left-associative correspondence preserves every traced token,
cursor, endIndex, and ordered event. Only file/endByte frames reconstruct the
untraced fields; successful or rejected children may replace the token carrier
or numeric window. Pointwise invariant exclusion remains explicit. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {operand : Parser Expr}
  {operandTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem leftAssociative_trace_success_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (rejectSound : ParserTraceRejectSound operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) {input : State}
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, leftAssociative operand precedence input ≠ .invariant error)
    {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    LeftAssociativeTraceParses operandTrace precedence input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      leftAssociative operand precedence input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases (leftAssociative_trace_success_iff_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree).mp parsed with ⟨output, result, afterEq, events⟩
    have frame := leftAssociative_success_context_of_windowProjection successFrame precedence result
    exact State.eq_traceResult_of_fields frame.1 frame.2 afterEq events ▸ result
  · intro result
    exact (leftAssociative_trace_success_iff_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem leftAssociative_trace_reject_failure_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (rejectSound : ParserTraceRejectSound operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (rejectFrame : ∀ {input rejected failure}, operand input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (precedence : Nat) {input : State}
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, leftAssociative operand precedence input ≠ .invariant error)
    {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LeftAssociativeTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      leftAssociative operand precedence input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (leftAssociative_trace_reject_failure_iff_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree).mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := leftAssociative_reject_context_of_windowProjection successFrame rejectFrame precedence result
    exact State.eq_traceResult_of_fields frame.1 frame.2 afterEq events ▸ result
  · intro result
    exact (leftAssociative_trace_reject_failure_iff_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem leftAssociative_trace_reject_state_iff_of_ne_invariant
    (successSound : ParserTraceSuccessSound operand operandTrace)
    (rejectSound : ParserTraceRejectSound operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (rejectFrame : ∀ {input rejected failure}, operand input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (precedence : Nat) {input : State}
    (outcomes : TraceExactOutcomeSpec operandTrace operandRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, leftAssociative operand precedence input ≠ .invariant error)
    {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LeftAssociativeTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, leftAssociative operand precedence input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases (leftAssociative_trace_reject_iff_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree).mp rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (leftAssociative_trace_reject_failure_state_iff_of_ne_invariant successSound rejectSound
      successFrame rejectFrame precedence outcomes invariantFree).mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (leftAssociative_trace_reject_failure_state_iff_of_ne_invariant successSound rejectSound
      successFrame rejectFrame precedence outcomes invariantFree).mpr result

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.LeftAssociativeUnrestrictedFuelContractProperties
/-! Left-associative layers preserve unrestricted operand contracts at the
same fuel. A tail has one extra unit of operand allowance because its actual
recognized operator is consumed before the child. Successful numeric frames
hold at every fuel and on arbitrary States, independently of ordinary bounds.
No validity, source, token-carrier, or byte-end frame is required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem leftAssociativeTail_endIndex_onSuccess
    (operand : Parser Expr)
    (operandSuccess : ∀ {input output value}, operand input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (precedence : Nat) : ∀ fuel left {input output : State} {value : Expr},
      leftAssociativeTail operand precedence fuel left input = .ok value output →
      output.window.endIndex = input.window.endIndex := by
  intro fuel
  induction fuel with
  | zero => intro left input output value result; simp [leftAssociativeTail] at result
  | succ fuel ih =>
      intro left input output value result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => simp only [leftAssociativeTail, operatorResult] at result; cases result; rfl
      | some operator =>
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape] at result
          cases childResult : operand { input with cursor := input.cursor + operator.value.tokenCount } with
          | invariant error => simp [childResult] at result
          | reject failure rejected => simp [childResult] at result
          | ok right next =>
              simp only [childResult] at result
              have childFrame := operandSuccess childResult
              exact (ih (binaryNode left operator right) result).trans childFrame

theorem leftAssociative_endIndex_onSuccess
    (operand : Parser Expr)
    (operandSuccess : ∀ {input output value}, operand input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (precedence : Nat) {input output : State} {value : Expr}
    (result : leftAssociative operand precedence input = .ok value output) :
    output.window.endIndex = input.window.endIndex := by
  unfold leftAssociative at result
  cases firstResult : operand input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok left next =>
      simp only [firstResult] at result
      exact (leftAssociativeTail_endIndex_onSuccess operand operandSuccess precedence
        (next.remainingCount + 1) left result).trans (operandSuccess firstResult)

theorem leftAssociativeTail_preservesEndIndex
    (operand : Parser Expr) (operandFrame : Parser.PreservesEndIndex operand)
    (precedence : Nat) : ∀ fuel left,
      Parser.PreservesEndIndex (leftAssociativeTail operand precedence fuel left) := by
  intro fuel
  induction fuel with
  | zero => intro left input; trivial
  | succ fuel ih =>
      intro left input
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => simp only [leftAssociativeTail, operatorResult, Reply.PreservesEndIndex]
      | some operator =>
          simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape]
          cases childResult : operand { input with cursor := input.cursor + operator.value.tokenCount } with
          | invariant error => trivial
          | reject failure rejected =>
              have childFrame := operandFrame.endIndex_eq_of_reject childResult
              exact childFrame
          | ok right next =>
              have childFrame := operandFrame.endIndex_eq_of_ok childResult
              exact (ih (binaryNode left operator right) next).trans childFrame

theorem leftAssociative_preservesEndIndex
    (operand : Parser Expr) (operandFrame : Parser.PreservesEndIndex operand) (precedence : Nat) :
    Parser.PreservesEndIndex (leftAssociative operand precedence) := by
  intro input
  unfold leftAssociative
  cases firstResult : operand input with
  | invariant error => trivial
  | reject failure rejected => exact operandFrame.endIndex_eq_of_reject firstResult
  | ok left next =>
      exact (leftAssociativeTail_preservesEndIndex operand operandFrame precedence
        (next.remainingCount + 1) left next).trans (operandFrame.endIndex_eq_of_ok firstResult)

/-- The recognized operator pays one unit before the operand is run. Child
successes cannot increase the numeric remainder, even on malformed States. -/
theorem leftAssociativeTail_ordinary_of_unrestrictedFuels
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : UnrestrictedFuelElementContract operand operandFuel) :
    ∀ loopFuel left input, input.remainingCount < loopFuel →
      input.remainingCount < operandFuel + 1 →
      (∃ value output, leftAssociativeTail operand precedence loopFuel left input = .ok value output) ∨
      (∃ failure rejected, leftAssociativeTail operand precedence loopFuel left input = .reject failure rejected) := by
  intro loopFuel
  induction loopFuel with
  | zero => intro left input loopAdequate operandAdequate; omega
  | succ loopFuel ih =>
      intro left input loopAdequate operandAdequate
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => exact Or.inl ⟨left, input, by simp only [leftAssociativeTail, operatorResult]⟩
      | some operator =>
          rcases binaryAtPrecedence?_some_state_shape operatorResult with
            ⟨token, found, _, _, operatorBound⟩
          have beforeEnd := State.cursor_lt_endIndex_of_peek?_eq_some found
          have operatorPositive := BinaryOp.tokenCount_pos operator.value
          let afterOperator := { input with cursor := input.cursor + operator.value.tokenCount }
          have childAdequate : afterOperator.remainingCount < operandFuel := by
            simp only [afterOperator, State.remainingCount] at operandAdequate ⊢
            omega
          have afterOperatorLoop : afterOperator.remainingCount < loopFuel := by
            simp only [afterOperator, State.remainingCount] at loopAdequate ⊢
            omega
          rcases contract.ordinary afterOperator childAdequate with
            ⟨right, next, childResult⟩ | ⟨failure, rejected, childResult⟩
          · dsimp only [afterOperator] at childResult
            have nextLoop := contract.remainingCount_lt_of_success childResult afterOperatorLoop
            have nextChild := contract.remainingCount_lt_of_success childResult childAdequate
            rcases ih (binaryNode left operator right) next nextLoop (by omega) with
              ⟨value, output, tailResult⟩ | ⟨failure, rejected, tailResult⟩
            · exact Or.inl ⟨value, output, by
                simpa only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape,
                  childResult] using tailResult⟩
            · exact Or.inr ⟨failure, rejected, by
                simpa only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape,
                  childResult] using tailResult⟩
          · dsimp only [afterOperator] at childResult
            exact Or.inr ⟨failure, rejected, by
              simp only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape, childResult]⟩

theorem leftAssociativeTail_ne_invariant_of_unrestrictedFuels
    (operand : Parser Expr) (operandFuel precedence loopFuel : Nat)
    (contract : UnrestrictedFuelElementContract operand operandFuel)
    (left : Expr) (input : State) (loopAdequate : input.remainingCount < loopFuel)
    (operandAdequate : input.remainingCount < operandFuel + 1) (error : ParserInvariantError) :
    leftAssociativeTail operand precedence loopFuel left input ≠ .invariant error := by
  intro failed
  rcases leftAssociativeTail_ordinary_of_unrestrictedFuels operand operandFuel precedence contract
      loopFuel left input loopAdequate operandAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

theorem leftAssociative_ordinary_of_unrestrictedElementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : UnrestrictedFuelElementContract operand operandFuel)
    (input : State) (adequate : input.remainingCount < operandFuel) :
    (∃ value output, leftAssociative operand precedence input = .ok value output) ∨
    (∃ failure rejected, leftAssociative operand precedence input = .reject failure rejected) := by
  rcases contract.ordinary input adequate with
    ⟨left, next, firstResult⟩ | ⟨failure, rejected, firstResult⟩
  · have nextAdequate := contract.remainingCount_lt_of_success firstResult adequate
    rcases leftAssociativeTail_ordinary_of_unrestrictedFuels operand operandFuel precedence contract
        (next.remainingCount + 1) left next (by omega) (by omega) with
      ⟨value, output, tailResult⟩ | ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨value, output, by simpa only [leftAssociative, firstResult] using tailResult⟩
    · exact Or.inr ⟨failure, rejected, by simpa only [leftAssociative, firstResult] using tailResult⟩
  · exact Or.inr ⟨failure, rejected, by simp only [leftAssociative, firstResult]⟩

theorem leftAssociative_ne_invariant_of_unrestrictedElementFuel
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : UnrestrictedFuelElementContract operand operandFuel)
    (input : State) (adequate : input.remainingCount < operandFuel) (error : ParserInvariantError) :
    leftAssociative operand precedence input ≠ .invariant error := by
  intro failed
  rcases leftAssociative_ordinary_of_unrestrictedElementFuel operand operandFuel precedence
      contract input adequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

/-- Whole-layer success laws remain unrestricted; only ordinary execution
inherits the first operand's same-fuel input bound. -/
theorem leftAssociative_unrestrictedElementContract
    (operand : Parser Expr) (operandFuel precedence : Nat)
    (contract : UnrestrictedFuelElementContract operand operandFuel) :
    UnrestrictedFuelElementContract (leftAssociative operand precedence) operandFuel where
  endIndexOnSuccess := leftAssociative_endIndex_onSuccess operand contract.endIndexOnSuccess precedence
  cursorLtOnSuccess := leftAssociative_cursor_lt_onSuccess operand contract.cursorLtOnSuccess precedence
  ordinary := leftAssociative_ordinary_of_unrestrictedElementFuel operand operandFuel precedence contract

end Solcore.Syntax.Parser.ExpressionInternals
end
