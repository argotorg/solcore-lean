import Solcore.Syntax.Parser.DelimitedUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Expression.Atom

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
