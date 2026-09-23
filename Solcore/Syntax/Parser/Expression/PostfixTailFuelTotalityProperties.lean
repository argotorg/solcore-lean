import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Fuel-aware totality for the postfix-expression tail loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem postfixTail_ordinary_of_fuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel) :
    ∀ loopFuel base input, input.ValidFor →
      input.remainingCount < loopFuel →
      input.remainingCount < nestedFuel + 1 →
      (∃ value next,
        postfixTail nested block loopFuel base input = .ok value next) ∨
      (∃ failure next,
        postfixTail nested block loopFuel base input = .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro base input inputValid loopAdequate nestedAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro base input inputValid loopAdequate nestedAdequate
      unfold postfixTail
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true]
        rcases (symbol_ordinary .leftBracket .expression) input with
          ⟨opening, afterOpening, openingResult⟩ |
          ⟨failure, rejected, openingResult⟩
        · have openingValid := symbol_validFor .leftBracket .expression input
            inputValid
          rw [openingResult] at openingValid
          have openingWindow := symbol_preservesTokenWindow .leftBracket
            .expression input
          rw [openingResult] at openingWindow
          have afterOpeningNested : afterOpening.remainingCount < nestedFuel :=
            remainingCount_lt_after_strict_progress openingValid.2.1
              openingWindow.2
              (acceptToken_cursor_lt_onSuccess (.symbol .leftBracket)
                .expression (· == .symbol .leftBracket) openingResult)
              nestedAdequate
          rcases contract.ordinary afterOpening openingValid.2.1
              afterOpeningNested with
            ⟨index, afterIndex, indexResult⟩ |
            ⟨failure, rejected, indexResult⟩
          · have indexValid := contract.validFor afterOpening openingValid.2.1
            rw [indexResult] at indexValid
            rcases (symbol_ordinary .rightBracket .expression) afterIndex with
              ⟨closing, afterClosing, closingResult⟩ |
              ⟨failure, rejected, closingResult⟩
            · have closingValid := symbol_validFor .rightBracket .expression
                afterIndex indexValid.2.1
              rw [closingResult] at closingValid
              have suffixWindow :=
                (symbol_preservesTokenWindow .rightBracket .expression
                  afterIndex)
              rw [closingResult] at suffixWindow
              have indexWindow := contract.preservesTokenWindow afterOpening
              rw [indexResult] at indexWindow
              have afterClosingWindow : afterClosing.window = input.window :=
                suffixWindow.2.trans (indexWindow.2.trans openingWindow.2)
              have loopNext : afterClosing.remainingCount < loopFuel :=
                remainingCount_lt_after_strict_progress closingValid.2.1
                  afterClosingWindow
                  (Nat.lt_of_lt_of_le
                    (acceptToken_cursor_lt_onSuccess (.symbol .leftBracket)
                      .expression (· == .symbol .leftBracket) openingResult)
                    (Nat.le_trans (Nat.le_of_lt
                      (contract.cursorLtOnSuccess indexResult))
                      (symbol_cursorMonotoneOnSuccess .rightBracket .expression
                        afterIndex closing afterClosing closingResult)))
                  loopAdequate
              have nestedNext : afterClosing.remainingCount < nestedFuel + 1 :=
                remainingCount_lt_of_cursor_le afterClosingWindow
                  (Nat.le_trans
                    (symbol_cursorMonotoneOnSuccess .leftBracket .expression
                      input opening afterOpening openingResult)
                    (Nat.le_trans (Nat.le_of_lt
                      (contract.cursorLtOnSuccess indexResult))
                      (symbol_cursorMonotoneOnSuccess .rightBracket .expression
                        afterIndex closing afterClosing closingResult)))
                  nestedAdequate
              rcases inductionHypothesis {
                    span := SourceSpan.cover base.span closing.span
                    value := .index base
                      (SourceSpan.cover opening.span closing.span) index
                  } afterClosing closingValid.2.1 loopNext nestedNext with
                ⟨value, final, tailResult⟩ |
                ⟨failure, final, tailResult⟩
              · exact Or.inl ⟨value, final, by
                  simp only [openingResult, indexResult, closingResult,
                    tailResult]⟩
              · exact Or.inr ⟨failure, final, by
                  simp only [openingResult, indexResult, closingResult,
                    tailResult]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [openingResult, indexResult, closingResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [openingResult, indexResult]⟩
        · exact Or.inr ⟨failure, rejected, by simp only [openingResult]⟩
      · simp only [indexed, Bool.false_eq_true, if_false]
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true]
          rcases delimitedWithPolicy_ordinary_of_elementFuel .leftParen
              .rightParen true false nested .expression .expression nestedFuel
              contract input inputValid nestedAdequate with
            ⟨arguments, next, argumentsResult⟩ |
            ⟨failure, rejected, argumentsResult⟩
          · have ordinaryResult : delimitedNoTrailing .leftParen .rightParen
                true nested .expression .expression input = .ok arguments next :=
              by simpa only [delimitedNoTrailing] using argumentsResult
            have argumentsValid := delimitedNoTrailing_validFor (fun _ _ => True)
              .leftParen .rightParen true nested .expression .expression
              contract.validFor
              contract.preservesTokenWindow.preservesTokensOnSuccess input
              inputValid
            rw [ordinaryResult] at argumentsValid
            have argumentsWindow := delimitedWithPolicy_preservesTokenWindow
              .leftParen .rightParen true false nested .expression .expression
              contract.preservesTokenWindow input
            rw [argumentsResult] at argumentsWindow
            have strict := delimitedWithPolicy_cursor_lt_onSuccess .leftParen
              .rightParen true false nested .expression .expression
              argumentsResult
            have loopNext := remainingCount_lt_after_strict_progress
              argumentsValid.2.1 argumentsWindow.2 strict loopAdequate
            have nestedNext := remainingCount_lt_of_cursor_le argumentsWindow.2
              (Nat.le_of_lt strict) nestedAdequate
            rcases inductionHypothesis {
                  span := SourceSpan.cover base.span arguments.span
                  value := .call base arguments
                } next argumentsValid.2.1 loopNext nestedNext with
              ⟨value, final, tailResult⟩ |
              ⟨failure, final, tailResult⟩
            · exact Or.inl ⟨value, final, by
                simp only [ordinaryResult, tailResult]⟩
            · exact Or.inr ⟨failure, final, by
                simp only [ordinaryResult, tailResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [delimitedNoTrailing, argumentsResult]⟩
        · simp only [called, Bool.false_eq_true, if_false]
          by_cases field : isSymbol input .dot
          · simp only [field, if_true]
            rcases (symbol_ordinary .dot .expression) input with
              ⟨dot, afterDot, dotResult⟩ | ⟨failure, rejected, dotResult⟩
            · have dotValid := symbol_validFor .dot .expression input inputValid
              rw [dotResult] at dotValid
              rcases (identifier_ordinary .expression) afterDot with
                ⟨name, next, nameResult⟩ | ⟨failure, rejected, nameResult⟩
              · have nameValid := identifier_validFor .expression afterDot
                    dotValid.2.1
                rw [nameResult] at nameValid
                have dotWindow := symbol_preservesTokenWindow .dot .expression
                  input
                rw [dotResult] at dotWindow
                have nameWindow := identifier_preservesTokenWindow .expression
                  afterDot
                rw [nameResult] at nameWindow
                have nextWindow : next.window = input.window :=
                  nameWindow.2.trans dotWindow.2
                have strict := acceptToken_cursor_lt_onSuccess (.symbol .dot)
                  .expression (· == .symbol .dot) dotResult
                have loopNext := remainingCount_lt_after_strict_progress
                  nameValid.2.1 nextWindow
                    (Nat.lt_of_lt_of_le strict
                      (identifier_cursorMonotoneOnSuccess .expression afterDot
                        name next nameResult)) loopAdequate
                have nestedNext := remainingCount_lt_of_cursor_le nextWindow
                  (Nat.le_trans
                    (symbol_cursorMonotoneOnSuccess .dot .expression input dot
                      afterDot dotResult)
                    (identifier_cursorMonotoneOnSuccess .expression afterDot
                      name next nameResult)) nestedAdequate
                rcases inductionHypothesis {
                      span := SourceSpan.cover base.span name.span
                      value := .field base dot.span name
                    } next nameValid.2.1 loopNext nestedNext with
                  ⟨value, final, tailResult⟩ |
                  ⟨failure, final, tailResult⟩
                · exact Or.inl ⟨value, final, by
                    simp only [dotResult, nameResult, tailResult]⟩
                · exact Or.inr ⟨failure, final, by
                    simp only [dotResult, nameResult, tailResult]⟩
              · exact Or.inr ⟨failure, rejected, by
                  simp only [dotResult, nameResult]⟩
            · exact Or.inr ⟨failure, rejected, by simp only [dotResult]⟩
          · have absent : isSymbol input .dot = false := by
              cases found : isSymbol input .dot with
              | false => rfl
              | true => exact False.elim (field found)
            exact Or.inl ⟨base, input, by
              simp only [absent, Bool.false_eq_true, if_false]⟩

theorem postfixTail_ne_invariant_of_fuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel loopFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (base : Expr) (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    postfixTail nested block loopFuel base input ≠ .invariant error := by
  intro failed
  rcases postfixTail_ordinary_of_fuel nested block nestedFuel contract loopFuel
      base input inputValid loopAdequate nestedAdequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

theorem postfixTail_production_ordinary
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (base : Expr) (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next,
      postfixTail nested block (input.remainingCount + 1) base input =
        .ok value next) ∨
    (∃ failure next,
      postfixTail nested block (input.remainingCount + 1) base input =
        .reject failure next) :=
  postfixTail_ordinary_of_fuel nested block nestedFuel contract
    (input.remainingCount + 1) base input inputValid (by omega) nestedAdequate

end Solcore.Syntax.Parser.ExpressionAtomInternals
