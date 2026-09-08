import Solcore.Syntax.Parser.UnrestrictedFuelElementContract
import Solcore.Syntax.Parser.Expression.Atom

/-! Parenthesized atoms and their actual tuple loop are ordinary on arbitrary
States. A real opening/comma token pays one fuel unit; successful children
preserve only endIndex and strict cursor progress. No other child frame is used. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem closeTuple_ordinary_unrestricted (opening : Token) (elementsRev : List Expr) :
    Parser.Ordinary (closeTuple opening elementsRev) := by
  intro input
  rcases symbol_ordinary .rightParen .expression input with
    ⟨closing, next, result⟩ | ⟨failure, rejected, result⟩
  · simp only [closeTuple, bind, result]
    split <;> exact .inl ⟨_, next, rfl⟩
  · exact .inr ⟨failure, rejected, by simp only [closeTuple, bind, result]⟩

theorem closeTuple_ne_invariant_unrestricted (opening : Token) (elementsRev : List Expr)
    (input : State) (error : ParserInvariantError) : closeTuple opening elementsRev input ≠ .invariant error :=
  (closeTuple_ordinary_unrestricted opening elementsRev).ne_invariant input error

theorem tupleTail_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel) (opening : Token) :
    ∀ loopFuel elementsRev input,
      input.remainingCount < loopFuel → input.remainingCount < nestedFuel + 1 →
      (∃ value next, tupleTail nested opening loopFuel elementsRev input = .ok value next) ∨
      (∃ failure next, tupleTail nested opening loopFuel elementsRev input = .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero => intro elementsRev input loopAdequate nestedAdequate; omega
  | succ loopFuel ih =>
      intro elementsRev input loopAdequate nestedAdequate
      unfold tupleTail
      cases commaResult : symbol .comma .expression input with
      | invariant error => exact False.elim (symbol_ne_invariant .comma .expression input error commaResult)
      | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
      | ok comma afterComma =>
          have commaLoopAdequate := symbol_remainingCount_lt_of_success .comma .expression commaResult loopAdequate
          have commaNestedAdequate := symbol_remainingCount_lt_of_success .comma .expression commaResult nestedAdequate
          simp only
          split
          · exact closeTuple_ordinary_unrestricted opening elementsRev afterComma
          · cases childResult : nested afterComma with
            | invariant error => exact False.elim (contract.ne_invariant afterComma commaNestedAdequate error childResult)
            | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
            | ok value next =>
                have progress := contract.cursorLtOnSuccess childResult
                have nextNestedAdequate := contract.remainingCount_lt_of_success childResult commaNestedAdequate
                dsimp only
                split
                · split
                  · exact ih (value :: elementsRev) next
                      (contract.remainingCount_lt_of_success childResult commaLoopAdequate) (by omega)
                  · exact closeTuple_ordinary_unrestricted opening (value :: elementsRev) next
                · omega

theorem tupleTail_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (opening : Token) (loopFuel : Nat) (elementsRev : List Expr) (input : State)
    (loopAdequate : input.remainingCount < loopFuel) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    tupleTail nested opening loopFuel elementsRev input ≠ .invariant error := by
  intro failed
  rcases tupleTail_ordinary_of_unrestrictedElementFuel nested nestedFuel contract opening
    loopFuel elementsRev input loopAdequate nestedAdequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

theorem tupleTail_production_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (opening : Token) (elementsRev : List Expr) (input : State)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, tupleTail nested opening (input.remainingCount + 1) elementsRev input = .ok value next) ∨
    (∃ failure next, tupleTail nested opening (input.remainingCount + 1) elementsRev input = .reject failure next) :=
  tupleTail_ordinary_of_unrestrictedElementFuel nested nestedFuel contract opening
    (input.remainingCount + 1) elementsRev input (Nat.lt_succ_self _) adequate

theorem tupleTail_production_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (opening : Token) (elementsRev : List Expr) (input : State)
    (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    tupleTail nested opening (input.remainingCount + 1) elementsRev input ≠ .invariant error :=
  tupleTail_ne_invariant_of_unrestrictedElementFuel nested nestedFuel contract opening
    (input.remainingCount + 1) elementsRev input (Nat.lt_succ_self _) adequate error

theorem parenthesized_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, parenthesized nested input = .ok value next) ∨
    (∃ failure next, parenthesized nested input = .reject failure next) := by
  unfold parenthesized
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => exact False.elim (symbol_ne_invariant .leftParen .expression input error openingResult)
  | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
  | ok opening afterOpening =>
      have afterOpeningAdequate := symbol_remainingCount_lt_of_success .leftParen .expression openingResult adequate
      simp only
      split
      · exact closeTuple_ordinary_unrestricted opening [] afterOpening
      · cases childResult : nested afterOpening with
        | invariant error => exact False.elim (contract.ne_invariant afterOpening afterOpeningAdequate error childResult)
        | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
        | ok first next =>
            have progress := contract.cursorLtOnSuccess childResult
            have nextAdequate := contract.remainingCount_lt_of_success childResult afterOpeningAdequate
            dsimp only
            split
            · omega
            · split
              · exact tupleTail_production_ordinary_of_unrestrictedElementFuel nested nestedFuel contract
                  opening [first] next (by omega)
              · exact closeTuple_ordinary_unrestricted opening [first] next

theorem parenthesized_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    parenthesized nested input ≠ .invariant error := by
  intro failed
  rcases parenthesized_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
