import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.PatternProperties

/-! Fuel-aware totality for grouped patterns and pattern tuples. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Closing a grouped pattern or tuple is invariant-free on valid input. -/
theorem closePatternTuple_invariantFreeOnValid (opening : Token)
    (elementsRev : List Pattern) :
    Parser.InvariantFreeOnValid (closePatternTuple opening elementsRev) := by
  unfold closePatternTuple
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .rightParen .pattern)
    (symbol_ordinary .rightParen .pattern).invariantFreeOnValid
  intro closing
  cases elementsRev with
  | nil => exact Parser.pure_invariantFreeOnValid _
  | cons only tail =>
      cases tail <;> exact Parser.pure_invariantFreeOnValid _

/--
The pattern-tuple tail is ordinary when both its loop fuel and the nested
parser's fixed recursive-fuel bound are adequate.
-/
theorem patternTupleTail_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) :
    ∀ loopFuel elementsRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < nestedFuel + 1 →
      (∃ value next,
        patternTupleTail nested opening loopFuel elementsRev input =
          .ok value next) ∨
      (∃ failure next,
        patternTupleTail nested opening loopFuel elementsRev input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro elementsRev input inputValid loopAdequate nestedAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro elementsRev input inputValid loopAdequate nestedAdequate
      unfold patternTupleTail
      cases commaResult : symbol .comma .pattern input with
      | invariant error =>
          exact False.elim
            (symbol_ne_invariant .comma .pattern input error commaResult)
      | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
      | ok comma afterComma =>
          have commaValid := symbol_validFor .comma .pattern input inputValid
          rw [commaResult] at commaValid
          have commaWindow := symbol_preservesTokenWindow .comma .pattern input
          rw [commaResult] at commaWindow
          have commaProgress : input.cursor < afterComma.cursor :=
            acceptToken_cursor_lt_onSuccess (.symbol .comma) .pattern
              (· == .symbol .comma) commaResult
          have afterCommaNestedAdequate :
              afterComma.remainingCount < nestedFuel :=
            remainingCount_lt_after_strict_progress commaValid.2.1
              commaWindow.2 commaProgress nestedAdequate
          simp only
          split
          · exact closePatternTuple_invariantFreeOnValid opening elementsRev
              afterComma commaValid.2.1
          · cases nestedResult : nested afterComma with
            | invariant error =>
                exact False.elim (contract.ne_invariant afterComma
                  commaValid.2.1 afterCommaNestedAdequate error nestedResult)
            | reject failure rejected =>
                exact Or.inr ⟨failure, rejected, rfl⟩
            | ok value next =>
                have valueValid := contract.validFor afterComma commaValid.2.1
                rw [nestedResult] at valueValid
                have valueWindow := contract.preservesTokenWindow afterComma
                rw [nestedResult] at valueWindow
                have valueProgress := contract.cursorLtOnSuccess nestedResult
                dsimp only
                split
                · omega
                · split
                  · have nextWindow : next.window = input.window :=
                      valueWindow.2.trans commaWindow.2
                    have nextLoopAdequate :
                        next.remainingCount < loopFuel :=
                      remainingCount_lt_after_strict_progress valueValid.2.1
                        nextWindow (Nat.lt_trans commaProgress valueProgress)
                        (by simpa [Nat.succ_eq_add_one] using loopAdequate)
                    have nextNestedAdequate :
                        next.remainingCount < nestedFuel + 1 := by
                      have preserved : next.remainingCount < nestedFuel :=
                        remainingCount_lt_of_cursor_le valueWindow.2
                          (Nat.le_of_lt valueProgress)
                          afterCommaNestedAdequate
                      omega
                    exact inductionHypothesis (value :: elementsRev) next
                      valueValid.2.1 nextLoopAdequate nextNestedAdequate
                  · exact closePatternTuple_invariantFreeOnValid opening
                      (value :: elementsRev) next valueValid.2.1

theorem patternTupleTail_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) (loopFuel : Nat) (elementsRev : List Pattern)
    (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    patternTupleTail nested opening loopFuel elementsRev input ≠
      .invariant error := by
  intro failed
  rcases patternTupleTail_ordinary_of_elementFuel nested nestedFuel contract
      opening loopFuel elementsRev input inputValid loopAdequate
        nestedAdequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- The production pattern-tuple loop fuel is always adequate. -/
theorem patternTupleTail_production_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) (elementsRev : List Pattern)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next,
      patternTupleTail nested opening (input.remainingCount + 1) elementsRev
        input = .ok value next) ∨
    (∃ failure next,
      patternTupleTail nested opening (input.remainingCount + 1) elementsRev
        input = .reject failure next) :=
  patternTupleTail_ordinary_of_elementFuel nested nestedFuel contract opening
    (input.remainingCount + 1) elementsRev input inputValid (by omega)
      nestedAdequate

theorem patternTupleTail_production_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (opening : Token) (elementsRev : List Pattern)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    patternTupleTail nested opening (input.remainingCount + 1) elementsRev
      input ≠ .invariant error :=
  patternTupleTail_ne_invariant_of_elementFuel nested nestedFuel contract
    opening (input.remainingCount + 1) elementsRev input inputValid (by omega)
      nestedAdequate error

/--
Parenthesized-pattern parsing is ordinary with one fuel unit beyond its nested
parser. The opening parenthesis spends that unit before the first nested call.
-/
theorem parenthesizedPattern_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, parenthesizedPattern nested input = .ok value next) ∨
      (∃ failure next,
        parenthesizedPattern nested input = .reject failure next) := by
  unfold parenthesizedPattern
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error =>
      exact False.elim
        (symbol_ne_invariant .leftParen .pattern input error openingResult)
  | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
  | ok opening afterOpening =>
      have openingValid := symbol_validFor .leftParen .pattern input inputValid
      rw [openingResult] at openingValid
      have openingWindow := symbol_preservesTokenWindow .leftParen .pattern input
      rw [openingResult] at openingWindow
      have openingProgress : input.cursor < afterOpening.cursor :=
        acceptToken_cursor_lt_onSuccess (.symbol .leftParen) .pattern
          (· == .symbol .leftParen) openingResult
      have afterOpeningAdequate :
          afterOpening.remainingCount < nestedFuel :=
        remainingCount_lt_after_strict_progress openingValid.2.1
          openingWindow.2 openingProgress adequate
      simp only
      split
      · exact closePatternTuple_invariantFreeOnValid opening [] afterOpening
          openingValid.2.1
      · cases nestedResult : nested afterOpening with
        | invariant error =>
            exact False.elim (contract.ne_invariant afterOpening
              openingValid.2.1 afterOpeningAdequate error nestedResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok first next =>
            have firstValid := contract.validFor afterOpening openingValid.2.1
            rw [nestedResult] at firstValid
            have firstWindow := contract.preservesTokenWindow afterOpening
            rw [nestedResult] at firstWindow
            have firstProgress := contract.cursorLtOnSuccess nestedResult
            dsimp only
            split
            · omega
            · split
              · have nextAdequate :
                    next.remainingCount < nestedFuel + 1 := by
                  have preserved : next.remainingCount < nestedFuel :=
                    remainingCount_lt_of_cursor_le firstWindow.2
                      (Nat.le_of_lt firstProgress) afterOpeningAdequate
                  omega
                exact patternTupleTail_production_ordinary_of_elementFuel
                  nested nestedFuel contract opening [first] next
                    firstValid.2.1 nextAdequate
              · exact closePatternTuple_invariantFreeOnValid opening [first]
                  next firstValid.2.1

theorem parenthesizedPattern_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    parenthesizedPattern nested input ≠ .invariant error := by
  intro failed
  rcases parenthesizedPattern_ordinary_of_elementFuel nested nestedFuel contract
      input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals
