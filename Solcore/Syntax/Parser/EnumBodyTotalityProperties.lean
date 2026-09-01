import Solcore.Syntax.Parser.EnumElementTotalityProperties

/-! Valid-input totality for canonical enum-body iteration. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

private theorem closeEnumBody_ordinary (opening : Token)
    (constructorsRev : List EnumConstructor) :
    Parser.Ordinary (closeEnumBody opening constructorsRev) := by
  intro input
  rcases (symbol_ordinary .rightBrace .topItem) input with
    ⟨closing, next, closingResult⟩ |
    ⟨failure, rejected, closingResult⟩
  · exact Or.inl ⟨{
        span := SourceSpan.cover opening.span closing.span
        constructors := constructorsRev.reverse
      }, next, by
        simp only [closeEnumBody, bind, closingResult, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [closeEnumBody, bind, closingResult]⟩

/-- Strict constructor progress makes the explicit loop fuel sufficient. -/
theorem enumConstructors_ordinary :
    ∀ opening fuel constructorsRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ body next,
        enumConstructors opening fuel constructorsRev input = .ok body next) ∨
      (∃ failure next,
        enumConstructors opening fuel constructorsRev input =
          .reject failure next) := by
  intro opening fuel
  induction fuel with
  | zero => intros; omega
  | succ fuel inductionHypothesis =>
      intro constructorsRev input inputValid adequate
      unfold enumConstructors
      by_cases commaPresent : isSymbol input .comma
      · simp only [commaPresent, if_true]
        rcases (symbol_ordinary .comma .topItem) input with
          ⟨comma, afterComma, commaResult⟩ |
          ⟨failure, rejected, commaResult⟩
        · have commaReply := symbol_validFor .comma .topItem input inputValid
          rw [commaResult] at commaReply
          have commaWindow := symbol_preservesTokenWindow .comma .topItem input
          rw [commaResult] at commaWindow
          have commaProgress := acceptToken_cursor_lt_onSuccess
            (.symbol .comma) .topItem (· == .symbol .comma) commaResult
          have afterCommaAdequate : afterComma.remainingCount < fuel :=
            remainingCount_lt_after_strict_progress commaReply.2.1
              commaWindow.2 commaProgress adequate
          by_cases closes : isSymbol afterComma .rightBrace
          · simpa only [commaResult, closes, if_true] using
              closeEnumBody_ordinary opening constructorsRev afterComma
          · rcases enumConstructor_ordinary afterComma commaReply.2.1 with
              ⟨constructor, next, constructorResult⟩ |
              ⟨failure, rejected, constructorResult⟩
            · have constructorReply :=
                enumConstructor_elementTotalityContract.validFor
                  afterComma commaReply.2.1
              rw [constructorResult] at constructorReply
              have constructorWindow :=
                enumConstructor_elementTotalityContract.preservesTokenWindow
                  afterComma
              rw [constructorResult] at constructorWindow
              have progress :=
                enumConstructor_elementTotalityContract.cursorLtOnSuccess
                  constructorResult
              have nextAdequate : next.remainingCount < fuel :=
                remainingCount_lt_of_cursor_le constructorWindow.2
                  (Nat.le_of_lt progress) afterCommaAdequate
              simpa only [commaResult, closes, Bool.false_eq_true, if_false,
                constructorResult, if_pos progress] using
                  inductionHypothesis (constructor :: constructorsRev) next
                    constructorReply.2.1 nextAdequate
            · exact Or.inr ⟨failure, rejected, by
                simp only [commaResult, closes, Bool.false_eq_true, if_false,
                  constructorResult]⟩
        · exact Or.inr ⟨failure, rejected, by simp only [commaResult]⟩
      · simp only [commaPresent, Bool.false_eq_true, if_false]
        exact closeEnumBody_ordinary opening constructorsRev input

theorem enumConstructors_ne_invariant
    (opening : Token) (fuel : Nat)
    (constructorsRev : List EnumConstructor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    enumConstructors opening fuel constructorsRev input ≠ .invariant error := by
  intro failed
  rcases enumConstructors_ordinary opening fuel constructorsRev input
      inputValid adequate with
    ⟨body, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Production enum-body fuel always yields an ordinary result. -/
theorem enumBody_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ body next, enumBody input = .ok body next) ∨
      (∃ failure next, enumBody input = .reject failure next) := by
  rcases (symbol_ordinary .leftBrace .topItem) input with
    ⟨opening, afterOpening, openingResult⟩ |
    ⟨failure, rejected, openingResult⟩
  · have openingReply := symbol_validFor .leftBrace .topItem input inputValid
    rw [openingResult] at openingReply
    by_cases empty : isSymbol afterOpening .rightBrace
    · simpa only [enumBody, openingResult, empty, if_true] using
        closeEnumBody_ordinary opening [] afterOpening
    · rcases enumConstructor_ordinary afterOpening openingReply.2.1 with
        ⟨constructor, afterFirst, constructorResult⟩ |
        ⟨failure, rejected, constructorResult⟩
      · have constructorReply :=
          enumConstructor_elementTotalityContract.validFor afterOpening
            openingReply.2.1
        rw [constructorResult] at constructorReply
        simpa only [enumBody, openingResult, empty, Bool.false_eq_true,
          if_false, constructorResult] using
            enumConstructors_ordinary opening
              (afterFirst.remainingCount + 1) [constructor] afterFirst
                constructorReply.2.1 (by omega)
      · exact Or.inr ⟨failure, rejected, by
          simp only [enumBody, openingResult, empty, Bool.false_eq_true,
            if_false, constructorResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [enumBody, openingResult]⟩

theorem enumBody_invariantFreeOnValid :
    Parser.InvariantFreeOnValid enumBody :=
  enumBody_ordinary

theorem enumBody_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    enumBody input ≠ .invariant error :=
  enumBody_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser.EnumInternals
