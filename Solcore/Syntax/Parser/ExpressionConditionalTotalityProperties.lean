import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.ExpressionProperties

/-! Fuel-aware totality for conditional-expression parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

theorem conditionalTail_ordinary_of_fuels
    (nested alternative : Parser Expr)
    (nestedFuel alternativeFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (alternativeContract :
      FuelElementTotalityContract alternative alternativeFuel) :
    ∀ loopFuel headsRev condition input,
      input.ValidFor →
      input.remainingCount < loopFuel →
      input.remainingCount < nestedFuel + 1 →
      input.remainingCount < alternativeFuel →
      (∃ expression next,
        conditionalTail nested alternative loopFuel headsRev condition input =
          .ok expression next) ∨
      (∃ failure next,
        conditionalTail nested alternative loopFuel headsRev condition input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro headsRev condition input inputValid loopAdequate
        nestedAdequate alternativeAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro headsRev condition input inputValid loopAdequate
        nestedAdequate alternativeAdequate
      by_cases questionPresent : isSymbol input .question
      · rcases (symbol_ordinary .question .expression) input with
          ⟨question, afterQuestion, questionResult⟩ |
          ⟨failure, rejected, questionResult⟩
        · have questionValid := symbol_validFor .question .expression
            input inputValid
          rw [questionResult] at questionValid
          have questionWindow := symbol_preservesTokenWindow
            .question .expression input
          rw [questionResult] at questionWindow
          have questionProgress : input.cursor < afterQuestion.cursor :=
            acceptToken_cursor_lt_onSuccess (.symbol .question) .expression
              (· == .symbol .question) questionResult
          have afterQuestionNestedAdequate :
              afterQuestion.remainingCount < nestedFuel :=
            remainingCount_lt_after_strict_progress questionValid.2.1
              questionWindow.2 questionProgress nestedAdequate
          rcases nestedContract.ordinary afterQuestion questionValid.2.1
              afterQuestionNestedAdequate with
            ⟨thenBranch, afterThen, thenResult⟩ |
            ⟨failure, rejected, thenResult⟩
          · have thenValid := nestedContract.validFor afterQuestion
                questionValid.2.1
            rw [thenResult] at thenValid
            have thenWindow := nestedContract.preservesTokenWindow
              afterQuestion
            rw [thenResult] at thenWindow
            have thenProgress := nestedContract.cursorLtOnSuccess thenResult
            rcases (symbol_ordinary .colon .expression) afterThen with
              ⟨colon, afterColon, colonResult⟩ |
              ⟨failure, rejected, colonResult⟩
            · have colonValid := symbol_validFor .colon .expression
                  afterThen thenValid.2.1
              rw [colonResult] at colonValid
              have colonWindow := symbol_preservesTokenWindow
                .colon .expression afterThen
              rw [colonResult] at colonWindow
              have colonProgress : afterThen.cursor < afterColon.cursor :=
                acceptToken_cursor_lt_onSuccess (.symbol .colon) .expression
                  (· == .symbol .colon) colonResult
              have afterColonWindow : afterColon.window = input.window :=
                colonWindow.2.trans
                  (thenWindow.2.trans questionWindow.2)
              have inputBeforeColon : input.cursor ≤ afterColon.cursor :=
                Nat.le_of_lt (Nat.lt_trans questionProgress
                  (Nat.lt_trans thenProgress colonProgress))
              have afterColonAlternativeAdequate :
                  afterColon.remainingCount < alternativeFuel :=
                remainingCount_lt_of_cursor_le afterColonWindow
                  inputBeforeColon alternativeAdequate
              rcases alternativeContract.ordinary afterColon colonValid.2.1
                  afterColonAlternativeAdequate with
                ⟨nextCondition, next, alternativeResult⟩ |
                ⟨failure, rejected, alternativeResult⟩
              · have alternativeValid := alternativeContract.validFor
                    afterColon colonValid.2.1
                rw [alternativeResult] at alternativeValid
                have alternativeWindow :=
                  alternativeContract.preservesTokenWindow afterColon
                rw [alternativeResult] at alternativeWindow
                have alternativeProgress :=
                  alternativeContract.cursorLtOnSuccess alternativeResult
                have nextWindow : next.window = input.window :=
                  alternativeWindow.2.trans afterColonWindow
                have inputProgress : input.cursor < next.cursor :=
                  Nat.lt_trans questionProgress
                    (Nat.lt_trans thenProgress
                      (Nat.lt_trans colonProgress alternativeProgress))
                have nextLoopAdequate :
                    next.remainingCount < loopFuel :=
                  remainingCount_lt_after_strict_progress
                    alternativeValid.2.1 nextWindow inputProgress
                    loopAdequate
                have nextNestedAdequate :
                    next.remainingCount < nestedFuel + 1 :=
                  remainingCount_lt_of_cursor_le nextWindow
                    (Nat.le_of_lt inputProgress) nestedAdequate
                have nextAlternativeAdequate :
                    next.remainingCount < alternativeFuel :=
                  remainingCount_lt_of_cursor_le nextWindow
                    (Nat.le_of_lt inputProgress) alternativeAdequate
                rcases inductionHypothesis ({
                      condition
                      question := question.span
                      thenBranch
                      colon := colon.span
                    } :: headsRev) nextCondition next alternativeValid.2.1
                    nextLoopAdequate nextNestedAdequate
                    nextAlternativeAdequate with
                  ⟨expression, final, recursiveResult⟩ |
                  ⟨failure, rejected, recursiveResult⟩
                · exact Or.inl ⟨expression, final, by
                    simp only [conditionalTail, questionPresent, ↓reduceIte,
                      questionResult, thenResult, colonResult,
                      alternativeResult]
                    exact recursiveResult⟩
                · exact Or.inr ⟨failure, rejected, by
                    simp only [conditionalTail, questionPresent, ↓reduceIte,
                      questionResult, thenResult, colonResult,
                      alternativeResult]
                    exact recursiveResult⟩
              · exact Or.inr ⟨failure, rejected, by
                  simp only [conditionalTail, questionPresent, ↓reduceIte,
                    questionResult, thenResult, colonResult,
                    alternativeResult]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [conditionalTail, questionPresent, ↓reduceIte,
                  questionResult, thenResult, colonResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [conditionalTail, questionPresent, ↓reduceIte,
                questionResult, thenResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [conditionalTail, questionPresent, ↓reduceIte,
              questionResult]⟩
      · have questionAbsent : isSymbol input .question = false := by
          cases found : isSymbol input .question with
          | false => rfl
          | true => exact False.elim (questionPresent found)
        exact Or.inl ⟨headsRev.foldl foldConditionalHead condition,
          input, by
            simp only [conditionalTail, questionAbsent, Bool.false_eq_true,
              ↓reduceIte]⟩

theorem conditionalTail_ne_invariant_of_fuels
    (nested alternative : Parser Expr)
    (nestedFuel alternativeFuel loopFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (alternativeContract :
      FuelElementTotalityContract alternative alternativeFuel)
    (headsRev : List ConditionalHead) (condition : Expr)
    (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (alternativeAdequate : input.remainingCount < alternativeFuel)
    (error : ParserInvariantError) :
    conditionalTail nested alternative loopFuel headsRev condition input ≠
      .invariant error := by
  intro failed
  rcases conditionalTail_ordinary_of_fuels nested alternative nestedFuel
      alternativeFuel nestedContract alternativeContract loopFuel headsRev
      condition input inputValid loopAdequate nestedAdequate
      alternativeAdequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem conditional_ordinary_of_elementFuels
    (nested alternative : Parser Expr)
    (nestedFuel alternativeFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (alternativeContract :
      FuelElementTotalityContract alternative alternativeFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (alternativeAdequate : input.remainingCount < alternativeFuel) :
    (∃ expression next,
      conditional nested alternative input = .ok expression next) ∨
    (∃ failure next,
      conditional nested alternative input = .reject failure next) := by
  rcases alternativeContract.ordinary input inputValid
      alternativeAdequate with
    ⟨condition, next, alternativeResult⟩ |
    ⟨failure, rejected, alternativeResult⟩
  · have conditionValid := alternativeContract.validFor input inputValid
    rw [alternativeResult] at conditionValid
    have conditionWindow := alternativeContract.preservesTokenWindow input
    rw [alternativeResult] at conditionWindow
    have conditionProgress :=
      alternativeContract.cursorLtOnSuccess alternativeResult
    have nextNestedAdequate : next.remainingCount < nestedFuel + 1 :=
      remainingCount_lt_of_cursor_le conditionWindow.2
        (Nat.le_of_lt conditionProgress) nestedAdequate
    have nextAlternativeAdequate :
        next.remainingCount < alternativeFuel :=
      remainingCount_lt_of_cursor_le conditionWindow.2
        (Nat.le_of_lt conditionProgress) alternativeAdequate
    rcases conditionalTail_ordinary_of_fuels nested alternative nestedFuel
        alternativeFuel nestedContract alternativeContract
        (next.remainingCount + 1) [] condition next conditionValid.2.1
        (by omega) nextNestedAdequate nextAlternativeAdequate with
      ⟨expression, final, tailResult⟩ |
      ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨expression, final, by
        simp only [conditional, alternativeResult]
        exact tailResult⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [conditional, alternativeResult]
        exact tailResult⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [conditional, alternativeResult]⟩

theorem conditional_ne_invariant_of_elementFuels
    (nested alternative : Parser Expr)
    (nestedFuel alternativeFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (alternativeContract :
      FuelElementTotalityContract alternative alternativeFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (alternativeAdequate : input.remainingCount < alternativeFuel)
    (error : ParserInvariantError) :
    conditional nested alternative input ≠ .invariant error := by
  intro failed
  rcases conditional_ordinary_of_elementFuels nested alternative nestedFuel
      alternativeFuel nestedContract alternativeContract input inputValid
      nestedAdequate alternativeAdequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionInternals
