import Solcore.Syntax.DeclarativeEnumBodyOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.EnumBodyOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.EnumConstructorOrdinaryOutcomeSoundnessProperties

/-! Exact ordinary-rejection bridge for the custom enum-body loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

private theorem closeEnumBody_reject_sound (opening : Token)
    (constructorsRev : List EnumConstructor)
    {input rejected : State} {failure : Failure}
    (result : closeEnumBody opening constructorsRev input =
      .reject failure rejected) :
    rejected = input ∧
      DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.symbol .rightBrace) := by
  unfold closeEnumBody at result
  cases closingResult : symbol .rightBrace .topItem input with
  | invariant error => simp [bind, closingResult] at result
  | ok closing output => simp [bind, closingResult, pure] at result
  | reject closingFailure closingRejected =>
      simp only [bind, closingResult] at result
      cases result
      exact ⟨symbol_reject_state_eq .rightBrace .topItem closingResult,
        symbol_reject_tokenKindAbsentAt .rightBrace .topItem closingResult⟩

private theorem enumConstructors_reject_ordinaryOutcome_sound
    (opening : Token) :
    ∀ fuel constructorsRev input rejected failure,
      enumConstructors opening fuel constructorsRev input =
        .reject failure rejected →
      DeclarativeGrammar.DelimitedTailRejects .rightBrace true
        DeclarativeGrammar.EnumConstructorOrdinaryParses
        DeclarativeGrammar.EnumConstructorRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro constructorsRev input rejected failure result
      simp [enumConstructors] at result
  | succ fuel inductionHypothesis =>
      intro constructorsRev input rejected failure result
      unfold enumConstructors at result
      by_cases commaPresent : isSymbol input .comma = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .comma .topItem commaPresent
          with ⟨comma, commaResult⟩
        simp only [commaPresent, if_true, commaResult] at result
        by_cases closingPresent :
            isSymbol { input with cursor := input.cursor + 1 }
              .rightBrace = true
        · rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .topItem
              closingPresent with ⟨closing, closingResult⟩
          simp only [closingPresent, if_true] at result
          unfold closeEnumBody at result
          simp [bind, closingResult, pure] at result
        · have closingAbsent :
              isSymbol { input with cursor := input.cursor + 1 }
                .rightBrace = false :=
            Bool.eq_false_iff.mpr closingPresent
          simp only [closingAbsent, Bool.false_eq_true, if_false] at result
          cases constructorResult : enumConstructor
              { input with cursor := input.cursor + 1 } with
          | invariant error => simp [constructorResult] at result
          | reject constructorFailure constructorRejected =>
              simp only [constructorResult] at result
              cases result
              exact .elementRejected comma.span
                (symbol_ok_tokenAt .comma .topItem commaResult).1
                (by
                  exact .absent
                    (by
                      simpa [State.declarativeRemainder] using
                        symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingAbsent))
                (by
                  simpa [State.declarativeRemainder] using
                    enumConstructor_reject_ordinaryOutcome_sound
                      constructorResult)
          | ok constructor afterConstructor =>
              simp only [constructorResult] at result
              by_cases progress :
                  afterConstructor.cursor > input.cursor + 1
              · simp only [progress, if_true] at result
                exact .laterRejected comma.span
                  (symbol_ok_tokenAt .comma .topItem commaResult).1
                  (by
                    exact .absent
                      (by
                        simpa [State.declarativeRemainder] using
                          symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                            closingAbsent))
                  (by
                    simpa [State.declarativeRemainder] using
                      enumConstructor_success_ordinaryOutcome_sound
                        constructorResult)
                  (by
                    simpa [State.declarativeRemainder] using
                      progress)
                  (inductionHypothesis (constructor :: constructorsRev)
                    afterConstructor rejected failure result)
              · simp [progress] at result
      · have commaAbsent : isSymbol input .comma = false :=
          Bool.eq_false_iff.mpr commaPresent
        simp only [commaAbsent, Bool.false_eq_true, if_false] at result
        rcases closeEnumBody_reject_sound opening constructorsRev result with
          ⟨rejectedEq, closingAbsent⟩
        subst rejected
        exact .delimiterMissing
          (symbolAbsentAt_of_isSymbol_eq_false .comma commaAbsent)
          closingAbsent

/-- Every enum-body rejection follows the generic allow-empty,
allow-trailing rejection relation at the exact retained remainder. -/
theorem enumBody_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : enumBody input = .reject failure rejected) :
    DeclarativeGrammar.EnumBodyRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold enumBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      simp only [openingResult] at result
      cases result
      have rejectedEq := symbol_reject_state_eq .leftBrace .topItem
        openingResult
      subst rejected
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftBrace .topItem openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingSound := symbol_ok_tokenAt .leftBrace .topItem openingResult
      by_cases closingPresent : isSymbol afterOpening .rightBrace = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .topItem
            closingPresent with ⟨closing, closingResult⟩
        simp only [closingPresent, if_true] at result
        unfold closeEnumBody at result
        simp [bind, closingResult, pure] at result
      · have closingAbsent : isSymbol afterOpening .rightBrace = false :=
          Bool.eq_false_iff.mpr closingPresent
        simp only [closingAbsent, Bool.false_eq_true, if_false] at result
        have continues : DeclarativeGrammar.PreferredCloseNotTaken
            .rightBrace true {
              input.declarativeRemainder with cursor := input.cursor + 1
            } := by
          exact .absent (by
            simpa only [openingSound.2, State.declarativeRemainder,
              State.tokens, State.window, State.cursor] using
                symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingAbsent)
        cases firstResult : enumConstructor afterOpening with
        | invariant error => simp [firstResult] at result
        | reject firstFailure firstRejected =>
            simp only [firstResult] at result
            cases result
            exact .firstRejected opening.span openingSound.1 continues
              (by
                simpa only [openingSound.2, State.declarativeRemainder,
                  State.tokens, State.window, State.cursor] using
                    enumConstructor_reject_ordinaryOutcome_sound firstResult)
        | ok first afterFirst =>
            simp only [firstResult] at result
            exact .tailRejected opening.span openingSound.1 continues
              (by
                simpa only [openingSound.2, State.declarativeRemainder,
                  State.tokens, State.window, State.cursor] using
                    enumConstructor_success_ordinaryOutcome_sound firstResult)
              (by
                have progress := enumConstructor_cursor_lt_onSuccess
                  firstResult
                simpa only [openingSound.2, State.declarativeRemainder,
                  State.cursor] using progress)
              (enumConstructors_reject_ordinaryOutcome_sound opening
                (afterFirst.remainingCount + 1) [first] afterFirst rejected
                  failure result)

end Solcore.Syntax.Parser.EnumInternals
