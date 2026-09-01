import Solcore.Syntax.DeclarativeCorePatternParenthesizedOutcomeGrammar
import Solcore.Syntax.Parser.CorePatternParenthesizedOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Exact ordinary-rejection reflection for parenthesized patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem closePatternTuple_reject_ordinary_sound (opening : Token)
    (elementsRev : List Pattern) {input rejected : State}
    {failure : Failure}
    (result : closePatternTuple opening elementsRev input =
      .reject failure rejected) :
    rejected = input ∧
      DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.symbol .rightParen) := by
  unfold closePatternTuple at result
  cases closingResult : symbol .rightParen .pattern input with
  | invariant error => simp [bind, closingResult] at result
  | ok closing afterClosing =>
      simp only [bind, closingResult] at result
      cases elementsRev with
      | nil => simp [pure] at result
      | cons head tail =>
          cases tail with
          | nil => simp [pure] at result
          | cons second rest => simp [pure] at result
  | reject closingFailure closingRejected =>
      simp only [bind, closingResult] at result
      cases result
      exact ⟨symbol_reject_state_eq .rightParen .pattern closingResult,
        symbol_reject_tokenKindAbsentAt .rightParen .pattern closingResult⟩

/-- Every tuple-tail rejection under its positive comma guard is exact. -/
theorem patternTupleTail_reject_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (opening : Token) : ∀ fuel elementsRev input failure rejected,
      isSymbol input .comma = true →
      patternTupleTail nested opening fuel elementsRev input =
        .reject failure rejected →
      DeclarativeGrammar.ParenthesizedPatternTupleTailRejects nestedOrdinary
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input failure rejected commaPresent result
      simp [patternTupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input failure rejected commaPresent result
      unfold patternTupleTail at result
      cases commaResult : symbol .comma .pattern input with
      | invariant error => simp [commaResult] at result
      | reject commaFailure commaRejected =>
          rcases symbol_eq_ok_of_isSymbol_eq_true .comma .pattern commaPresent
              with ⟨comma, parsed⟩
          rw [parsed] at commaResult
          contradiction
      | ok comma afterComma =>
          simp only [commaResult] at result
          have commaParsed := symbol_success_exactTokenParses .comma
            .pattern commaResult
          by_cases closingPresent : isSymbol afterComma .rightParen
          · simp only [closingPresent, if_true] at result
            rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .pattern
                closingPresent with ⟨closing, closingResult⟩
            unfold closePatternTuple at result
            simp only [bind, closingResult] at result
            cases elementsRev with
            | nil => simp [pure] at result
            | cons head tail =>
                cases tail with
                | nil => simp [pure] at result
                | cons second rest => simp [pure] at result
          · have closingAbsentBool :
                isSymbol afterComma .rightParen = false :=
              Bool.eq_false_iff.mpr closingPresent
            simp only [closingAbsentBool, Bool.false_eq_true, if_false]
              at result
            have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false
              .rightParen closingAbsentBool
            cases elementResult : nested afterComma with
            | invariant error => simp [elementResult] at result
            | reject elementFailure elementRejected =>
                simp only [elementResult] at result
                cases result
                exact .elementRejected comma.span commaParsed closingAbsent
                  (nestedRejectSound elementResult)
            | ok element afterElement =>
                simp only [elementResult] at result
                by_cases noProgress :
                    afterElement.cursor ≤ afterComma.cursor
                · simp [noProgress] at result
                · simp only [noProgress, if_false] at result
                  have elementParsed := nestedSuccessSound elementResult
                  have progress : afterComma.declarativeRemainder.cursor <
                      afterElement.declarativeRemainder.cursor := by
                    simpa [State.declarativeRemainder] using
                      (Nat.lt_of_not_ge noProgress)
                  by_cases commaAgain : isSymbol afterElement .comma
                  · simp only [commaAgain, if_true] at result
                    exact .laterRejected comma.span commaParsed closingAbsent
                      elementParsed progress
                      (inductionHypothesis (element :: elementsRev)
                        afterElement failure rejected commaAgain result)
                  · have commaAbsentBool :
                        isSymbol afterElement .comma = false :=
                      Bool.eq_false_iff.mpr commaAgain
                    simp only [commaAbsentBool, Bool.false_eq_true, if_false]
                      at result
                    rcases closePatternTuple_reject_ordinary_sound opening
                        (element :: elementsRev) result with
                      ⟨rejectedEq, rightParenAbsent⟩
                    subst rejectedEq
                    exact .closingMissing comma.span commaParsed closingAbsent
                      elementParsed progress
                      (symbolAbsentAt_of_isSymbol_eq_false .comma
                        commaAbsentBool) rightParenAbsent

/-- Every public parenthesized-pattern rejection follows its exact branch. -/
theorem parenthesizedPattern_reject_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : parenthesizedPattern nested input = .reject failure rejected) :
    DeclarativeGrammar.ParenthesizedPatternRejects nestedOrdinary
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold parenthesizedPattern at result
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure afterOpening =>
      simp only [openingResult] at result
      have rejectedEq : afterOpening = rejected := by injection result
      subst rejected
      have stateEq := symbol_reject_state_eq .leftParen .pattern
        openingResult
      rw [stateEq]
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftParen .pattern openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingParsed := symbol_success_exactTokenParses .leftParen
        .pattern openingResult
      by_cases closingPresent : isSymbol afterOpening .rightParen
      · simp only [closingPresent, if_true] at result
        rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .pattern
            closingPresent with ⟨closing, closingResult⟩
        unfold closePatternTuple at result
        simp [bind, closingResult, pure] at result
      · have closingAbsentBool :
            isSymbol afterOpening .rightParen = false :=
          Bool.eq_false_iff.mpr closingPresent
        simp only [closingAbsentBool, Bool.false_eq_true, if_false] at result
        have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen
          closingAbsentBool
        cases firstResult : nested afterOpening with
        | invariant error => simp [firstResult] at result
        | reject firstFailure firstRejected =>
            simp only [firstResult] at result
            cases result
            exact .firstRejected opening.span openingParsed closingAbsent
              (nestedRejectSound firstResult)
        | ok first afterFirst =>
            simp only [firstResult] at result
            by_cases noProgress : afterFirst.cursor ≤ afterOpening.cursor
            · simp [noProgress] at result
            · simp only [noProgress, if_false] at result
              have firstParsed := nestedSuccessSound firstResult
              have progress : afterOpening.declarativeRemainder.cursor <
                  afterFirst.declarativeRemainder.cursor := by
                simpa [State.declarativeRemainder] using
                  (Nat.lt_of_not_ge noProgress)
              by_cases commaPresent : isSymbol afterFirst .comma
              · simp only [commaPresent, if_true] at result
                exact .tailRejected opening.span openingParsed closingAbsent
                  firstParsed progress
                  (patternTupleTail_reject_ordinary_sound nested
                    nestedOrdinary nestedRejects nestedSuccessSound
                      nestedRejectSound opening
                        (afterFirst.remainingCount + 1) [first] afterFirst
                          failure rejected commaPresent result)
              · have commaAbsentBool : isSymbol afterFirst .comma = false :=
                  Bool.eq_false_iff.mpr commaPresent
                simp only [commaAbsentBool, Bool.false_eq_true, if_false]
                  at result
                rcases closePatternTuple_reject_ordinary_sound opening [first]
                    result with ⟨rejectedEq, rightParenAbsent⟩
                subst rejectedEq
                exact .closingMissing opening.span openingParsed closingAbsent
                  firstParsed progress
                    (symbolAbsentAt_of_isSymbol_eq_false .comma
                      commaAbsentBool) rightParenAbsent

end Solcore.Syntax.Parser.PatternInternals
