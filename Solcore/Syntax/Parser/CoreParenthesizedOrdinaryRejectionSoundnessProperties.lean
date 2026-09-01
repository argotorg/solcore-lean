import Solcore.Syntax.DeclarativeCoreParenthesizedOutcomeGrammar
import Solcore.Syntax.Parser.CoreParenthesizedOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Exact ordinary-rejection reflection for guarded Core parentheses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem closeTuple_reject_ordinary_sound (opening : Token)
    (elementsRev : List Expr) {input rejected : State} {failure : Failure}
    (result : closeTuple opening elementsRev input =
      .reject failure rejected) :
    rejected = input ∧
      DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.symbol .rightParen) := by
  unfold closeTuple at result
  cases closingResult : symbol .rightParen .expression input with
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
      exact ⟨symbol_reject_state_eq .rightParen .expression closingResult,
        symbol_reject_tokenKindAbsentAt .rightParen .expression
          closingResult⟩

/-- Every tuple-tail rejection under its positive comma guard follows exactly
the nested-element, missing-closing, or later-tail branch. -/
theorem tupleTail_reject_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (opening : Token) : ∀ fuel elementsRev input failure rejected,
      isSymbol input .comma = true →
      tupleTail nested opening fuel elementsRev input =
        .reject failure rejected →
      DeclarativeGrammar.ParenthesizedTupleTailRejects nestedOrdinary
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input failure rejected commaPresent result
      simp [tupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input failure rejected commaPresent result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject commaFailure commaRejected =>
          rcases symbol_eq_ok_of_isSymbol_eq_true .comma .expression
              commaPresent with ⟨comma, parsed⟩
          rw [parsed] at commaResult
          contradiction
      | ok comma afterComma =>
          simp only [commaResult] at result
          have commaParsed := symbol_success_exactTokenParses .comma
            .expression commaResult
          by_cases closingPresent : isSymbol afterComma .rightParen
          · simp only [closingPresent, if_true] at result
            rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .expression
                closingPresent with ⟨closing, closingResult⟩
            unfold closeTuple at result
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
                by_cases progressed : afterElement.cursor > afterComma.cursor
                · simp only [progressed, if_true] at result
                  have elementParsed := nestedSuccessSound elementResult
                  have progress : afterComma.declarativeRemainder.cursor <
                      afterElement.declarativeRemainder.cursor := by
                    simpa [State.declarativeRemainder] using progressed
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
                    rcases closeTuple_reject_ordinary_sound opening
                        (element :: elementsRev) result with
                      ⟨rejectedEq, rightParenAbsent⟩
                    subst rejectedEq
                    exact .closingMissing comma.span commaParsed closingAbsent
                      elementParsed progress
                      (symbolAbsentAt_of_isSymbol_eq_false .comma
                        commaAbsentBool) rightParenAbsent
                · simp [progressed] at result

/-- Under the dispatcher's positive `(` guard, every parenthesized rejection
is the exact first-element, closing, or tuple-tail rejection. -/
theorem parenthesized_reject_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (openingPresent : isSymbol input .leftParen = true)
    (result : parenthesized nested input = .reject failure rejected) :
    DeclarativeGrammar.ParenthesizedExpressionRejects nestedOrdinary
      nestedRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .expression
          openingPresent with ⟨opening, parsed⟩
      rw [parsed] at openingResult
      contradiction
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingParsed := symbol_success_exactTokenParses .leftParen
        .expression openingResult
      by_cases closingPresent : isSymbol afterOpening .rightParen
      · simp only [closingPresent, if_true] at result
        rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .expression
            closingPresent with ⟨closing, closingResult⟩
        unfold closeTuple at result
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
            by_cases progressed : afterFirst.cursor > afterOpening.cursor
            · have notLe : ¬ afterFirst.cursor ≤ afterOpening.cursor := by
                exact Nat.not_le_of_lt progressed
              simp only [notLe, if_false] at result
              have firstParsed := nestedSuccessSound firstResult
              have progress : afterOpening.declarativeRemainder.cursor <
                  afterFirst.declarativeRemainder.cursor := by
                simpa [State.declarativeRemainder] using progressed
              by_cases commaPresent : isSymbol afterFirst .comma
              · simp only [commaPresent, if_true] at result
                exact .tailRejected opening.span openingParsed closingAbsent
                  firstParsed progress
                  (tupleTail_reject_ordinary_sound nested nestedOrdinary
                    nestedRejects nestedSuccessSound nestedRejectSound opening
                      (afterFirst.remainingCount + 1) [first] afterFirst
                        failure rejected commaPresent result)
              · have commaAbsentBool : isSymbol afterFirst .comma = false :=
                  Bool.eq_false_iff.mpr commaPresent
                simp only [commaAbsentBool, Bool.false_eq_true, if_false]
                  at result
                rcases closeTuple_reject_ordinary_sound opening [first]
                    result with ⟨rejectedEq, rightParenAbsent⟩
                subst rejectedEq
                exact .closingMissing opening.span openingParsed closingAbsent
                  firstParsed progress
                    (symbolAbsentAt_of_isSymbol_eq_false .comma
                      commaAbsentBool) rightParenAbsent
            · have le : afterFirst.cursor ≤ afterOpening.cursor :=
                Nat.le_of_not_gt progressed
              simp [le] at result

end Solcore.Syntax.Parser.ExpressionAtomInternals
