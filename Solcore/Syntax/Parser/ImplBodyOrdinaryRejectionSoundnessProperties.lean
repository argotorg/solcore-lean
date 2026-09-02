import Solcore.Syntax.DeclarativeImplBodyOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.ImplMethodOrdinaryOutcomeSoundnessProperties

/-! Exact broad ordinary rejection for the custom implementation-body loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

private theorem functionPresent_of_isKeyword_eq_true {input : State}
    (present : isKeyword input .functionKw = true) :
    DeclarativeGrammar.ImplMethodStartAt input.declarativeRemainder := by
  rcases keyword_eq_ok_of_isKeyword_eq_true .functionKw .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses .functionKw .topItem result).1⟩

private theorem implMethods_reject_ordinaryOutcome_sound
    (opening : Token) :
    ∀ fuel methodsRev input failure rejected,
      implMethods opening fuel methodsRev input = .reject failure rejected →
      DeclarativeGrammar.ImplMethodTailRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input failure rejected result
      simp [implMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input failure rejected result
      unfold implMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .topItem
              closingPresent with ⟨closing, closingResult⟩
          unfold closeImplBody at result
          simp [bind, closingResult, pure] at result
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases functionPresent : isKeyword input .functionKw with
          | false =>
              simp only [functionPresent, Bool.false_eq_true, if_false]
                at result
              unfold rejectAt at result
              cases result
              exact .unexpected
                (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                  closingPresent)
                (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                  functionPresent)
          | true =>
              simp only [functionPresent, if_true] at result
              cases methodResult : implMethod input with
              | invariant error => simp [methodResult] at result
              | reject methodFailure methodRejected =>
                  simp only [methodResult] at result
                  cases result
                  exact .methodRejected
                    (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                      closingPresent)
                    (functionPresent_of_isKeyword_eq_true functionPresent)
                    (implMethod_reject_ordinaryOutcome_sound methodResult)
              | ok method afterMethod =>
                  simp only [methodResult] at result
                  by_cases progress : afterMethod.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    exact .laterRejected
                      (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                        closingPresent)
                      (functionPresent_of_isKeyword_eq_true functionPresent)
                      (implMethod_success_ordinaryOutcome_sound methodResult)
                      progress
                      (inductionHypothesis (method :: methodsRev) afterMethod
                        failure rejected result)
                  · simp [progress] at result

/-- Every executable implementation-body rejection records opening failure or
the exact first rejection of its prioritized broad method tail. -/
theorem implBody_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : implBody input = .reject failure rejected) :
    DeclarativeGrammar.ImplBodyRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold implBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have rejectedEq := symbol_reject_state_eq .leftBrace .topItem
        openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftBrace .topItem openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      exact .tailRejected opening.span
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        (implMethods_reject_ordinaryOutcome_sound opening
          (afterOpening.remainingCount + 1) [] afterOpening failure rejected
            result)

end Solcore.Syntax.Parser.ImplInternals
