import Solcore.Syntax.DeclarativeCoreExpressionLayerOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Expression

/-!
Exact executable rejection bridges for the generic Core conditional layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Every executable conditional-tail rejection records the exact selected
suffix stage and all preceding ordinary subordinate outcomes. -/
theorem conditionalTail_reject_ordinary_sound
    (nested alternative : Parser Expr)
    (nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedRejects alternativeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (alternativeSuccessSound :
      ∀ {input output : State} {expression : Expr},
        alternative input = .ok expression output → alternativeOrdinary
          input.declarativeRemainder expression output.declarativeRemainder)
    (alternativeRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        alternative input = .reject failure rejected → alternativeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :
    ∀ fuel headsRev condition input failure rejected,
      conditionalTail nested alternative fuel headsRev condition input =
          .reject failure rejected →
        DeclarativeGrammar.ConditionalTailRejects nestedOrdinary
          alternativeOrdinary nestedRejects alternativeRejects
            input.declarativeRemainder condition
              rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro headsRev condition input failure rejected result
      simp [conditionalTail] at result
  | succ fuel inductionHypothesis =>
      intro headsRev condition input failure rejected result
      unfold conditionalTail at result
      split at result
      next questionPresent =>
        cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at result
        | reject questionFailure questionRejected =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .question .expression
                questionPresent with ⟨question, parsed⟩
            rw [parsed] at questionResult
            contradiction
        | ok question afterQuestion =>
            simp only [questionResult] at result
            have questionParsed := symbol_success_exactTokenParses .question
              .expression questionResult
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at result
            | reject thenFailure thenRejected =>
                simp only [thenResult] at result
                cases result
                exact .thenRejected question.span questionParsed
                  (nestedRejectSound thenResult)
            | ok thenBranch afterThen =>
                simp only [thenResult] at result
                have thenParsed := nestedSuccessSound thenResult
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at result
                | reject colonFailure colonRejected =>
                    have rejectedEq := symbol_reject_state_eq .colon .expression
                      colonResult
                    subst rejectedEq
                    simp only [colonResult] at result
                    cases result
                    exact .colonMissing question.span questionParsed thenParsed
                      (symbol_reject_tokenKindAbsentAt .colon .expression
                        colonResult)
                | ok colon afterColon =>
                    simp only [colonResult] at result
                    have colonParsed := symbol_success_exactTokenParses .colon
                      .expression colonResult
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at result
                    | reject alternativeFailure alternativeRejected =>
                        simp only [alternativeResult] at result
                        cases result
                        exact .alternativeRejected question.span colon.span
                          questionParsed thenParsed colonParsed
                          (alternativeRejectSound alternativeResult)
                    | ok nextCondition afterAlternative =>
                        simp only [alternativeResult] at result
                        exact .laterRejected question.span colon.span
                          questionParsed thenParsed colonParsed
                          (alternativeSuccessSound alternativeResult)
                          (inductionHypothesis ({
                            condition
                            question := question.span
                            thenBranch
                            colon := colon.span
                          } :: headsRev) nextCondition afterAlternative failure
                            rejected result)
      next questionAbsent =>
        cases result

/-- Every executable complete conditional rejection is either its initial
alternative rejection or an exact rejection in the maximal conditional tail. -/
theorem conditional_reject_ordinary_sound
    (nested alternative : Parser Expr)
    (nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedRejects alternativeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (alternativeSuccessSound :
      ∀ {input output : State} {expression : Expr},
        alternative input = .ok expression output → alternativeOrdinary
          input.declarativeRemainder expression output.declarativeRemainder)
    (alternativeRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        alternative input = .reject failure rejected → alternativeRejects
          input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : conditional nested alternative input = .reject failure rejected) :
    DeclarativeGrammar.ConditionalRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold conditional at result
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at result
  | reject alternativeFailure alternativeRejected =>
      simp only [alternativeResult] at result
      cases result
      exact .conditionRejected (alternativeRejectSound alternativeResult)
  | ok condition afterCondition =>
      simp only [alternativeResult] at result
      exact .tailRejected (alternativeSuccessSound alternativeResult)
        (conditionalTail_reject_ordinary_sound nested alternative nestedOrdinary
          alternativeOrdinary nestedRejects alternativeRejects
            nestedSuccessSound nestedRejectSound alternativeSuccessSound
              alternativeRejectSound (afterCondition.remainingCount + 1) []
                condition afterCondition failure rejected result)

end Solcore.Syntax.Parser.ExpressionInternals
