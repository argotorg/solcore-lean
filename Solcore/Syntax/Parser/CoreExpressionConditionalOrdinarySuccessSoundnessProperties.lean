import Solcore.Syntax.DeclarativeCoreExpressionLayerOutcomeGrammar
import Solcore.Syntax.Parser.CoreExpressionConditionalSoundnessProperties

/-!
Unconditional ordinary-success bridges for the Core conditional expression
layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Every executable conditional-tail success decomposes into the outstanding
head fold and an exact right-associated ordinary conditional tail. -/
theorem conditionalTail_success_ordinary_sound_strong
    (nested alternative : Parser Expr)
    (nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output →
        nestedOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (alternativeSuccessSound :
      ∀ {input output : State} {expression : Expr},
        alternative input = .ok expression output →
          alternativeOrdinary input.declarativeRemainder expression
            output.declarativeRemainder) :
    ∀ fuel headsRev condition input expression output,
      conditionalTail nested alternative fuel headsRev condition input =
          .ok expression output →
        ∃ tailExpression,
          expression = headsRev.foldl foldConditionalHead tailExpression ∧
          DeclarativeGrammar.ConditionalTailParses nestedOrdinary
            alternativeOrdinary input.declarativeRemainder condition
              tailExpression output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro headsRev condition input expression output result
      simp [conditionalTail] at result
  | succ fuel inductionHypothesis =>
      intro headsRev condition input expression output result
      unfold conditionalTail at result
      split at result
      next questionPresent =>
        cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at result
        | reject failure rejected => simp [questionResult] at result
        | ok question afterQuestion =>
            simp only [questionResult] at result
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at result
            | reject failure rejected => simp [thenResult] at result
            | ok thenBranch afterThen =>
                simp only [thenResult] at result
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at result
                | reject failure rejected => simp [colonResult] at result
                | ok colon afterColon =>
                    simp only [colonResult] at result
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at result
                    | reject failure rejected =>
                        simp [alternativeResult] at result
                    | ok nextCondition afterAlternative =>
                        simp only [alternativeResult] at result
                        let head : ConditionalHead := {
                          condition
                          question := question.span
                          thenBranch
                          colon := colon.span
                        }
                        rcases inductionHypothesis (head :: headsRev)
                            nextCondition afterAlternative expression output
                              result with
                          ⟨tailExpression, expressionEq, tailParsed⟩
                        have parsed :=
                          DeclarativeGrammar.ConditionalTailParses.next
                            (condition := condition)
                            question.span colon.span
                            (symbol_success_exactTokenParses .question
                              .expression questionResult)
                            (nestedSuccessSound thenResult)
                            (symbol_success_exactTokenParses .colon
                              .expression colonResult)
                            (alternativeSuccessSound alternativeResult)
                            tailParsed
                        refine ⟨foldConditionalHead tailExpression head,
                          ?_, ?_⟩
                        · simpa [head] using expressionEq
                        · simpa [head, foldConditionalHead] using parsed
      next questionAbsent =>
        cases result
        refine ⟨condition, rfl, .done ?_⟩
        exact symbolAbsentAt_of_isSymbol_eq_false .question
          (Bool.eq_false_iff.mpr questionAbsent)

/-- Every complete executable conditional success follows the exact ordinary
right-associated conditional grammar, independently of diagnostics. -/
theorem conditional_success_ordinary_sound
    (nested alternative : Parser Expr)
    (nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output →
        nestedOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (alternativeSuccessSound :
      ∀ {input output : State} {expression : Expr},
        alternative input = .ok expression output →
          alternativeOrdinary input.declarativeRemainder expression
            output.declarativeRemainder)
    {input output : State} {expression : Expr}
    (result : conditional nested alternative input = .ok expression output) :
    DeclarativeGrammar.ConditionalOrdinaryParses nestedOrdinary
      alternativeOrdinary input.declarativeRemainder expression
        output.declarativeRemainder := by
  unfold conditional at result
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at result
  | reject failure rejected => simp [alternativeResult] at result
  | ok condition afterCondition =>
      simp only [alternativeResult] at result
      rcases conditionalTail_success_ordinary_sound_strong nested alternative
          nestedOrdinary alternativeOrdinary nestedSuccessSound
            alternativeSuccessSound (afterCondition.remainingCount + 1) []
              condition afterCondition expression output result with
        ⟨tailExpression, expressionEq, tailParsed⟩
      simp only [List.foldl_nil] at expressionEq
      subst expression
      exact ⟨condition, afterCondition.declarativeRemainder,
        alternativeSuccessSound alternativeResult, tailParsed⟩

end Solcore.Syntax.Parser.ExpressionInternals
