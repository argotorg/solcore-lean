import Solcore.Syntax.Parser.CoreBlockOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-!
Exact executable ordinary-rejection soundness for raw Core blocks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every rejected block-item loop records right-brace priority, the forced
closing failure at window end, or the exact rejected statement prefix. -/
theorem coreBlockItems_reject_ordinary_sound
    (statement : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input failure rejected,
      coreBlockItems statement opening policy fuel bodyRev input =
          .reject failure rejected →
      DeclarativeGrammar.CoreBlockItemsRejects statementOrdinary
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input failure rejected result
      simp [coreBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input failure rejected result
      unfold coreBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .statement
              closingPresent with ⟨closing, closingResult⟩
          unfold closeCoreBlock at result
          simp only [bind, closingResult, modifyState, pure] at result
          contradiction
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .statement input with
              | invariant error => simp [closingResult] at result
              | ok closing afterClosing => simp [closingResult] at result
              | reject closingFailure closingRejected =>
                  have rejectedEq := symbol_reject_state_eq .rightBrace
                    .statement closingResult
                  subst closingRejected
                  simp only [closingResult] at result
                  cases result
                  exact .missingClose
                    (symbol_reject_tokenKindAbsentAt .rightBrace .statement
                      closingResult)
                    (by simpa [State.atEnd, State.declarativeRemainder]
                      using ended)
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              have notAtEnd : input.cursor < input.window.endIndex := by
                simpa [State.atEnd] using ended
              have closingAbsent :=
                symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingPresent
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject statementFailure statementRejected =>
                  simp only [statementResult] at result
                  cases result
                  exact .statementRejected notAtEnd closingAbsent
                    (statementRejectSound statementResult)
              | ok value afterStatement =>
                  simp only [statementResult] at result
                  by_cases progress : afterStatement.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    exact .laterRejected notAtEnd closingAbsent
                      (statementSuccessSound statementResult) progress
                      (inductionHypothesis (value :: bodyRev) afterStatement
                        failure rejected result)
                  · simp only [progress, if_false] at result
                    contradiction

/-- Every rejected raw Core block follows opening failure or the exact
ordinary-prefix item rejection for its tail policy. -/
theorem coreBlock_reject_ordinary_sound
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : coreBlock statement policy input = .reject failure rejected) :
    DeclarativeGrammar.CoreBlockRejects statementOrdinary statementRejects
      policy.declarative input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have rejectedEq := symbol_reject_state_eq .leftBrace .statement
        openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftBrace .statement openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      exact .itemsRejected opening.span
        (symbol_success_exactTokenParses .leftBrace .statement openingResult)
        (coreBlockItems_reject_ordinary_sound statement statementOrdinary
          statementRejects statementSuccessSound statementRejectSound opening
          policy (afterOpening.remainingCount + 1) [] afterOpening failure
          rejected result)

end Solcore.Syntax.Parser
