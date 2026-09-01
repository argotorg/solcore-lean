import Solcore.Syntax.DeclarativeCoreBlockOutcomeProperties
import Solcore.Syntax.Parser.Block

/-!
Diagnostic-inclusive executable success soundness for raw Core blocks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful block-item loop retains its existing reverse accumulator
and exposes the remaining statements in source order. -/
theorem coreBlockItems_success_ordinary_sound
    (statement : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input body output,
      coreBlockItems statement opening policy fuel bodyRev input =
          .ok body output →
      ∃ closingSpan suffix,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          value := bodyRev.reverse ++ suffix
        } ∧
        DeclarativeGrammar.CoreBlockItemsParses statementOrdinary
          input.declarativeRemainder suffix closingSpan
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input body output result
      simp [coreBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input body output result
      unfold coreBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeCoreBlock_success_ordinary_sound opening policy bodyRev
              result with ⟨closingSpan, bodyEq, closingParsed⟩
          exact ⟨closingSpan, [], by simpa using bodyEq,
            .close closingSpan closingParsed⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .statement input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok value afterStatement =>
                  simp only [statementResult] at result
                  by_cases progress : afterStatement.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (value :: bodyRev)
                        afterStatement body output result with
                      ⟨closingSpan, suffix, bodyEq, tailParsed⟩
                    have notAtEnd :
                        input.cursor < input.window.endIndex := by
                      simpa [State.atEnd] using ended
                    refine ⟨closingSpan, value :: suffix, ?_,
                      .next notAtEnd
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        (statementSuccessSound statementResult) progress
                        tailParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction

/-- Every successful raw Core block follows the diagnostic-inclusive ordinary
grammar for its exact tail policy. -/
theorem coreBlock_success_ordinary_sound
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {body : Block}
    (result : coreBlock statement policy input = .ok body output) :
    DeclarativeGrammar.CoreBlockOrdinaryParses statementOrdinary
      policy.declarative input.declarativeRemainder body
        output.declarativeRemainder := by
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases coreBlockItems_success_ordinary_sound statement
          statementOrdinary statementSuccessSound opening policy
          (afterOpening.remainingCount + 1) [] afterOpening body output result
        with ⟨closingSpan, suffix, bodyEq, bodyParsed⟩
      rw [bodyEq]
      exact .parsed opening.span closingSpan
        (symbol_success_exactTokenParses .leftBrace .statement openingResult)
        bodyParsed

end Solcore.Syntax.Parser
