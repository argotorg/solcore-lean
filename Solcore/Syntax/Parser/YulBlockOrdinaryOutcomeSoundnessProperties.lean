import Solcore.Syntax.DeclarativeYulBlockOutcomeProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.YulBlockSoundnessProperties

/-!
Executable ordinary-success and exact-rejection bridges for braced Yul
blocks, parameterized by matching statement outcome callbacks.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful block-item loop follows the ordinary statement grammar,
retaining the forward suffix after its existing reverse accumulator. -/
theorem yulBlockItems_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (opening : Token) : ∀ fuel bodyRev input body output,
      yulBlockItems statement opening fuel bodyRev input = .ok body output →
      ∃ bodySpan suffix,
        body = {
          span := bodySpan
          body := bodyRev.reverse ++ suffix
        } ∧
        DeclarativeGrammar.YulBlockItemsParses statementOrdinary opening.span
          input.declarativeRemainder bodySpan suffix
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input body output result
      simp [yulBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input body output result
      unfold yulBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeYulBlock_success_sound opening bodyRev result with
            ⟨closingSpan, bodyEq, closeGrammar, closingParsed⟩
          exact ⟨SourceSpan.cover opening.span closingSpan, [],
            by simpa using bodyEq, .close closingSpan closingParsed⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .yulStatement input <;>
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
                      ⟨bodySpan, suffix, bodyEq, tailGrammar⟩
                    have notAtEnd :
                        input.cursor < input.window.endIndex := by
                      simpa [State.atEnd] using ended
                    refine ⟨bodySpan, value :: suffix, ?_,
                      .next notAtEnd
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        (statementSuccessSound statementResult) progress
                        tailGrammar⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction

/-- Every successful complete block follows the ordinary block grammar. -/
theorem yulBlock_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {body : YulParsedBlock}
    (result : yulBlock statement input = .ok body output) :
    DeclarativeGrammar.YulBlockOrdinaryParses statementOrdinary
      input.declarativeRemainder body.span body.body
        output.declarativeRemainder := by
  unfold yulBlock at result
  cases openingResult : symbol .leftBrace .yulStatement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases yulBlockItems_success_ordinary_sound statement
          statementOrdinary statementSuccessSound opening
          (afterOpening.remainingCount + 1) [] afterOpening body output result
        with ⟨bodySpan, suffix, bodyEq, itemsParsed⟩
      rw [bodyEq]
      exact .parsed opening.span
        (symbol_success_exactTokenParses .leftBrace .yulStatement
          openingResult) itemsParsed

/-- Every rejected block-item loop follows the exact ordinary-prefix
rejection trace. -/
theorem yulBlockItems_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (opening : Token) : ∀ fuel bodyRev input failure rejected,
      yulBlockItems statement opening fuel bodyRev input =
        .reject failure rejected →
      DeclarativeGrammar.YulBlockItemsRejects statementOrdinary
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input failure rejected result
      simp [yulBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input failure rejected result
      unfold yulBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .yulStatement
              closingPresent with ⟨closing, closingResult⟩
          unfold closeYulBlock at result
          simp [closingResult] at result
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .yulStatement input with
              | invariant error => simp [closingResult] at result
              | ok closing afterClosing => simp [closingResult] at result
              | reject closingFailure closingRejected =>
                  have rejectedEq := symbol_reject_state_eq .rightBrace
                    .yulStatement closingResult
                  subst closingRejected
                  simp only [closingResult] at result
                  cases result
                  exact .missingClose
                    (symbol_reject_tokenKindAbsentAt .rightBrace .yulStatement
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

/-- Every rejected complete block follows opening failure or the exact
ordinary-prefix block-item rejection trace. -/
theorem yulBlock_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulBlock statement input = .reject failure rejected) :
    DeclarativeGrammar.YulBlockRejects statementOrdinary statementRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulBlock at result
  cases openingResult : symbol .leftBrace .yulStatement input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have rejectedEq := symbol_reject_state_eq .leftBrace .yulStatement
        openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftBrace .yulStatement
          openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      exact .itemsRejected opening.span
        (symbol_success_exactTokenParses .leftBrace .yulStatement
          openingResult)
        (yulBlockItems_reject_ordinary_sound statement statementOrdinary
          statementRejects statementSuccessSound statementRejectSound opening
          (afterOpening.remainingCount + 1) [] afterOpening failure rejected
          result)

end Solcore.Syntax.Parser
