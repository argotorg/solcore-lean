import Solcore.Syntax.Parser.BarePredicateSequenceOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.DeclarativePredicateSequenceExactnessProperties
import Solcore.Syntax.Parser.PredicateSequenceSoundnessProperties

/-! Exact executable rejection reflection for grouped-first predicate choice. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

private theorem openingPresent_of_isSymbol_eq_true {input : State}
    (present : isSymbol input .leftParen = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .leftParen } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeExpr present with
    ⟨opening, parsed⟩
  exact ⟨opening.span,
    (symbol_success_exactTokenParses .leftParen .typeExpr parsed).1⟩

/-- Every rejected predicate sequence retains exact grouped-first dispatch and
the final bare rejection remainder. -/
theorem predicateSequence_reject_sound
    {input rejected : State} {failure : Failure}
    (result : predicateSequence input = .reject failure rejected) :
    DeclarativeGrammar.PredicateSequenceRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold predicateSequence at result
  split at result
  · rename_i openingPresent
    unfold orElse at result
    cases groupedResult : groupedPredicates input with
    | ok grouped afterGrouped => simp [groupedResult] at result
    | invariant error => simp [groupedResult] at result
    | reject groupedFailure groupedRejected =>
        simp only [groupedResult] at result
        exact .fallback
          (openingPresent_of_isSymbol_eq_true openingPresent)
          (groupedPredicates_reject_sound groupedResult)
          (barePredicates_reject_sound result)
  · rename_i openingAbsent
    exact .direct
      (symbolAbsentAt_of_isSymbol_eq_false .leftParen
        (Bool.eq_false_iff.mpr openingAbsent))
      (barePredicates_reject_sound result)

/-- Package executable predicate-sequence success and exact rejection. -/
theorem predicateSequence_ordinaryOutcome_sound :
    (∀ {input next : State} {values : PredicateSequence},
      predicateSequence input = .ok values next →
        DeclarativeGrammar.PredicateSequenceParses
          input.declarativeRemainder values next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      predicateSequence input = .reject failure rejected →
        DeclarativeGrammar.PredicateSequenceRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨predicateSequence_success_sound, predicateSequence_reject_sound⟩

/-- Re-export exact prioritized predicate-sequence outcomes. -/
theorem predicateSequence_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.PredicateSequenceParses
      DeclarativeGrammar.PredicateSequenceRejects :=
  DeclarativeGrammar.predicateSequenceExactOutcomeSpec

/-- Two prioritized predicate-sequence successes have the same AST and
remainder. -/
theorem predicateSequence_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : PredicateSequence}
    (leftResult : predicateSequence input = .ok left leftOutput)
    (rightResult : predicateSequence input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.PredicateSequenceParses.result_unique
    (predicateSequence_success_sound leftResult)
    (predicateSequence_success_sound rightResult)

/-- Two prioritized predicate-sequence rejections have the same endpoint. -/
theorem predicateSequence_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : predicateSequence input = .reject leftFailure leftOutput)
    (rightResult : predicateSequence input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.PredicateSequenceRejects.output_unique
    (predicateSequence_reject_sound leftResult)
    (predicateSequence_reject_sound rightResult)

end Solcore.Syntax.Parser.PredicateInternals
